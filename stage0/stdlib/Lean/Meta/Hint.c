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
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl(uint8_t v_x_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_box(v_x_217_);
v___x_219_ = lean_obj_tag_nat(v___x_218_);
lean_dec(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl___boxed(lean_object* v_x_220_){
_start:
{
uint8_t v_x_4__boxed_221_; lean_object* v_res_222_; 
v_x_4__boxed_221_ = lean_unbox(v_x_220_);
v_res_222_ = l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl(v_x_4__boxed_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(lean_object* v_k_223_){
_start:
{
lean_inc(v_k_223_);
return v_k_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg___boxed(lean_object* v_k_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(v_k_224_);
lean_dec(v_k_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim(lean_object* v_motive_226_, lean_object* v_ctorIdx_227_, uint8_t v_t_228_, lean_object* v_h_229_, lean_object* v_k_230_){
_start:
{
lean_inc(v_k_230_);
return v_k_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___boxed(lean_object* v_motive_231_, lean_object* v_ctorIdx_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_k_235_){
_start:
{
uint8_t v_t_boxed_236_; lean_object* v_res_237_; 
v_t_boxed_236_ = lean_unbox(v_t_233_);
v_res_237_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim(v_motive_231_, v_ctorIdx_232_, v_t_boxed_236_, v_h_234_, v_k_235_);
lean_dec(v_k_235_);
lean_dec(v_ctorIdx_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(lean_object* v_auto_238_){
_start:
{
lean_inc(v_auto_238_);
return v_auto_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg___boxed(lean_object* v_auto_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(v_auto_239_);
lean_dec(v_auto_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim(lean_object* v_motive_241_, uint8_t v_t_242_, lean_object* v_h_243_, lean_object* v_auto_244_){
_start:
{
lean_inc(v_auto_244_);
return v_auto_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___boxed(lean_object* v_motive_245_, lean_object* v_t_246_, lean_object* v_h_247_, lean_object* v_auto_248_){
_start:
{
uint8_t v_t_boxed_249_; lean_object* v_res_250_; 
v_t_boxed_249_ = lean_unbox(v_t_246_);
v_res_250_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim(v_motive_245_, v_t_boxed_249_, v_h_247_, v_auto_248_);
lean_dec(v_auto_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(lean_object* v_char_251_){
_start:
{
lean_inc(v_char_251_);
return v_char_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg___boxed(lean_object* v_char_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(v_char_252_);
lean_dec(v_char_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim(lean_object* v_motive_254_, uint8_t v_t_255_, lean_object* v_h_256_, lean_object* v_char_257_){
_start:
{
lean_inc(v_char_257_);
return v_char_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___boxed(lean_object* v_motive_258_, lean_object* v_t_259_, lean_object* v_h_260_, lean_object* v_char_261_){
_start:
{
uint8_t v_t_boxed_262_; lean_object* v_res_263_; 
v_t_boxed_262_ = lean_unbox(v_t_259_);
v_res_263_ = l_Lean_Meta_Hint_DiffGranularity_char_elim(v_motive_258_, v_t_boxed_262_, v_h_260_, v_char_261_);
lean_dec(v_char_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(lean_object* v_word_264_){
_start:
{
lean_inc(v_word_264_);
return v_word_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg___boxed(lean_object* v_word_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(v_word_265_);
lean_dec(v_word_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim(lean_object* v_motive_267_, uint8_t v_t_268_, lean_object* v_h_269_, lean_object* v_word_270_){
_start:
{
lean_inc(v_word_270_);
return v_word_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___boxed(lean_object* v_motive_271_, lean_object* v_t_272_, lean_object* v_h_273_, lean_object* v_word_274_){
_start:
{
uint8_t v_t_boxed_275_; lean_object* v_res_276_; 
v_t_boxed_275_ = lean_unbox(v_t_272_);
v_res_276_ = l_Lean_Meta_Hint_DiffGranularity_word_elim(v_motive_271_, v_t_boxed_275_, v_h_273_, v_word_274_);
lean_dec(v_word_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(lean_object* v_all_277_){
_start:
{
lean_inc(v_all_277_);
return v_all_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg___boxed(lean_object* v_all_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(v_all_278_);
lean_dec(v_all_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim(lean_object* v_motive_280_, uint8_t v_t_281_, lean_object* v_h_282_, lean_object* v_all_283_){
_start:
{
lean_inc(v_all_283_);
return v_all_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___boxed(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_all_287_){
_start:
{
uint8_t v_t_boxed_288_; lean_object* v_res_289_; 
v_t_boxed_288_ = lean_unbox(v_t_285_);
v_res_289_ = l_Lean_Meta_Hint_DiffGranularity_all_elim(v_motive_284_, v_t_boxed_288_, v_h_286_, v_all_287_);
lean_dec(v_all_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(lean_object* v_none_290_){
_start:
{
lean_inc(v_none_290_);
return v_none_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg___boxed(lean_object* v_none_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(v_none_291_);
lean_dec(v_none_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim(lean_object* v_motive_293_, uint8_t v_t_294_, lean_object* v_h_295_, lean_object* v_none_296_){
_start:
{
lean_inc(v_none_296_);
return v_none_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___boxed(lean_object* v_motive_297_, lean_object* v_t_298_, lean_object* v_h_299_, lean_object* v_none_300_){
_start:
{
uint8_t v_t_boxed_301_; lean_object* v_res_302_; 
v_t_boxed_301_ = lean_unbox(v_t_298_);
v_res_302_ = l_Lean_Meta_Hint_DiffGranularity_none_elim(v_motive_297_, v_t_boxed_301_, v_h_299_, v_none_300_);
lean_dec(v_none_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___lam__0(lean_object* v_t_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; lean_object* v___x_307_; 
v___x_304_ = lean_box(0);
v___x_305_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_305_, 0, v_t_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
lean_ctor_set(v___x_305_, 2, v___x_304_);
lean_ctor_set(v___x_305_, 3, v___x_304_);
lean_ctor_set(v___x_305_, 4, v___x_304_);
lean_ctor_set(v___x_305_, 5, v___x_304_);
v___x_306_ = 0;
v___x_307_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___x_304_);
lean_ctor_set(v___x_307_, 2, v___x_304_);
lean_ctor_set_uint8(v___x_307_, sizeof(void*)*3, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instToMessageDataSuggestion___lam__0(lean_object* v_s_310_){
_start:
{
lean_object* v_toTryThisSuggestion_311_; lean_object* v_messageData_x3f_312_; 
v_toTryThisSuggestion_311_ = lean_ctor_get(v_s_310_, 0);
lean_inc_ref(v_toTryThisSuggestion_311_);
lean_dec_ref(v_s_310_);
v_messageData_x3f_312_ = lean_ctor_get(v_toTryThisSuggestion_311_, 4);
if (lean_obj_tag(v_messageData_x3f_312_) == 0)
{
lean_object* v_suggestion_313_; 
v_suggestion_313_ = lean_ctor_get(v_toTryThisSuggestion_311_, 0);
lean_inc_ref(v_suggestion_313_);
lean_dec_ref(v_toTryThisSuggestion_311_);
if (lean_obj_tag(v_suggestion_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_315_; 
v_a_314_ = lean_ctor_get(v_suggestion_313_, 1);
lean_inc(v_a_314_);
lean_dec_ref_known(v_suggestion_313_, 2);
v___x_315_ = l_Lean_MessageData_ofSyntax(v_a_314_);
return v___x_315_;
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_a_316_ = lean_ctor_get(v_suggestion_313_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v_suggestion_313_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v_suggestion_313_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v_suggestion_313_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 3);
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_323_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_MessageData_ofFormat(v___x_321_);
return v___x_322_;
}
}
}
}
else
{
lean_object* v_val_325_; 
lean_inc_ref(v_messageData_x3f_312_);
lean_dec_ref(v_toTryThisSuggestion_311_);
v_val_325_ = lean_ctor_get(v_messageData_x3f_312_, 0);
lean_inc(v_val_325_);
lean_dec_ref_known(v_messageData_x3f_312_, 1);
return v_val_325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(lean_object* v_as_328_, size_t v_i_329_, size_t v_stop_330_, lean_object* v_b_331_){
_start:
{
lean_object* v___y_333_; uint8_t v___x_337_; 
v___x_337_ = lean_usize_dec_eq(v_i_329_, v_stop_330_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v_fst_339_; lean_object* v_snd_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_377_; 
v___x_338_ = lean_array_uget(v_as_328_, v_i_329_);
v_fst_339_ = lean_ctor_get(v___x_338_, 0);
v_snd_340_ = lean_ctor_get(v___x_338_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_377_ == 0)
{
v___x_342_ = v___x_338_;
v_isShared_343_ = v_isSharedCheck_377_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_snd_340_);
lean_inc(v_fst_339_);
lean_dec(v___x_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_377_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = lean_array_get_size(v_b_331_);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_nat_dec_eq(v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v_fst_350_; lean_object* v_snd_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_369_; 
lean_del_object(v___x_342_);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_sub(v___x_344_, v___x_347_);
v___x_349_ = lean_array_fget(v_b_331_, v___x_348_);
v_fst_350_ = lean_ctor_get(v___x_349_, 0);
v_snd_351_ = lean_ctor_get(v___x_349_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_369_ == 0)
{
v___x_353_ = v___x_349_;
v_isShared_354_ = v_isSharedCheck_369_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_snd_351_);
lean_inc(v_fst_350_);
lean_dec(v___x_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_369_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
uint8_t v___x_355_; uint8_t v___x_356_; uint8_t v___x_357_; 
v___x_355_ = lean_unbox(v_fst_339_);
v___x_356_ = lean_unbox(v_fst_350_);
lean_dec(v_fst_350_);
v___x_357_ = l_Lean_Diff_instBEqAction_beq(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
lean_dec(v_snd_351_);
lean_dec(v___x_348_);
v___x_358_ = lean_mk_empty_array_with_capacity(v___x_347_);
v___x_359_ = lean_array_push(v___x_358_, v_snd_340_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_359_);
lean_ctor_set(v___x_353_, 0, v_fst_339_);
v___x_361_ = v___x_353_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_fst_339_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v___x_359_);
v___x_361_ = v_reuseFailAlloc_363_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; 
v___x_362_ = lean_array_push(v_b_331_, v___x_361_);
v___y_333_ = v___x_362_;
goto v___jp_332_;
}
}
else
{
lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_364_ = lean_array_push(v_snd_351_, v_snd_340_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_364_);
lean_ctor_set(v___x_353_, 0, v_fst_339_);
v___x_366_ = v___x_353_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_fst_339_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_368_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; 
v___x_367_ = lean_array_fset(v_b_331_, v___x_348_, v___x_366_);
lean_dec(v___x_348_);
v___y_333_ = v___x_367_;
goto v___jp_332_;
}
}
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
lean_dec_ref(v_b_331_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_mk_empty_array_with_capacity(v___x_370_);
lean_inc_ref(v___x_371_);
v___x_372_ = lean_array_push(v___x_371_, v_snd_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v___x_372_);
v___x_374_ = v___x_342_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_fst_339_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_376_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; 
v___x_375_ = lean_array_push(v___x_371_, v___x_374_);
v___y_333_ = v___x_375_;
goto v___jp_332_;
}
}
}
}
else
{
return v_b_331_;
}
v___jp_332_:
{
size_t v___x_334_; size_t v___x_335_; 
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_add(v_i_329_, v___x_334_);
v_i_329_ = v___x_335_;
v_b_331_ = v___y_333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg___boxed(lean_object* v_as_378_, lean_object* v_i_379_, lean_object* v_stop_380_, lean_object* v_b_381_){
_start:
{
size_t v_i_boxed_382_; size_t v_stop_boxed_383_; lean_object* v_res_384_; 
v_i_boxed_382_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_stop_boxed_383_ = lean_unbox_usize(v_stop_380_);
lean_dec(v_stop_380_);
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_378_, v_i_boxed_382_, v_stop_boxed_383_, v_b_381_);
lean_dec_ref(v_as_378_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(lean_object* v_ds_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0));
v___x_390_ = lean_array_get_size(v_ds_387_);
v___x_391_ = lean_nat_dec_lt(v___x_388_, v___x_390_);
if (v___x_391_ == 0)
{
return v___x_389_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = lean_nat_dec_le(v___x_390_, v___x_390_);
if (v___x_392_ == 0)
{
if (v___x_391_ == 0)
{
return v___x_389_;
}
else
{
size_t v___x_393_; size_t v___x_394_; lean_object* v___x_395_; 
v___x_393_ = ((size_t)0ULL);
v___x_394_ = lean_usize_of_nat(v___x_390_);
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_ds_387_, v___x_393_, v___x_394_, v___x_389_);
return v___x_395_;
}
}
else
{
size_t v___x_396_; size_t v___x_397_; lean_object* v___x_398_; 
v___x_396_ = ((size_t)0ULL);
v___x_397_ = lean_usize_of_nat(v___x_390_);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_ds_387_, v___x_396_, v___x_397_, v___x_389_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___boxed(lean_object* v_ds_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_399_);
lean_dec_ref(v_ds_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(lean_object* v_00_u03b1_401_, lean_object* v_ds_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___boxed(lean_object* v_00_u03b1_404_, lean_object* v_ds_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(v_00_u03b1_404_, v_ds_405_);
lean_dec_ref(v_ds_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(lean_object* v_00_u03b1_407_, lean_object* v_as_408_, size_t v_i_409_, size_t v_stop_410_, lean_object* v_b_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_408_, v_i_409_, v_stop_410_, v_b_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___boxed(lean_object* v_00_u03b1_413_, lean_object* v_as_414_, lean_object* v_i_415_, lean_object* v_stop_416_, lean_object* v_b_417_){
_start:
{
size_t v_i_boxed_418_; size_t v_stop_boxed_419_; lean_object* v_res_420_; 
v_i_boxed_418_ = lean_unbox_usize(v_i_415_);
lean_dec(v_i_415_);
v_stop_boxed_419_ = lean_unbox_usize(v_stop_416_);
lean_dec(v_stop_416_);
v_res_420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(v_00_u03b1_413_, v_as_414_, v_i_boxed_418_, v_stop_boxed_419_, v_b_417_);
lean_dec_ref(v_as_414_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(size_t v_sz_421_, size_t v_i_422_, lean_object* v_bs_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_usize_dec_lt(v_i_422_, v_sz_421_);
if (v___x_424_ == 0)
{
return v_bs_423_;
}
else
{
lean_object* v_v_425_; lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_442_; 
v_v_425_ = lean_array_uget(v_bs_423_, v_i_422_);
v_fst_426_ = lean_ctor_get(v_v_425_, 0);
v_snd_427_ = lean_ctor_get(v_v_425_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_v_425_);
if (v_isSharedCheck_442_ == 0)
{
v___x_429_ = v_v_425_;
v_isShared_430_ = v_isSharedCheck_442_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_427_);
lean_inc(v_fst_426_);
lean_dec(v_v_425_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_442_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v_bs_x27_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_431_ = lean_unsigned_to_nat(0u);
v_bs_x27_432_ = lean_array_uset(v_bs_423_, v_i_422_, v___x_431_);
v___x_433_ = lean_array_to_list(v_snd_427_);
v___x_434_ = lean_string_mk(v___x_433_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_434_);
v___x_436_ = v___x_429_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_fst_426_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_434_);
v___x_436_ = v_reuseFailAlloc_441_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
size_t v___x_437_; size_t v___x_438_; lean_object* v___x_439_; 
v___x_437_ = ((size_t)1ULL);
v___x_438_ = lean_usize_add(v_i_422_, v___x_437_);
v___x_439_ = lean_array_uset(v_bs_x27_432_, v_i_422_, v___x_436_);
v_i_422_ = v___x_438_;
v_bs_423_ = v___x_439_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0___boxed(lean_object* v_sz_443_, lean_object* v_i_444_, lean_object* v_bs_445_){
_start:
{
size_t v_sz_boxed_446_; size_t v_i_boxed_447_; lean_object* v_res_448_; 
v_sz_boxed_446_ = lean_unbox_usize(v_sz_443_);
lean_dec(v_sz_443_);
v_i_boxed_447_ = lean_unbox_usize(v_i_444_);
lean_dec(v_i_444_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_boxed_446_, v_i_boxed_447_, v_bs_445_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(lean_object* v_d_449_){
_start:
{
lean_object* v___x_450_; size_t v_sz_451_; size_t v___x_452_; lean_object* v___x_453_; 
v___x_450_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_d_449_);
v_sz_451_ = lean_array_size(v___x_450_);
v___x_452_ = ((size_t)0ULL);
v___x_453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_451_, v___x_452_, v___x_450_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff___boxed(lean_object* v_d_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v_d_454_);
lean_dec_ref(v_d_454_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(size_t v_sz_456_, size_t v_i_457_, lean_object* v_bs_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_usize_dec_lt(v_i_457_, v_sz_456_);
if (v___x_459_ == 0)
{
return v_bs_458_;
}
else
{
lean_object* v_v_460_; lean_object* v___x_461_; lean_object* v_bs_x27_462_; uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v_v_460_ = lean_array_uget(v_bs_458_, v_i_457_);
v___x_461_ = lean_unsigned_to_nat(0u);
v_bs_x27_462_ = lean_array_uset(v_bs_458_, v_i_457_, v___x_461_);
v___x_463_ = 0;
v___x_464_ = lean_box(v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v_v_460_);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_add(v_i_457_, v___x_466_);
v___x_468_ = lean_array_uset(v_bs_x27_462_, v_i_457_, v___x_465_);
v_i_457_ = v___x_467_;
v_bs_458_ = v___x_468_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9___boxed(lean_object* v_sz_470_, lean_object* v_i_471_, lean_object* v_bs_472_){
_start:
{
size_t v_sz_boxed_473_; size_t v_i_boxed_474_; lean_object* v_res_475_; 
v_sz_boxed_473_ = lean_unbox_usize(v_sz_470_);
lean_dec(v_sz_470_);
v_i_boxed_474_ = lean_unbox_usize(v_i_471_);
lean_dec(v_i_471_);
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_boxed_473_, v_i_boxed_474_, v_bs_472_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(lean_object* v___x_476_, lean_object* v_original_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_fst_479_; lean_object* v_snd_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_499_; 
v_fst_479_ = lean_ctor_get(v_a_478_, 0);
v_snd_480_ = lean_ctor_get(v_a_478_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_a_478_);
if (v_isSharedCheck_499_ == 0)
{
v___x_482_ = v_a_478_;
v_isShared_483_ = v_isSharedCheck_499_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_snd_480_);
lean_inc(v_fst_479_);
lean_dec(v_a_478_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_499_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
uint8_t v___x_484_; 
v___x_484_ = lean_nat_dec_lt(v_snd_480_, v___x_476_);
if (v___x_484_ == 0)
{
lean_object* v___x_486_; 
if (v_isShared_483_ == 0)
{
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_fst_479_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_snd_480_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
else
{
uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_488_ = 1;
v___x_489_ = lean_array_fget_borrowed(v_original_477_, v_snd_480_);
v___x_490_ = lean_box(v___x_488_);
lean_inc(v___x_489_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v___x_489_);
lean_ctor_set(v___x_482_, 0, v___x_490_);
v___x_492_ = v___x_482_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_489_);
v___x_492_ = v_reuseFailAlloc_498_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = lean_array_push(v_fst_479_, v___x_492_);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_add(v_snd_480_, v___x_494_);
lean_dec(v_snd_480_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_493_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v_a_478_ = v___x_496_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_500_, lean_object* v_original_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_500_, v_original_501_, v_a_502_);
lean_dec_ref(v_original_501_);
lean_dec(v___x_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(uint32_t v_a_504_, lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v___x_506_; 
v___x_506_ = lean_box(0);
return v___x_506_;
}
else
{
lean_object* v_key_507_; lean_object* v_value_508_; lean_object* v_tail_509_; uint32_t v___x_510_; uint8_t v___x_511_; 
v_key_507_ = lean_ctor_get(v_x_505_, 0);
v_value_508_ = lean_ctor_get(v_x_505_, 1);
v_tail_509_ = lean_ctor_get(v_x_505_, 2);
v___x_510_ = lean_unbox_uint32(v_key_507_);
v___x_511_ = lean_uint32_dec_eq(v___x_510_, v_a_504_);
if (v___x_511_ == 0)
{
v_x_505_ = v_tail_509_;
goto _start;
}
else
{
lean_object* v___x_513_; 
lean_inc(v_value_508_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v_value_508_);
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg___boxed(lean_object* v_a_514_, lean_object* v_x_515_){
_start:
{
uint32_t v_a_boxed_516_; lean_object* v_res_517_; 
v_a_boxed_516_ = lean_unbox_uint32(v_a_514_);
lean_dec(v_a_514_);
v_res_517_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_boxed_516_, v_x_515_);
lean_dec(v_x_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(lean_object* v_m_518_, uint32_t v_a_519_){
_start:
{
lean_object* v_buckets_520_; lean_object* v___x_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; uint64_t v_fold_525_; uint64_t v___x_526_; uint64_t v___x_527_; uint64_t v___x_528_; size_t v___x_529_; size_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_buckets_520_ = lean_ctor_get(v_m_518_, 1);
v___x_521_ = lean_array_get_size(v_buckets_520_);
v___x_522_ = lean_uint32_to_uint64(v_a_519_);
v___x_523_ = 32ULL;
v___x_524_ = lean_uint64_shift_right(v___x_522_, v___x_523_);
v_fold_525_ = lean_uint64_xor(v___x_522_, v___x_524_);
v___x_526_ = 16ULL;
v___x_527_ = lean_uint64_shift_right(v_fold_525_, v___x_526_);
v___x_528_ = lean_uint64_xor(v_fold_525_, v___x_527_);
v___x_529_ = lean_uint64_to_usize(v___x_528_);
v___x_530_ = lean_usize_of_nat(v___x_521_);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_sub(v___x_530_, v___x_531_);
v___x_533_ = lean_usize_land(v___x_529_, v___x_532_);
v___x_534_ = lean_array_uget_borrowed(v_buckets_520_, v___x_533_);
v___x_535_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_519_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg___boxed(lean_object* v_m_536_, lean_object* v_a_537_){
_start:
{
uint32_t v_a_boxed_538_; lean_object* v_res_539_; 
v_a_boxed_538_ = lean_unbox_uint32(v_a_537_);
lean_dec(v_a_537_);
v_res_539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_536_, v_a_boxed_538_);
lean_dec_ref(v_m_536_);
return v_res_539_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(uint32_t v_a_540_, lean_object* v_x_541_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
uint8_t v___x_542_; 
v___x_542_ = 0;
return v___x_542_;
}
else
{
lean_object* v_key_543_; lean_object* v_tail_544_; uint32_t v___x_545_; uint8_t v___x_546_; 
v_key_543_ = lean_ctor_get(v_x_541_, 0);
v_tail_544_ = lean_ctor_get(v_x_541_, 2);
v___x_545_ = lean_unbox_uint32(v_key_543_);
v___x_546_ = lean_uint32_dec_eq(v___x_545_, v_a_540_);
if (v___x_546_ == 0)
{
v_x_541_ = v_tail_544_;
goto _start;
}
else
{
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg___boxed(lean_object* v_a_548_, lean_object* v_x_549_){
_start:
{
uint32_t v_a_boxed_550_; uint8_t v_res_551_; lean_object* v_r_552_; 
v_a_boxed_550_ = lean_unbox_uint32(v_a_548_);
lean_dec(v_a_548_);
v_res_551_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_boxed_550_, v_x_549_);
lean_dec(v_x_549_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(uint32_t v_a_553_, lean_object* v_b_554_, lean_object* v_x_555_){
_start:
{
if (lean_obj_tag(v_x_555_) == 0)
{
lean_dec(v_b_554_);
return v_x_555_;
}
else
{
lean_object* v_key_556_; lean_object* v_value_557_; lean_object* v_tail_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_572_; 
v_key_556_ = lean_ctor_get(v_x_555_, 0);
v_value_557_ = lean_ctor_get(v_x_555_, 1);
v_tail_558_ = lean_ctor_get(v_x_555_, 2);
v_isSharedCheck_572_ = !lean_is_exclusive(v_x_555_);
if (v_isSharedCheck_572_ == 0)
{
v___x_560_ = v_x_555_;
v_isShared_561_ = v_isSharedCheck_572_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_tail_558_);
lean_inc(v_value_557_);
lean_inc(v_key_556_);
lean_dec(v_x_555_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_572_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
uint32_t v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_unbox_uint32(v_key_556_);
v___x_563_ = lean_uint32_dec_eq(v___x_562_, v_a_553_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_553_, v_b_554_, v_tail_558_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 2, v___x_564_);
v___x_566_ = v___x_560_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_key_556_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_value_557_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec(v_value_557_);
lean_dec(v_key_556_);
v___x_568_ = lean_box_uint32(v_a_553_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_b_554_);
lean_ctor_set(v___x_560_, 0, v___x_568_);
v___x_570_ = v___x_560_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_b_554_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_tail_558_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg___boxed(lean_object* v_a_573_, lean_object* v_b_574_, lean_object* v_x_575_){
_start:
{
uint32_t v_a_boxed_576_; lean_object* v_res_577_; 
v_a_boxed_576_ = lean_unbox_uint32(v_a_573_);
lean_dec(v_a_573_);
v_res_577_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_boxed_576_, v_b_574_, v_x_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
return v_x_578_;
}
else
{
lean_object* v_key_580_; lean_object* v_value_581_; lean_object* v_tail_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_606_; 
v_key_580_ = lean_ctor_get(v_x_579_, 0);
v_value_581_ = lean_ctor_get(v_x_579_, 1);
v_tail_582_ = lean_ctor_get(v_x_579_, 2);
v_isSharedCheck_606_ = !lean_is_exclusive(v_x_579_);
if (v_isSharedCheck_606_ == 0)
{
v___x_584_ = v_x_579_;
v_isShared_585_ = v_isSharedCheck_606_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_tail_582_);
lean_inc(v_value_581_);
lean_inc(v_key_580_);
lean_dec(v_x_579_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_606_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; uint32_t v___x_587_; uint64_t v___x_588_; uint64_t v___x_589_; uint64_t v___x_590_; uint64_t v_fold_591_; uint64_t v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; size_t v___x_595_; size_t v___x_596_; size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_586_ = lean_array_get_size(v_x_578_);
v___x_587_ = lean_unbox_uint32(v_key_580_);
v___x_588_ = lean_uint32_to_uint64(v___x_587_);
v___x_589_ = 32ULL;
v___x_590_ = lean_uint64_shift_right(v___x_588_, v___x_589_);
v_fold_591_ = lean_uint64_xor(v___x_588_, v___x_590_);
v___x_592_ = 16ULL;
v___x_593_ = lean_uint64_shift_right(v_fold_591_, v___x_592_);
v___x_594_ = lean_uint64_xor(v_fold_591_, v___x_593_);
v___x_595_ = lean_uint64_to_usize(v___x_594_);
v___x_596_ = lean_usize_of_nat(v___x_586_);
v___x_597_ = ((size_t)1ULL);
v___x_598_ = lean_usize_sub(v___x_596_, v___x_597_);
v___x_599_ = lean_usize_land(v___x_595_, v___x_598_);
v___x_600_ = lean_array_uget_borrowed(v_x_578_, v___x_599_);
lean_inc(v___x_600_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 2, v___x_600_);
v___x_602_ = v___x_584_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_key_580_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_value_581_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v___x_600_);
v___x_602_ = v_reuseFailAlloc_605_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; 
v___x_603_ = lean_array_uset(v_x_578_, v___x_599_, v___x_602_);
v_x_578_ = v___x_603_;
v_x_579_ = v_tail_582_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(lean_object* v_i_607_, lean_object* v_source_608_, lean_object* v_target_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_source_608_);
v___x_611_ = lean_nat_dec_lt(v_i_607_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec_ref(v_source_608_);
lean_dec(v_i_607_);
return v_target_609_;
}
else
{
lean_object* v_es_612_; lean_object* v___x_613_; lean_object* v_source_614_; lean_object* v_target_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_es_612_ = lean_array_fget(v_source_608_, v_i_607_);
v___x_613_ = lean_box(0);
v_source_614_ = lean_array_fset(v_source_608_, v_i_607_, v___x_613_);
v_target_615_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(v_target_609_, v_es_612_);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_add(v_i_607_, v___x_616_);
lean_dec(v_i_607_);
v_i_607_ = v___x_617_;
v_source_608_ = v_source_614_;
v_target_609_ = v_target_615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(lean_object* v_data_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_nbuckets_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_620_ = lean_array_get_size(v_data_619_);
v___x_621_ = lean_unsigned_to_nat(2u);
v_nbuckets_622_ = lean_nat_mul(v___x_620_, v___x_621_);
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_box(0);
v___x_625_ = lean_mk_array(v_nbuckets_622_, v___x_624_);
v___x_626_ = lean_array_propagate_mark(v_data_619_, v___x_625_);
v___x_627_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v___x_623_, v_data_619_, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(lean_object* v_m_628_, uint32_t v_a_629_, lean_object* v_b_630_){
_start:
{
lean_object* v_size_631_; lean_object* v_buckets_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_676_; 
v_size_631_ = lean_ctor_get(v_m_628_, 0);
v_buckets_632_ = lean_ctor_get(v_m_628_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_m_628_);
if (v_isSharedCheck_676_ == 0)
{
v___x_634_ = v_m_628_;
v_isShared_635_ = v_isSharedCheck_676_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_buckets_632_);
lean_inc(v_size_631_);
lean_dec(v_m_628_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_676_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; uint64_t v___x_637_; uint64_t v___x_638_; uint64_t v___x_639_; uint64_t v_fold_640_; uint64_t v___x_641_; uint64_t v___x_642_; uint64_t v___x_643_; size_t v___x_644_; size_t v___x_645_; size_t v___x_646_; size_t v___x_647_; size_t v___x_648_; lean_object* v_bkt_649_; uint8_t v___x_650_; 
v___x_636_ = lean_array_get_size(v_buckets_632_);
v___x_637_ = lean_uint32_to_uint64(v_a_629_);
v___x_638_ = 32ULL;
v___x_639_ = lean_uint64_shift_right(v___x_637_, v___x_638_);
v_fold_640_ = lean_uint64_xor(v___x_637_, v___x_639_);
v___x_641_ = 16ULL;
v___x_642_ = lean_uint64_shift_right(v_fold_640_, v___x_641_);
v___x_643_ = lean_uint64_xor(v_fold_640_, v___x_642_);
v___x_644_ = lean_uint64_to_usize(v___x_643_);
v___x_645_ = lean_usize_of_nat(v___x_636_);
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_sub(v___x_645_, v___x_646_);
v___x_648_ = lean_usize_land(v___x_644_, v___x_647_);
v_bkt_649_ = lean_array_uget_borrowed(v_buckets_632_, v___x_648_);
v___x_650_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_629_, v_bkt_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v_size_x27_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v_buckets_x27_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v_size_x27_652_ = lean_nat_add(v_size_631_, v___x_651_);
lean_dec(v_size_631_);
v___x_653_ = lean_box_uint32(v_a_629_);
lean_inc(v_bkt_649_);
v___x_654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_b_630_);
lean_ctor_set(v___x_654_, 2, v_bkt_649_);
v_buckets_x27_655_ = lean_array_uset(v_buckets_632_, v___x_648_, v___x_654_);
v___x_656_ = lean_unsigned_to_nat(4u);
v___x_657_ = lean_nat_mul(v_size_x27_652_, v___x_656_);
v___x_658_ = lean_unsigned_to_nat(3u);
v___x_659_ = lean_nat_div(v___x_657_, v___x_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_array_get_size(v_buckets_x27_655_);
v___x_661_ = lean_nat_dec_le(v___x_659_, v___x_660_);
lean_dec(v___x_659_);
if (v___x_661_ == 0)
{
lean_object* v_val_662_; lean_object* v___x_664_; 
v_val_662_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_buckets_x27_655_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v_val_662_);
lean_ctor_set(v___x_634_, 0, v_size_x27_652_);
v___x_664_ = v___x_634_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_size_x27_652_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_val_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
lean_object* v___x_667_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v_buckets_x27_655_);
lean_ctor_set(v___x_634_, 0, v_size_x27_652_);
v___x_667_ = v___x_634_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_size_x27_652_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_buckets_x27_655_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v___x_669_; lean_object* v_buckets_x27_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
lean_inc(v_bkt_649_);
v___x_669_ = lean_box(0);
v_buckets_x27_670_ = lean_array_uset(v_buckets_632_, v___x_648_, v___x_669_);
v___x_671_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_629_, v_b_630_, v_bkt_649_);
v___x_672_ = lean_array_uset(v_buckets_x27_670_, v___x_648_, v___x_671_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_672_);
v___x_674_ = v___x_634_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_size_631_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg___boxed(lean_object* v_m_677_, lean_object* v_a_678_, lean_object* v_b_679_){
_start:
{
uint32_t v_a_boxed_680_; lean_object* v_res_681_; 
v_a_boxed_680_ = lean_unbox_uint32(v_a_678_);
lean_dec(v_a_678_);
v_res_681_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_677_, v_a_boxed_680_, v_b_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(lean_object* v_histogram_682_, lean_object* v_index_683_, uint32_t v_val_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_682_, v_val_684_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_box(0);
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v_index_683_);
v___x_690_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_690_, 0, v___x_686_);
lean_ctor_set(v___x_690_, 1, v___x_687_);
lean_ctor_set(v___x_690_, 2, v___x_688_);
lean_ctor_set(v___x_690_, 3, v___x_689_);
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_682_, v_val_684_, v___x_690_);
return v___x_691_;
}
else
{
lean_object* v_val_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_713_; 
v_val_692_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_713_ == 0)
{
v___x_694_ = v___x_685_;
v_isShared_695_ = v_isSharedCheck_713_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_val_692_);
lean_dec(v___x_685_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_713_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_leftCount_696_; lean_object* v_leftIndex_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_710_; 
v_leftCount_696_ = lean_ctor_get(v_val_692_, 0);
v_leftIndex_697_ = lean_ctor_get(v_val_692_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_val_692_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; lean_object* v_unused_712_; 
v_unused_711_ = lean_ctor_get(v_val_692_, 3);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_val_692_, 2);
lean_dec(v_unused_712_);
v___x_699_ = v_val_692_;
v_isShared_700_ = v_isSharedCheck_710_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_leftIndex_697_);
lean_inc(v_leftCount_696_);
lean_dec(v_val_692_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_710_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_nat_add(v_leftCount_696_, v___x_701_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_index_683_);
v___x_704_ = v___x_694_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_index_683_);
v___x_704_ = v_reuseFailAlloc_709_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 3, v___x_704_);
lean_ctor_set(v___x_699_, 2, v___x_702_);
v___x_706_ = v___x_699_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_leftCount_696_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_leftIndex_697_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v___x_704_);
v___x_706_ = v_reuseFailAlloc_708_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_682_, v_val_684_, v___x_706_);
return v___x_707_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_histogram_714_, lean_object* v_index_715_, lean_object* v_val_716_){
_start:
{
uint32_t v_val_boxed_717_; lean_object* v_res_718_; 
v_val_boxed_717_ = lean_unbox_uint32(v_val_716_);
lean_dec(v_val_716_);
v_res_718_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_714_, v_index_715_, v_val_boxed_717_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(lean_object* v_upperBound_719_, lean_object* v___x_720_, lean_object* v_fst_721_, lean_object* v___x_722_, lean_object* v_a_723_, lean_object* v_b_724_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = lean_nat_dec_lt(v_a_723_, v_upperBound_719_);
if (v___x_725_ == 0)
{
lean_dec(v_a_723_);
return v_b_724_;
}
else
{
lean_object* v___x_726_; uint32_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_726_ = l_Subarray_get___redArg(v_fst_721_, v_a_723_);
v___x_727_ = lean_unbox_uint32(v___x_726_);
lean_dec(v___x_726_);
lean_inc(v_a_723_);
v___x_728_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_b_724_, v_a_723_, v___x_727_);
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_add(v_a_723_, v___x_729_);
lean_dec(v_a_723_);
v_a_723_ = v___x_730_;
v_b_724_ = v___x_728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_upperBound_732_, lean_object* v___x_733_, lean_object* v_fst_734_, lean_object* v___x_735_, lean_object* v_a_736_, lean_object* v_b_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_732_, v___x_733_, v_fst_734_, v___x_735_, v_a_736_, v_b_737_);
lean_dec(v___x_735_);
lean_dec_ref(v_fst_734_);
lean_dec(v___x_733_);
lean_dec(v_upperBound_732_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(lean_object* v_as_x27_739_, lean_object* v_b_740_){
_start:
{
if (lean_obj_tag(v_as_x27_739_) == 0)
{
return v_b_740_;
}
else
{
lean_object* v_head_741_; lean_object* v_snd_742_; lean_object* v_leftIndex_743_; 
v_head_741_ = lean_ctor_get(v_as_x27_739_, 0);
v_snd_742_ = lean_ctor_get(v_head_741_, 1);
v_leftIndex_743_ = lean_ctor_get(v_snd_742_, 1);
if (lean_obj_tag(v_leftIndex_743_) == 1)
{
lean_object* v_rightIndex_744_; 
v_rightIndex_744_ = lean_ctor_get(v_snd_742_, 3);
if (lean_obj_tag(v_rightIndex_744_) == 1)
{
if (lean_obj_tag(v_b_740_) == 0)
{
lean_object* v_tail_745_; lean_object* v_fst_746_; lean_object* v_leftCount_747_; lean_object* v_rightCount_748_; lean_object* v_val_749_; lean_object* v_val_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_tail_745_ = lean_ctor_get(v_as_x27_739_, 1);
v_fst_746_ = lean_ctor_get(v_head_741_, 0);
v_leftCount_747_ = lean_ctor_get(v_snd_742_, 0);
v_rightCount_748_ = lean_ctor_get(v_snd_742_, 2);
v_val_749_ = lean_ctor_get(v_leftIndex_743_, 0);
v_val_750_ = lean_ctor_get(v_rightIndex_744_, 0);
v___x_751_ = lean_nat_add(v_leftCount_747_, v_rightCount_748_);
lean_inc(v_val_750_);
lean_inc(v_val_749_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_val_749_);
lean_ctor_set(v___x_752_, 1, v_val_750_);
lean_inc(v_fst_746_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_fst_746_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_751_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
v_as_x27_739_ = v_tail_745_;
v_b_740_ = v___x_755_;
goto _start;
}
else
{
lean_object* v_val_757_; lean_object* v_tail_758_; lean_object* v_fst_759_; lean_object* v_leftCount_760_; lean_object* v_rightCount_761_; lean_object* v_val_762_; lean_object* v_val_763_; lean_object* v_fst_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_785_; 
v_val_757_ = lean_ctor_get(v_b_740_, 0);
lean_inc(v_val_757_);
v_tail_758_ = lean_ctor_get(v_as_x27_739_, 1);
v_fst_759_ = lean_ctor_get(v_head_741_, 0);
v_leftCount_760_ = lean_ctor_get(v_snd_742_, 0);
v_rightCount_761_ = lean_ctor_get(v_snd_742_, 2);
v_val_762_ = lean_ctor_get(v_leftIndex_743_, 0);
v_val_763_ = lean_ctor_get(v_rightIndex_744_, 0);
v_fst_764_ = lean_ctor_get(v_val_757_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v_val_757_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_val_757_, 1);
lean_dec(v_unused_786_);
v___x_766_ = v_val_757_;
v_isShared_767_ = v_isSharedCheck_785_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_fst_764_);
lean_dec(v_val_757_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_785_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_nat_add(v_leftCount_760_, v_rightCount_761_);
v___x_769_ = lean_nat_dec_lt(v___x_768_, v_fst_764_);
lean_dec(v_fst_764_);
if (v___x_769_ == 0)
{
lean_dec(v___x_768_);
lean_del_object(v___x_766_);
v_as_x27_739_ = v_tail_758_;
goto _start;
}
else
{
lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_783_; 
v_isSharedCheck_783_ = !lean_is_exclusive(v_b_740_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_b_740_, 0);
lean_dec(v_unused_784_);
v___x_772_ = v_b_740_;
v_isShared_773_ = v_isSharedCheck_783_;
goto v_resetjp_771_;
}
else
{
lean_dec(v_b_740_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_783_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
lean_inc(v_val_763_);
lean_inc(v_val_762_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_val_763_);
lean_ctor_set(v___x_766_, 0, v_val_762_);
v___x_775_ = v___x_766_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_val_762_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_val_763_);
v___x_775_ = v_reuseFailAlloc_782_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
lean_inc(v_fst_759_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_fst_759_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_768_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_777_);
v___x_779_ = v___x_772_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_781_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
v_as_x27_739_ = v_tail_758_;
v_b_740_ = v___x_779_;
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
lean_object* v_tail_787_; 
v_tail_787_ = lean_ctor_get(v_as_x27_739_, 1);
v_as_x27_739_ = v_tail_787_;
goto _start;
}
}
else
{
lean_object* v_tail_789_; 
v_tail_789_ = lean_ctor_get(v_as_x27_739_, 1);
v_as_x27_739_ = v_tail_789_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_as_x27_791_, lean_object* v_b_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_791_, v_b_792_);
lean_dec(v_as_x27_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_a_794_, lean_object* v_b_795_){
_start:
{
lean_object* v_array_796_; lean_object* v_start_797_; lean_object* v_stop_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_811_; 
v_array_796_ = lean_ctor_get(v_a_794_, 0);
v_start_797_ = lean_ctor_get(v_a_794_, 1);
v_stop_798_ = lean_ctor_get(v_a_794_, 2);
v_isSharedCheck_811_ = !lean_is_exclusive(v_a_794_);
if (v_isSharedCheck_811_ == 0)
{
v___x_800_ = v_a_794_;
v_isShared_801_ = v_isSharedCheck_811_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_stop_798_);
lean_inc(v_start_797_);
lean_inc(v_array_796_);
lean_dec(v_a_794_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_811_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint8_t v___x_802_; 
v___x_802_ = lean_nat_dec_lt(v_start_797_, v_stop_798_);
if (v___x_802_ == 0)
{
lean_del_object(v___x_800_);
lean_dec(v_stop_798_);
lean_dec(v_start_797_);
lean_dec_ref(v_array_796_);
return v_b_795_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = lean_nat_add(v_start_797_, v___x_803_);
lean_inc_ref(v_array_796_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_804_);
v___x_806_ = v___x_800_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_array_796_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_stop_798_);
v___x_806_ = v_reuseFailAlloc_810_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_array_fget(v_array_796_, v_start_797_);
lean_dec(v_start_797_);
lean_dec_ref(v_array_796_);
v___x_808_ = lean_array_push(v_b_795_, v___x_807_);
v_a_794_ = v___x_806_;
v_b_795_ = v___x_808_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(lean_object* v_left_812_, lean_object* v_right_813_, lean_object* v_i_814_){
_start:
{
lean_object* v_start_815_; lean_object* v_stop_816_; lean_object* v___x_817_; uint8_t v___x_831_; 
v_start_815_ = lean_ctor_get(v_left_812_, 1);
v_stop_816_ = lean_ctor_get(v_left_812_, 2);
v___x_817_ = lean_nat_sub(v_stop_816_, v_start_815_);
v___x_831_ = lean_nat_dec_lt(v_i_814_, v___x_817_);
if (v___x_831_ == 0)
{
goto v___jp_818_;
}
else
{
lean_object* v_start_832_; lean_object* v_stop_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_start_832_ = lean_ctor_get(v_right_813_, 1);
v_stop_833_ = lean_ctor_get(v_right_813_, 2);
v___x_834_ = lean_nat_sub(v_stop_833_, v_start_832_);
v___x_835_ = lean_nat_dec_lt(v_i_814_, v___x_834_);
if (v___x_835_ == 0)
{
lean_dec(v___x_834_);
goto v___jp_818_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint32_t v___x_843_; uint32_t v___x_844_; uint8_t v___x_845_; 
v___x_836_ = lean_nat_sub(v___x_817_, v_i_814_);
lean_dec(v___x_817_);
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_sub(v___x_836_, v___x_837_);
v___x_839_ = l_Subarray_get___redArg(v_left_812_, v___x_838_);
lean_dec(v___x_838_);
v___x_840_ = lean_nat_sub(v___x_834_, v_i_814_);
lean_dec(v___x_834_);
v___x_841_ = lean_nat_sub(v___x_840_, v___x_837_);
v___x_842_ = l_Subarray_get___redArg(v_right_813_, v___x_841_);
lean_dec(v___x_841_);
v___x_843_ = lean_unbox_uint32(v___x_839_);
lean_dec(v___x_839_);
v___x_844_ = lean_unbox_uint32(v___x_842_);
lean_dec(v___x_842_);
v___x_845_ = lean_uint32_dec_eq(v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v_i_814_);
lean_inc_ref(v_left_812_);
v___x_846_ = l_Subarray_take___redArg(v_left_812_, v___x_836_);
v___x_847_ = l_Subarray_take___redArg(v_right_813_, v___x_840_);
lean_dec(v___x_840_);
v___x_848_ = l_Subarray_drop___redArg(v_left_812_, v___x_836_);
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
v___x_853_ = lean_nat_add(v_i_814_, v___x_837_);
lean_dec(v_i_814_);
v_i_814_ = v___x_853_;
goto _start;
}
}
}
v___jp_818_:
{
lean_object* v_start_819_; lean_object* v_stop_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_start_819_ = lean_ctor_get(v_right_813_, 1);
v_stop_820_ = lean_ctor_get(v_right_813_, 2);
v___x_821_ = lean_nat_sub(v___x_817_, v_i_814_);
lean_dec(v___x_817_);
lean_inc_ref(v_left_812_);
v___x_822_ = l_Subarray_take___redArg(v_left_812_, v___x_821_);
v___x_823_ = lean_nat_sub(v_stop_820_, v_start_819_);
v___x_824_ = lean_nat_sub(v___x_823_, v_i_814_);
lean_dec(v_i_814_);
lean_dec(v___x_823_);
v___x_825_ = l_Subarray_take___redArg(v_right_813_, v___x_824_);
lean_dec(v___x_824_);
v___x_826_ = l_Subarray_drop___redArg(v_left_812_, v___x_821_);
lean_dec(v___x_821_);
v___x_827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_828_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v___x_826_, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_825_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_822_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(lean_object* v_left_855_, lean_object* v_right_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(v_left_855_, v_right_856_, v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
if (lean_obj_tag(v_x_860_) == 0)
{
lean_inc(v_x_859_);
return v_x_859_;
}
else
{
lean_object* v_key_861_; lean_object* v_value_862_; lean_object* v_tail_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_key_861_ = lean_ctor_get(v_x_860_, 0);
v_value_862_ = lean_ctor_get(v_x_860_, 1);
v_tail_863_ = lean_ctor_get(v_x_860_, 2);
v___x_864_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_859_, v_tail_863_);
lean_inc(v_value_862_);
lean_inc(v_key_861_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v_key_861_);
lean_ctor_set(v___x_865_, 1, v_value_862_);
v___x_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v___x_864_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8___boxed(lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_867_, v_x_868_);
lean_dec(v_x_868_);
lean_dec(v_x_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(lean_object* v_as_870_, size_t v_i_871_, size_t v_stop_872_, lean_object* v_b_873_){
_start:
{
uint8_t v___x_874_; 
v___x_874_ = lean_usize_dec_eq(v_i_871_, v_stop_872_);
if (v___x_874_ == 0)
{
size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_sub(v_i_871_, v___x_875_);
v___x_877_ = lean_array_uget_borrowed(v_as_870_, v___x_876_);
v___x_878_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_b_873_, v___x_877_);
lean_dec(v_b_873_);
v_i_871_ = v___x_876_;
v_b_873_ = v___x_878_;
goto _start;
}
else
{
return v_b_873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9___boxed(lean_object* v_as_880_, lean_object* v_i_881_, lean_object* v_stop_882_, lean_object* v_b_883_){
_start:
{
size_t v_i_boxed_884_; size_t v_stop_boxed_885_; lean_object* v_res_886_; 
v_i_boxed_884_ = lean_unbox_usize(v_i_881_);
lean_dec(v_i_881_);
v_stop_boxed_885_ = lean_unbox_usize(v_stop_882_);
lean_dec(v_stop_882_);
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_as_880_, v_i_boxed_884_, v_stop_boxed_885_, v_b_883_);
lean_dec_ref(v_as_880_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(lean_object* v_left_887_, lean_object* v_right_888_, lean_object* v_pref_889_){
_start:
{
lean_object* v_start_890_; lean_object* v_stop_891_; lean_object* v_i_892_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_start_890_ = lean_ctor_get(v_left_887_, 1);
v_stop_891_ = lean_ctor_get(v_left_887_, 2);
v_i_892_ = lean_array_get_size(v_pref_889_);
v___x_898_ = lean_nat_sub(v_stop_891_, v_start_890_);
v___x_899_ = lean_nat_dec_lt(v_i_892_, v___x_898_);
lean_dec(v___x_898_);
if (v___x_899_ == 0)
{
goto v___jp_893_;
}
else
{
lean_object* v_start_900_; lean_object* v_stop_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_start_900_ = lean_ctor_get(v_right_888_, 1);
v_stop_901_ = lean_ctor_get(v_right_888_, 2);
v___x_902_ = lean_nat_sub(v_stop_901_, v_start_900_);
v___x_903_ = lean_nat_dec_lt(v_i_892_, v___x_902_);
lean_dec(v___x_902_);
if (v___x_903_ == 0)
{
goto v___jp_893_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; uint32_t v___x_906_; uint32_t v___x_907_; uint8_t v___x_908_; 
v___x_904_ = l_Subarray_get___redArg(v_left_887_, v_i_892_);
v___x_905_ = l_Subarray_get___redArg(v_right_888_, v_i_892_);
v___x_906_ = lean_unbox_uint32(v___x_904_);
v___x_907_ = lean_unbox_uint32(v___x_905_);
lean_dec(v___x_905_);
v___x_908_ = lean_uint32_dec_eq(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec(v___x_904_);
v___x_909_ = l_Subarray_drop___redArg(v_left_887_, v_i_892_);
v___x_910_ = l_Subarray_drop___redArg(v_right_888_, v_i_892_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_pref_889_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; 
v___x_913_ = lean_array_push(v_pref_889_, v___x_904_);
v_pref_889_ = v___x_913_;
goto _start;
}
}
}
v___jp_893_:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_894_ = l_Subarray_drop___redArg(v_left_887_, v_i_892_);
v___x_895_ = l_Subarray_drop___redArg(v_right_888_, v_i_892_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v_pref_889_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(lean_object* v_left_915_, lean_object* v_right_916_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_918_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(v_left_915_, v_right_916_, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(lean_object* v_histogram_919_, lean_object* v_index_920_, uint32_t v_val_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_919_, v_val_921_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_924_, 0, v_index_920_);
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_box(0);
v___x_927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_927_, 0, v___x_923_);
lean_ctor_set(v___x_927_, 1, v___x_924_);
lean_ctor_set(v___x_927_, 2, v___x_925_);
lean_ctor_set(v___x_927_, 3, v___x_926_);
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_919_, v_val_921_, v___x_927_);
return v___x_928_;
}
else
{
lean_object* v_val_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_950_; 
v_val_929_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_950_ == 0)
{
v___x_931_ = v___x_922_;
v_isShared_932_ = v_isSharedCheck_950_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_val_929_);
lean_dec(v___x_922_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_950_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_leftCount_933_; lean_object* v_rightCount_934_; lean_object* v_rightIndex_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_948_; 
v_leftCount_933_ = lean_ctor_get(v_val_929_, 0);
v_rightCount_934_ = lean_ctor_get(v_val_929_, 2);
v_rightIndex_935_ = lean_ctor_get(v_val_929_, 3);
v_isSharedCheck_948_ = !lean_is_exclusive(v_val_929_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_val_929_, 1);
lean_dec(v_unused_949_);
v___x_937_ = v_val_929_;
v_isShared_938_ = v_isSharedCheck_948_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_rightIndex_935_);
lean_inc(v_rightCount_934_);
lean_inc(v_leftCount_933_);
lean_dec(v_val_929_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_948_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_add(v_leftCount_933_, v___x_939_);
lean_dec(v_leftCount_933_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v_index_920_);
v___x_942_ = v___x_931_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_index_920_);
v___x_942_ = v_reuseFailAlloc_947_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v___x_942_);
lean_ctor_set(v___x_937_, 0, v___x_940_);
v___x_944_ = v___x_937_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_rightCount_934_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_rightIndex_935_);
v___x_944_ = v_reuseFailAlloc_946_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_919_, v_val_921_, v___x_944_);
return v___x_945_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg___boxed(lean_object* v_histogram_951_, lean_object* v_index_952_, lean_object* v_val_953_){
_start:
{
uint32_t v_val_boxed_954_; lean_object* v_res_955_; 
v_val_boxed_954_ = lean_unbox_uint32(v_val_953_);
lean_dec(v_val_953_);
v_res_955_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_951_, v_index_952_, v_val_boxed_954_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(lean_object* v_upperBound_956_, lean_object* v_fst_957_, lean_object* v___x_958_, lean_object* v_fst_959_, lean_object* v_a_960_, lean_object* v_b_961_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = lean_nat_dec_lt(v_a_960_, v_upperBound_956_);
if (v___x_962_ == 0)
{
lean_dec(v_a_960_);
return v_b_961_;
}
else
{
lean_object* v___x_963_; uint32_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_963_ = l_Subarray_get___redArg(v_fst_959_, v_a_960_);
v___x_964_ = lean_unbox_uint32(v___x_963_);
lean_dec(v___x_963_);
lean_inc(v_a_960_);
v___x_965_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_b_961_, v_a_960_, v___x_964_);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_a_960_, v___x_966_);
lean_dec(v_a_960_);
v_a_960_ = v___x_967_;
v_b_961_ = v___x_965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg___boxed(lean_object* v_upperBound_969_, lean_object* v_fst_970_, lean_object* v___x_971_, lean_object* v_fst_972_, lean_object* v_a_973_, lean_object* v_b_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_969_, v_fst_970_, v___x_971_, v_fst_972_, v_a_973_, v_b_974_);
lean_dec_ref(v_fst_972_);
lean_dec(v___x_971_);
lean_dec_ref(v_fst_970_);
lean_dec(v_upperBound_969_);
return v_res_975_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_box(0);
v___x_977_ = lean_unsigned_to_nat(16u);
v___x_978_ = lean_mk_array(v___x_977_, v___x_976_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_hist_981_; 
v___x_979_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0);
v___x_980_ = lean_unsigned_to_nat(0u);
v_hist_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_981_, 0, v___x_980_);
lean_ctor_set(v_hist_981_, 1, v___x_979_);
return v_hist_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_left_982_, lean_object* v_right_983_){
_start:
{
lean_object* v___x_984_; lean_object* v_snd_985_; lean_object* v_fst_986_; lean_object* v_fst_987_; lean_object* v_snd_988_; lean_object* v___x_989_; lean_object* v_snd_990_; lean_object* v_fst_991_; lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v_start_994_; lean_object* v_stop_995_; lean_object* v___x_996_; lean_object* v_hist_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_start_1000_; lean_object* v_stop_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v_buckets_1004_; lean_object* v___x_1005_; lean_object* v___y_1007_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_984_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(v_left_982_, v_right_983_);
v_snd_985_ = lean_ctor_get(v___x_984_, 1);
lean_inc(v_snd_985_);
v_fst_986_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_fst_986_);
lean_dec_ref(v___x_984_);
v_fst_987_ = lean_ctor_get(v_snd_985_, 0);
lean_inc(v_fst_987_);
v_snd_988_ = lean_ctor_get(v_snd_985_, 1);
lean_inc(v_snd_988_);
lean_dec(v_snd_985_);
v___x_989_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(v_fst_987_, v_snd_988_);
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
v_start_994_ = lean_ctor_get(v_fst_991_, 1);
v_stop_995_ = lean_ctor_get(v_fst_991_, 2);
v___x_996_ = lean_unsigned_to_nat(0u);
v_hist_997_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1);
v___x_998_ = lean_nat_sub(v_stop_995_, v_start_994_);
v___x_999_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v___x_998_, v_fst_992_, v___x_998_, v_fst_991_, v___x_996_, v_hist_997_);
v_start_1000_ = lean_ctor_get(v_fst_992_, 1);
v_stop_1001_ = lean_ctor_get(v_fst_992_, 2);
v___x_1002_ = lean_nat_sub(v_stop_1001_, v_start_1000_);
v___x_1003_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v___x_1002_, v___x_1002_, v_fst_992_, v___x_998_, v___x_996_, v___x_999_);
lean_dec(v___x_998_);
lean_dec(v___x_1002_);
v_buckets_1004_ = lean_ctor_get(v___x_1003_, 1);
lean_inc_ref(v_buckets_1004_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = lean_box(0);
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_array_get_size(v_buckets_1004_);
v___x_1035_ = lean_nat_dec_lt(v___x_996_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_dec_ref(v_buckets_1004_);
v___y_1007_ = v___x_1033_;
goto v___jp_1006_;
}
else
{
size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = lean_usize_of_nat(v___x_1034_);
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_buckets_1004_, v___x_1036_, v___x_1037_, v___x_1033_);
lean_dec_ref(v_buckets_1004_);
v___y_1007_ = v___x_1038_;
goto v___jp_1006_;
}
v___jp_1006_:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v___y_1007_, v___x_1005_);
lean_dec(v___y_1007_);
if (lean_obj_tag(v___x_1008_) == 1)
{
lean_object* v_val_1009_; lean_object* v_snd_1010_; lean_object* v_snd_1011_; lean_object* v_fst_1012_; lean_object* v_fst_1013_; lean_object* v_snd_1014_; lean_object* v___x_1015_; lean_object* v_fst_1016_; lean_object* v_snd_1017_; lean_object* v___x_1018_; lean_object* v_fst_1019_; lean_object* v_snd_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_val_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_val_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v_snd_1010_ = lean_ctor_get(v_val_1009_, 1);
lean_inc(v_snd_1010_);
lean_dec(v_val_1009_);
v_snd_1011_ = lean_ctor_get(v_snd_1010_, 1);
lean_inc(v_snd_1011_);
v_fst_1012_ = lean_ctor_get(v_snd_1010_, 0);
lean_inc(v_fst_1012_);
lean_dec(v_snd_1010_);
v_fst_1013_ = lean_ctor_get(v_snd_1011_, 0);
lean_inc(v_fst_1013_);
v_snd_1014_ = lean_ctor_get(v_snd_1011_, 1);
lean_inc(v_snd_1014_);
lean_dec(v_snd_1011_);
v___x_1015_ = l_Subarray_split___redArg(v_fst_991_, v_fst_1013_);
lean_dec(v_fst_1013_);
v_fst_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_fst_1016_);
v_snd_1017_ = lean_ctor_get(v___x_1015_, 1);
lean_inc(v_snd_1017_);
lean_dec_ref(v___x_1015_);
v___x_1018_ = l_Subarray_split___redArg(v_fst_992_, v_snd_1014_);
lean_dec(v_snd_1014_);
v_fst_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_fst_1019_);
v_snd_1020_ = lean_ctor_get(v___x_1018_, 1);
lean_inc(v_snd_1020_);
lean_dec_ref(v___x_1018_);
v___x_1021_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_fst_1016_, v_fst_1019_);
v___x_1022_ = l_Array_append___redArg(v_fst_986_, v___x_1021_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_mk_empty_array_with_capacity(v___x_1023_);
v___x_1025_ = lean_array_push(v___x_1024_, v_fst_1012_);
v___x_1026_ = l_Array_append___redArg(v___x_1022_, v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = l_Subarray_drop___redArg(v_snd_1017_, v___x_1023_);
v___x_1028_ = l_Subarray_drop___redArg(v_snd_1020_, v___x_1023_);
v___x_1029_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1027_, v___x_1028_);
v___x_1030_ = l_Array_append___redArg(v___x_1026_, v___x_1029_);
lean_dec_ref(v___x_1029_);
v___x_1031_ = l_Array_append___redArg(v___x_1030_, v_snd_993_);
lean_dec(v_snd_993_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; 
lean_dec(v___x_1008_);
lean_dec(v_fst_992_);
lean_dec(v_fst_991_);
v___x_1032_ = l_Array_append___redArg(v_fst_986_, v_snd_993_);
lean_dec(v_snd_993_);
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(lean_object* v___x_1039_, lean_object* v_edited_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_fst_1042_; lean_object* v_snd_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1062_; 
v_fst_1042_ = lean_ctor_get(v_a_1041_, 0);
v_snd_1043_ = lean_ctor_get(v_a_1041_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_a_1041_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1045_ = v_a_1041_;
v_isShared_1046_ = v_isSharedCheck_1062_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_snd_1043_);
lean_inc(v_fst_1042_);
lean_dec(v_a_1041_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1062_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_nat_dec_lt(v_snd_1043_, v___x_1039_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1049_; 
if (v_isShared_1046_ == 0)
{
v___x_1049_ = v___x_1045_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_fst_1042_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_snd_1043_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
else
{
uint8_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1051_ = 0;
v___x_1052_ = lean_array_fget_borrowed(v_edited_1040_, v_snd_1043_);
v___x_1053_ = lean_box(v___x_1051_);
lean_inc(v___x_1052_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 1, v___x_1052_);
lean_ctor_set(v___x_1045_, 0, v___x_1053_);
v___x_1055_ = v___x_1045_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1052_);
v___x_1055_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1056_ = lean_array_push(v_fst_1042_, v___x_1055_);
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_snd_1043_, v___x_1057_);
lean_dec(v_snd_1043_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1056_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v_a_1041_ = v___x_1059_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(lean_object* v___x_1063_, lean_object* v_edited_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1063_, v_edited_1064_, v_a_1065_);
lean_dec_ref(v_edited_1064_);
lean_dec(v___x_1063_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t v_sz_1067_, size_t v_i_1068_, lean_object* v_bs_1069_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_usize_dec_lt(v_i_1068_, v_sz_1067_);
if (v___x_1070_ == 0)
{
return v_bs_1069_;
}
else
{
lean_object* v_v_1071_; lean_object* v___x_1072_; lean_object* v_bs_x27_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; size_t v___x_1077_; size_t v___x_1078_; lean_object* v___x_1079_; 
v_v_1071_ = lean_array_uget(v_bs_1069_, v_i_1068_);
v___x_1072_ = lean_unsigned_to_nat(0u);
v_bs_x27_1073_ = lean_array_uset(v_bs_1069_, v_i_1068_, v___x_1072_);
v___x_1074_ = 1;
v___x_1075_ = lean_box(v___x_1074_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v_v_1071_);
v___x_1077_ = ((size_t)1ULL);
v___x_1078_ = lean_usize_add(v_i_1068_, v___x_1077_);
v___x_1079_ = lean_array_uset(v_bs_x27_1073_, v_i_1068_, v___x_1076_);
v_i_1068_ = v___x_1078_;
v_bs_1069_ = v___x_1079_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object* v_sz_1081_, lean_object* v_i_1082_, lean_object* v_bs_1083_){
_start:
{
size_t v_sz_boxed_1084_; size_t v_i_boxed_1085_; lean_object* v_res_1086_; 
v_sz_boxed_1084_ = lean_unbox_usize(v_sz_1081_);
lean_dec(v_sz_1081_);
v_i_boxed_1085_ = lean_unbox_usize(v_i_1082_);
lean_dec(v_i_1082_);
v_res_1086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_boxed_1084_, v_i_boxed_1085_, v_bs_1083_);
return v_res_1086_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = 65;
v___x_1088_ = lean_box_uint32(v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(lean_object* v___x_1089_, lean_object* v_original_1090_, uint32_t v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_fst_1093_; lean_object* v_snd_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1119_; 
v_fst_1093_ = lean_ctor_get(v_a_1092_, 0);
v_snd_1094_ = lean_ctor_get(v_a_1092_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1096_ = v_a_1092_;
v_isShared_1097_ = v_isSharedCheck_1119_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_snd_1094_);
lean_inc(v_fst_1093_);
lean_dec(v_a_1092_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1119_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_nat_dec_lt(v_snd_1094_, v___x_1089_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1100_; 
if (v_isShared_1097_ == 0)
{
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_fst_1093_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_snd_1094_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; uint32_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1102_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1103_ = lean_array_get_borrowed(v___x_1102_, v_original_1090_, v_snd_1094_);
v___x_1104_ = lean_unbox_uint32(v___x_1103_);
v___x_1105_ = lean_uint32_dec_eq(v___x_1104_, v_a_1091_);
if (v___x_1105_ == 0)
{
uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1106_ = 1;
v___x_1107_ = lean_box(v___x_1106_);
lean_inc(v___x_1103_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v___x_1103_);
lean_ctor_set(v___x_1096_, 0, v___x_1107_);
v___x_1109_ = v___x_1096_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v___x_1103_);
v___x_1109_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1110_ = lean_array_push(v_fst_1093_, v___x_1109_);
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_snd_1094_, v___x_1111_);
lean_dec(v_snd_1094_);
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1110_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v_a_1092_ = v___x_1113_;
goto _start;
}
}
else
{
lean_object* v___x_1117_; 
if (v_isShared_1097_ == 0)
{
v___x_1117_ = v___x_1096_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_fst_1093_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_snd_1094_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_1120_, lean_object* v_original_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
uint32_t v_a_boxed_1124_; lean_object* v_res_1125_; 
v_a_boxed_1124_ = lean_unbox_uint32(v_a_1122_);
lean_dec(v_a_1122_);
v_res_1125_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1120_, v_original_1121_, v_a_boxed_1124_, v_a_1123_);
lean_dec_ref(v_original_1121_);
lean_dec(v___x_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(lean_object* v___x_1126_, lean_object* v_edited_1127_, uint32_t v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_fst_1130_; lean_object* v_snd_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1156_; 
v_fst_1130_ = lean_ctor_get(v_a_1129_, 0);
v_snd_1131_ = lean_ctor_get(v_a_1129_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_a_1129_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1133_ = v_a_1129_;
v_isShared_1134_ = v_isSharedCheck_1156_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_snd_1131_);
lean_inc(v_fst_1130_);
lean_dec(v_a_1129_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1156_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
uint8_t v___x_1135_; 
v___x_1135_ = lean_nat_dec_lt(v_snd_1131_, v___x_1126_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1137_; 
if (v_isShared_1134_ == 0)
{
v___x_1137_ = v___x_1133_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_fst_1130_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_snd_1131_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; uint32_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1139_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1140_ = lean_array_get_borrowed(v___x_1139_, v_edited_1127_, v_snd_1131_);
v___x_1141_ = lean_unbox_uint32(v___x_1140_);
v___x_1142_ = lean_uint32_dec_eq(v___x_1141_, v_a_1128_);
if (v___x_1142_ == 0)
{
uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1143_ = 0;
v___x_1144_ = lean_box(v___x_1143_);
lean_inc(v___x_1140_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 1, v___x_1140_);
lean_ctor_set(v___x_1133_, 0, v___x_1144_);
v___x_1146_ = v___x_1133_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v___x_1140_);
v___x_1146_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1147_ = lean_array_push(v_fst_1130_, v___x_1146_);
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_add(v_snd_1131_, v___x_1148_);
lean_dec(v_snd_1131_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1147_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v_a_1129_ = v___x_1150_;
goto _start;
}
}
else
{
lean_object* v___x_1154_; 
if (v_isShared_1134_ == 0)
{
v___x_1154_ = v___x_1133_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_fst_1130_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_snd_1131_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(lean_object* v___x_1157_, lean_object* v_edited_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
uint32_t v_a_boxed_1161_; lean_object* v_res_1162_; 
v_a_boxed_1161_ = lean_unbox_uint32(v_a_1159_);
lean_dec(v_a_1159_);
v_res_1162_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1157_, v_edited_1158_, v_a_boxed_1161_, v_a_1160_);
lean_dec_ref(v_edited_1158_);
lean_dec(v___x_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(lean_object* v___x_1163_, lean_object* v_original_1164_, lean_object* v___x_1165_, lean_object* v_edited_1166_, lean_object* v_as_1167_, size_t v_sz_1168_, size_t v_i_1169_, lean_object* v_b_1170_){
_start:
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_usize_dec_lt(v_i_1169_, v_sz_1168_);
if (v___x_1171_ == 0)
{
return v_b_1170_;
}
else
{
lean_object* v_snd_1172_; lean_object* v_fst_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1222_; 
v_snd_1172_ = lean_ctor_get(v_b_1170_, 1);
v_fst_1173_ = lean_ctor_get(v_b_1170_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_b_1170_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1175_ = v_b_1170_;
v_isShared_1176_ = v_isSharedCheck_1222_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_snd_1172_);
lean_inc(v_fst_1173_);
lean_dec(v_b_1170_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1222_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1221_; 
v_fst_1177_ = lean_ctor_get(v_snd_1172_, 0);
v_snd_1178_ = lean_ctor_get(v_snd_1172_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_snd_1172_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1180_ = v_snd_1172_;
v_isShared_1181_ = v_isSharedCheck_1221_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snd_1178_);
lean_inc(v_fst_1177_);
lean_dec(v_snd_1172_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1221_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_a_1182_; lean_object* v___x_1184_; 
v_a_1182_ = lean_array_uget_borrowed(v_as_1167_, v_i_1169_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v_fst_1177_);
lean_ctor_set(v___x_1180_, 0, v_fst_1173_);
v___x_1184_ = v___x_1180_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_fst_1173_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_fst_1177_);
v___x_1184_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
uint32_t v___x_1185_; lean_object* v___x_1186_; lean_object* v_fst_1187_; lean_object* v_snd_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1219_; 
v___x_1185_ = lean_unbox_uint32(v_a_1182_);
v___x_1186_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1163_, v_original_1164_, v___x_1185_, v___x_1184_);
v_fst_1187_ = lean_ctor_get(v___x_1186_, 0);
v_snd_1188_ = lean_ctor_get(v___x_1186_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1190_ = v___x_1186_;
v_isShared_1191_ = v_isSharedCheck_1219_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1188_);
lean_inc(v_fst_1187_);
lean_dec(v___x_1186_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1219_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v_snd_1178_);
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_fst_1187_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_snd_1178_);
v___x_1193_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
uint32_t v___x_1194_; lean_object* v___x_1195_; lean_object* v_fst_1196_; lean_object* v_snd_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1217_; 
v___x_1194_ = lean_unbox_uint32(v_a_1182_);
v___x_1195_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1165_, v_edited_1166_, v___x_1194_, v___x_1193_);
v_fst_1196_ = lean_ctor_get(v___x_1195_, 0);
v_snd_1197_ = lean_ctor_get(v___x_1195_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1199_ = v___x_1195_;
v_isShared_1200_ = v_isSharedCheck_1217_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_snd_1197_);
lean_inc(v_fst_1196_);
lean_dec(v___x_1195_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1217_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1201_ = 2;
v___x_1202_ = lean_box(v___x_1201_);
lean_inc(v_a_1182_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v_a_1182_);
lean_ctor_set(v___x_1199_, 0, v___x_1202_);
v___x_1204_ = v___x_1199_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_a_1182_);
v___x_1204_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1205_ = lean_array_push(v_fst_1196_, v___x_1204_);
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_add(v_snd_1188_, v___x_1206_);
lean_dec(v_snd_1188_);
v___x_1208_ = lean_nat_add(v_snd_1197_, v___x_1206_);
lean_dec(v_snd_1197_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1208_);
lean_ctor_set(v___x_1175_, 0, v___x_1207_);
v___x_1210_ = v___x_1175_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; 
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1205_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = ((size_t)1ULL);
v___x_1213_ = lean_usize_add(v_i_1169_, v___x_1212_);
v_i_1169_ = v___x_1213_;
v_b_1170_ = v___x_1211_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object* v___x_1223_, lean_object* v_original_1224_, lean_object* v___x_1225_, lean_object* v_edited_1226_, lean_object* v_as_1227_, lean_object* v_sz_1228_, lean_object* v_i_1229_, lean_object* v_b_1230_){
_start:
{
size_t v_sz_boxed_1231_; size_t v_i_boxed_1232_; lean_object* v_res_1233_; 
v_sz_boxed_1231_ = lean_unbox_usize(v_sz_1228_);
lean_dec(v_sz_1228_);
v_i_boxed_1232_ = lean_unbox_usize(v_i_1229_);
lean_dec(v_i_1229_);
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1223_, v_original_1224_, v___x_1225_, v_edited_1226_, v_as_1227_, v_sz_boxed_1231_, v_i_boxed_1232_, v_b_1230_);
lean_dec_ref(v_as_1227_);
lean_dec_ref(v_edited_1226_);
lean_dec(v___x_1225_);
lean_dec_ref(v_original_1224_);
lean_dec(v___x_1223_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(lean_object* v___x_1234_, lean_object* v_edited_1235_, lean_object* v___x_1236_, lean_object* v_original_1237_, lean_object* v_as_1238_, size_t v_sz_1239_, size_t v_i_1240_, lean_object* v_b_1241_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_usize_dec_lt(v_i_1240_, v_sz_1239_);
if (v___x_1242_ == 0)
{
return v_b_1241_;
}
else
{
lean_object* v_snd_1243_; lean_object* v_fst_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1293_; 
v_snd_1243_ = lean_ctor_get(v_b_1241_, 1);
v_fst_1244_ = lean_ctor_get(v_b_1241_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_b_1241_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1246_ = v_b_1241_;
v_isShared_1247_ = v_isSharedCheck_1293_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_snd_1243_);
lean_inc(v_fst_1244_);
lean_dec(v_b_1241_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1293_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_fst_1248_; lean_object* v_snd_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1292_; 
v_fst_1248_ = lean_ctor_get(v_snd_1243_, 0);
v_snd_1249_ = lean_ctor_get(v_snd_1243_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_snd_1243_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1251_ = v_snd_1243_;
v_isShared_1252_ = v_isSharedCheck_1292_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_snd_1249_);
lean_inc(v_fst_1248_);
lean_dec(v_snd_1243_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1292_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_a_1253_; lean_object* v___x_1255_; 
v_a_1253_ = lean_array_uget_borrowed(v_as_1238_, v_i_1240_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v_fst_1248_);
lean_ctor_set(v___x_1251_, 0, v_fst_1244_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_fst_1244_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_fst_1248_);
v___x_1255_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
uint32_t v___x_1256_; lean_object* v___x_1257_; lean_object* v_fst_1258_; lean_object* v_snd_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1290_; 
v___x_1256_ = lean_unbox_uint32(v_a_1253_);
v___x_1257_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1236_, v_original_1237_, v___x_1256_, v___x_1255_);
v_fst_1258_ = lean_ctor_get(v___x_1257_, 0);
v_snd_1259_ = lean_ctor_get(v___x_1257_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1261_ = v___x_1257_;
v_isShared_1262_ = v_isSharedCheck_1290_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_snd_1259_);
lean_inc(v_fst_1258_);
lean_dec(v___x_1257_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1290_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_snd_1249_);
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_fst_1258_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_snd_1249_);
v___x_1264_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
uint32_t v___x_1265_; lean_object* v___x_1266_; lean_object* v_fst_1267_; lean_object* v_snd_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1288_; 
v___x_1265_ = lean_unbox_uint32(v_a_1253_);
v___x_1266_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1234_, v_edited_1235_, v___x_1265_, v___x_1264_);
v_fst_1267_ = lean_ctor_get(v___x_1266_, 0);
v_snd_1268_ = lean_ctor_get(v___x_1266_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1270_ = v___x_1266_;
v_isShared_1271_ = v_isSharedCheck_1288_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_snd_1268_);
lean_inc(v_fst_1267_);
lean_dec(v___x_1266_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1288_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1272_ = 2;
v___x_1273_ = lean_box(v___x_1272_);
lean_inc(v_a_1253_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v_a_1253_);
lean_ctor_set(v___x_1270_, 0, v___x_1273_);
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_a_1253_);
v___x_1275_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1276_ = lean_array_push(v_fst_1267_, v___x_1275_);
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_nat_add(v_snd_1259_, v___x_1277_);
lean_dec(v_snd_1259_);
v___x_1279_ = lean_nat_add(v_snd_1268_, v___x_1277_);
lean_dec(v_snd_1268_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1279_);
lean_ctor_set(v___x_1246_, 0, v___x_1278_);
v___x_1281_ = v___x_1246_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1276_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = ((size_t)1ULL);
v___x_1284_ = lean_usize_add(v_i_1240_, v___x_1283_);
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1236_, v_original_1237_, v___x_1234_, v_edited_1235_, v_as_1238_, v_sz_1239_, v___x_1284_, v___x_1282_);
return v___x_1285_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object* v___x_1294_, lean_object* v_edited_1295_, lean_object* v___x_1296_, lean_object* v_original_1297_, lean_object* v_as_1298_, lean_object* v_sz_1299_, lean_object* v_i_1300_, lean_object* v_b_1301_){
_start:
{
size_t v_sz_boxed_1302_; size_t v_i_boxed_1303_; lean_object* v_res_1304_; 
v_sz_boxed_1302_ = lean_unbox_usize(v_sz_1299_);
lean_dec(v_sz_1299_);
v_i_boxed_1303_ = lean_unbox_usize(v_i_1300_);
lean_dec(v_i_1300_);
v_res_1304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1294_, v_edited_1295_, v___x_1296_, v_original_1297_, v_as_1298_, v_sz_boxed_1302_, v_i_boxed_1303_, v_b_1301_);
lean_dec_ref(v_as_1298_);
lean_dec_ref(v_original_1297_);
lean_dec(v___x_1296_);
lean_dec_ref(v_edited_1295_);
lean_dec(v___x_1294_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(lean_object* v_original_1312_, lean_object* v_edited_1313_){
_start:
{
lean_object* v_i_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_i_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = lean_array_get_size(v_original_1312_);
v___x_1316_ = lean_nat_dec_lt(v_i_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
size_t v_sz_1317_; size_t v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref(v_original_1312_);
v_sz_1317_ = lean_array_size(v_edited_1313_);
v___x_1318_ = ((size_t)0ULL);
v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_1317_, v___x_1318_, v_edited_1313_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = lean_array_get_size(v_edited_1313_);
v___x_1321_ = lean_nat_dec_lt(v_i_1314_, v___x_1320_);
if (v___x_1321_ == 0)
{
size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
lean_dec_ref(v_edited_1313_);
v_sz_1322_ = lean_array_size(v_original_1312_);
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1322_, v___x_1323_, v_original_1312_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v_ds_1327_; lean_object* v___x_1328_; size_t v_sz_1329_; size_t v___x_1330_; lean_object* v___x_1331_; lean_object* v_snd_1332_; lean_object* v_fst_1333_; lean_object* v_fst_1334_; lean_object* v_snd_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1354_; 
lean_inc_ref(v_original_1312_);
v___x_1325_ = l_Array_toSubarray___redArg(v_original_1312_, v_i_1314_, v___x_1315_);
lean_inc_ref(v_edited_1313_);
v___x_1326_ = l_Array_toSubarray___redArg(v_edited_1313_, v_i_1314_, v___x_1320_);
v_ds_1327_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1325_, v___x_1326_);
v___x_1328_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2));
v_sz_1329_ = lean_array_size(v_ds_1327_);
v___x_1330_ = ((size_t)0ULL);
v___x_1331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1320_, v_edited_1313_, v___x_1315_, v_original_1312_, v_ds_1327_, v_sz_1329_, v___x_1330_, v___x_1328_);
lean_dec_ref(v_ds_1327_);
v_snd_1332_ = lean_ctor_get(v___x_1331_, 1);
lean_inc(v_snd_1332_);
v_fst_1333_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_fst_1333_);
lean_dec_ref(v___x_1331_);
v_fst_1334_ = lean_ctor_get(v_snd_1332_, 0);
v_snd_1335_ = lean_ctor_get(v_snd_1332_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_snd_1332_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1337_ = v_snd_1332_;
v_isShared_1338_ = v_isSharedCheck_1354_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_snd_1335_);
lean_inc(v_fst_1334_);
lean_dec(v_snd_1332_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1354_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v_fst_1334_);
lean_ctor_set(v___x_1337_, 0, v_fst_1333_);
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_fst_1333_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_fst_1334_);
v___x_1340_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; lean_object* v_fst_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1351_; 
v___x_1341_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1315_, v_original_1312_, v___x_1340_);
lean_dec_ref(v_original_1312_);
v_fst_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; 
v_unused_1352_ = lean_ctor_get(v___x_1341_, 1);
lean_dec(v_unused_1352_);
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1351_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_fst_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1351_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v_snd_1335_);
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_fst_1342_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_snd_1335_);
v___x_1347_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; lean_object* v_fst_1349_; 
v___x_1348_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1320_, v_edited_1313_, v___x_1347_);
lean_dec_ref(v_edited_1313_);
v_fst_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_fst_1349_);
lean_dec_ref(v___x_1348_);
return v_fst_1349_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object* v_s_1355_, lean_object* v_a_1356_, uint8_t v_b_1357_){
_start:
{
lean_object* v_str_1358_; lean_object* v_startInclusive_1359_; lean_object* v_endExclusive_1360_; lean_object* v___x_1361_; uint8_t v_decide_1362_; 
v_str_1358_ = lean_ctor_get(v_s_1355_, 0);
v_startInclusive_1359_ = lean_ctor_get(v_s_1355_, 1);
v_endExclusive_1360_ = lean_ctor_get(v_s_1355_, 2);
v___x_1361_ = lean_nat_sub(v_endExclusive_1360_, v_startInclusive_1359_);
v_decide_1362_ = lean_nat_dec_eq(v_a_1356_, v___x_1361_);
lean_dec(v___x_1361_);
if (v_decide_1362_ == 0)
{
lean_object* v___x_1363_; uint32_t v___x_1364_; uint32_t v___x_1365_; uint8_t v___x_1366_; 
v___x_1363_ = lean_nat_add(v_startInclusive_1359_, v_a_1356_);
lean_dec(v_a_1356_);
v___x_1364_ = lean_string_utf8_get_fast(v_str_1358_, v___x_1363_);
v___x_1365_ = 10;
v___x_1366_ = lean_uint32_dec_eq(v___x_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_string_utf8_next_fast(v_str_1358_, v___x_1363_);
lean_dec(v___x_1363_);
v___x_1368_ = lean_nat_sub(v___x_1367_, v_startInclusive_1359_);
v_a_1356_ = v___x_1368_;
v_b_1357_ = v___x_1366_;
goto _start;
}
else
{
lean_dec(v___x_1363_);
return v___x_1366_;
}
}
else
{
lean_dec(v_a_1356_);
return v_b_1357_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object* v_s_1370_, lean_object* v_a_1371_, lean_object* v_b_1372_){
_start:
{
uint8_t v_b_boxed_1373_; uint8_t v_res_1374_; lean_object* v_r_1375_; 
v_b_boxed_1373_ = lean_unbox(v_b_1372_);
v_res_1374_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1370_, v_a_1371_, v_b_boxed_1373_);
lean_dec_ref(v_s_1370_);
v_r_1375_ = lean_box(v_res_1374_);
return v_r_1375_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object* v_s_1376_){
_start:
{
lean_object* v_searcher_1377_; uint8_t v___x_1378_; uint8_t v___x_1379_; 
v_searcher_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = 0;
v___x_1379_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1376_, v_searcher_1377_, v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object* v_s_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1380_);
lean_dec_ref(v_s_1380_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object* v_oldWs_1383_, lean_object* v_newWs_1384_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = lean_string_utf8_byte_size(v_oldWs_1383_);
lean_inc_ref(v_oldWs_1383_);
v___x_1387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1387_, 0, v_oldWs_1383_);
lean_ctor_set(v___x_1387_, 1, v___x_1385_);
lean_ctor_set(v___x_1387_, 2, v___x_1386_);
v___x_1388_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1387_);
lean_dec_ref_known(v___x_1387_, 3);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1389_ = lean_string_data(v_oldWs_1383_);
v___x_1390_ = lean_array_mk(v___x_1389_);
v___x_1391_ = lean_string_data(v_newWs_1384_);
v___x_1392_ = lean_array_mk(v___x_1391_);
v___x_1393_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1390_, v___x_1392_);
v___x_1394_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1393_);
lean_dec_ref(v___x_1393_);
return v___x_1394_;
}
else
{
uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v_oldWs_1383_);
v___x_1395_ = 2;
v___x_1396_ = lean_box(v___x_1395_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v_newWs_1384_);
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_mk_empty_array_with_capacity(v___x_1398_);
v___x_1400_ = lean_array_push(v___x_1399_, v___x_1397_);
return v___x_1400_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1401_, lean_object* v_inst_1402_, lean_object* v_R_1403_, lean_object* v_a_1404_, uint8_t v_b_1405_, lean_object* v_c_1406_){
_start:
{
uint8_t v___x_1407_; 
v___x_1407_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1401_, v_a_1404_, v_b_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1408_, lean_object* v_inst_1409_, lean_object* v_R_1410_, lean_object* v_a_1411_, lean_object* v_b_1412_, lean_object* v_c_1413_){
_start:
{
uint8_t v_b_boxed_1414_; uint8_t v_res_1415_; lean_object* v_r_1416_; 
v_b_boxed_1414_ = lean_unbox(v_b_1412_);
v_res_1415_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1408_, v_inst_1409_, v_R_1410_, v_a_1411_, v_b_boxed_1414_, v_c_1413_);
lean_dec_ref(v_s_1408_);
v_r_1416_ = lean_box(v_res_1415_);
return v_r_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object* v___x_1417_, lean_object* v_original_1418_, uint32_t v_a_1419_, lean_object* v_inst_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1417_, v_original_1418_, v_a_1419_, v_a_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___boxed(lean_object* v___x_1423_, lean_object* v_original_1424_, lean_object* v_a_1425_, lean_object* v_inst_1426_, lean_object* v_a_1427_){
_start:
{
uint32_t v_a_boxed_1428_; lean_object* v_res_1429_; 
v_a_boxed_1428_ = lean_unbox_uint32(v_a_1425_);
lean_dec(v_a_1425_);
v_res_1429_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1423_, v_original_1424_, v_a_boxed_1428_, v_inst_1426_, v_a_1427_);
lean_dec_ref(v_original_1424_);
lean_dec(v___x_1423_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v___x_1430_, lean_object* v_edited_1431_, uint32_t v_a_1432_, lean_object* v_inst_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1430_, v_edited_1431_, v_a_1432_, v_a_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v___x_1436_, lean_object* v_edited_1437_, lean_object* v_a_1438_, lean_object* v_inst_1439_, lean_object* v_a_1440_){
_start:
{
uint32_t v_a_boxed_1441_; lean_object* v_res_1442_; 
v_a_boxed_1441_ = lean_unbox_uint32(v_a_1438_);
lean_dec(v_a_1438_);
v_res_1442_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v___x_1436_, v_edited_1437_, v_a_boxed_1441_, v_inst_1439_, v_a_1440_);
lean_dec_ref(v_edited_1437_);
lean_dec(v___x_1436_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object* v___x_1443_, lean_object* v_original_1444_, lean_object* v_inst_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1443_, v_original_1444_, v_a_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object* v___x_1448_, lean_object* v_original_1449_, lean_object* v_inst_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1448_, v_original_1449_, v_inst_1450_, v_a_1451_);
lean_dec_ref(v_original_1449_);
lean_dec(v___x_1448_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object* v___x_1453_, lean_object* v_edited_1454_, lean_object* v_inst_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1453_, v_edited_1454_, v_a_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object* v___x_1458_, lean_object* v_edited_1459_, lean_object* v_inst_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1458_, v_edited_1459_, v_inst_1460_, v_a_1461_);
lean_dec_ref(v_edited_1459_);
lean_dec(v___x_1458_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(lean_object* v_as_1463_, lean_object* v_as_x27_1464_, lean_object* v_b_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_1464_, v_b_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___boxed(lean_object* v_as_1468_, lean_object* v_as_x27_1469_, lean_object* v_b_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(v_as_1468_, v_as_x27_1469_, v_b_1470_, v_a_1471_);
lean_dec(v_as_x27_1469_);
lean_dec(v_as_1468_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(lean_object* v_lsize_1473_, lean_object* v_rsize_1474_, lean_object* v_histogram_1475_, lean_object* v_index_1476_, uint32_t v_val_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_1475_, v_index_1476_, v_val_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___boxed(lean_object* v_lsize_1479_, lean_object* v_rsize_1480_, lean_object* v_histogram_1481_, lean_object* v_index_1482_, lean_object* v_val_1483_){
_start:
{
uint32_t v_val_boxed_1484_; lean_object* v_res_1485_; 
v_val_boxed_1484_ = lean_unbox_uint32(v_val_1483_);
lean_dec(v_val_1483_);
v_res_1485_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(v_lsize_1479_, v_rsize_1480_, v_histogram_1481_, v_index_1482_, v_val_boxed_1484_);
lean_dec(v_rsize_1480_);
lean_dec(v_lsize_1479_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(lean_object* v_upperBound_1486_, lean_object* v___x_1487_, lean_object* v_fst_1488_, lean_object* v___x_1489_, lean_object* v_inst_1490_, lean_object* v_R_1491_, lean_object* v_a_1492_, lean_object* v_b_1493_, lean_object* v_c_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_1486_, v___x_1487_, v_fst_1488_, v___x_1489_, v_a_1492_, v_b_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___boxed(lean_object* v_upperBound_1496_, lean_object* v___x_1497_, lean_object* v_fst_1498_, lean_object* v___x_1499_, lean_object* v_inst_1500_, lean_object* v_R_1501_, lean_object* v_a_1502_, lean_object* v_b_1503_, lean_object* v_c_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(v_upperBound_1496_, v___x_1497_, v_fst_1498_, v___x_1499_, v_inst_1500_, v_R_1501_, v_a_1502_, v_b_1503_, v_c_1504_);
lean_dec(v___x_1499_);
lean_dec_ref(v_fst_1498_);
lean_dec(v___x_1497_);
lean_dec(v_upperBound_1496_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(lean_object* v_lsize_1506_, lean_object* v_rsize_1507_, lean_object* v_histogram_1508_, lean_object* v_index_1509_, uint32_t v_val_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_1508_, v_index_1509_, v_val_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___boxed(lean_object* v_lsize_1512_, lean_object* v_rsize_1513_, lean_object* v_histogram_1514_, lean_object* v_index_1515_, lean_object* v_val_1516_){
_start:
{
uint32_t v_val_boxed_1517_; lean_object* v_res_1518_; 
v_val_boxed_1517_ = lean_unbox_uint32(v_val_1516_);
lean_dec(v_val_1516_);
v_res_1518_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(v_lsize_1512_, v_rsize_1513_, v_histogram_1514_, v_index_1515_, v_val_boxed_1517_);
lean_dec(v_rsize_1513_);
lean_dec(v_lsize_1512_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(lean_object* v_upperBound_1519_, lean_object* v_fst_1520_, lean_object* v___x_1521_, lean_object* v_fst_1522_, lean_object* v_inst_1523_, lean_object* v_R_1524_, lean_object* v_a_1525_, lean_object* v_b_1526_, lean_object* v_c_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_1519_, v_fst_1520_, v___x_1521_, v_fst_1522_, v_a_1525_, v_b_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___boxed(lean_object* v_upperBound_1529_, lean_object* v_fst_1530_, lean_object* v___x_1531_, lean_object* v_fst_1532_, lean_object* v_inst_1533_, lean_object* v_R_1534_, lean_object* v_a_1535_, lean_object* v_b_1536_, lean_object* v_c_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(v_upperBound_1529_, v_fst_1530_, v___x_1531_, v_fst_1532_, v_inst_1533_, v_R_1534_, v_a_1535_, v_b_1536_, v_c_1537_);
lean_dec_ref(v_fst_1532_);
lean_dec(v___x_1531_);
lean_dec_ref(v_fst_1530_);
lean_dec(v_upperBound_1529_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(lean_object* v_00_u03b2_1539_, lean_object* v_m_1540_, uint32_t v_a_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_1540_, v_a_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___boxed(lean_object* v_00_u03b2_1543_, lean_object* v_m_1544_, lean_object* v_a_1545_){
_start:
{
uint32_t v_a_boxed_1546_; lean_object* v_res_1547_; 
v_a_boxed_1546_ = lean_unbox_uint32(v_a_1545_);
lean_dec(v_a_1545_);
v_res_1547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(v_00_u03b2_1543_, v_m_1544_, v_a_boxed_1546_);
lean_dec_ref(v_m_1544_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(lean_object* v_00_u03b2_1548_, lean_object* v_m_1549_, uint32_t v_a_1550_, lean_object* v_b_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_1549_, v_a_1550_, v_b_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___boxed(lean_object* v_00_u03b2_1553_, lean_object* v_m_1554_, lean_object* v_a_1555_, lean_object* v_b_1556_){
_start:
{
uint32_t v_a_boxed_1557_; lean_object* v_res_1558_; 
v_a_boxed_1557_ = lean_unbox_uint32(v_a_1555_);
lean_dec(v_a_1555_);
v_res_1558_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(v_00_u03b2_1553_, v_m_1554_, v_a_boxed_1557_, v_b_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14(lean_object* v_inst_1559_, lean_object* v_R_1560_, lean_object* v_a_1561_, lean_object* v_b_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v_a_1561_, v_b_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(lean_object* v_00_u03b2_1564_, uint32_t v_a_1565_, lean_object* v_x_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_1565_, v_x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___boxed(lean_object* v_00_u03b2_1568_, lean_object* v_a_1569_, lean_object* v_x_1570_){
_start:
{
uint32_t v_a_boxed_1571_; lean_object* v_res_1572_; 
v_a_boxed_1571_ = lean_unbox_uint32(v_a_1569_);
lean_dec(v_a_1569_);
v_res_1572_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(v_00_u03b2_1568_, v_a_boxed_1571_, v_x_1570_);
lean_dec(v_x_1570_);
return v_res_1572_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(lean_object* v_00_u03b2_1573_, uint32_t v_a_1574_, lean_object* v_x_1575_){
_start:
{
uint8_t v___x_1576_; 
v___x_1576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_1574_, v_x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___boxed(lean_object* v_00_u03b2_1577_, lean_object* v_a_1578_, lean_object* v_x_1579_){
_start:
{
uint32_t v_a_boxed_1580_; uint8_t v_res_1581_; lean_object* v_r_1582_; 
v_a_boxed_1580_ = lean_unbox_uint32(v_a_1578_);
lean_dec(v_a_1578_);
v_res_1581_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(v_00_u03b2_1577_, v_a_boxed_1580_, v_x_1579_);
lean_dec(v_x_1579_);
v_r_1582_ = lean_box(v_res_1581_);
return v_r_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23(lean_object* v_00_u03b2_1583_, lean_object* v_data_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_data_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(lean_object* v_00_u03b2_1586_, uint32_t v_a_1587_, lean_object* v_b_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_1587_, v_b_1588_, v_x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___boxed(lean_object* v_00_u03b2_1591_, lean_object* v_a_1592_, lean_object* v_b_1593_, lean_object* v_x_1594_){
_start:
{
uint32_t v_a_boxed_1595_; lean_object* v_res_1596_; 
v_a_boxed_1595_ = lean_unbox_uint32(v_a_1592_);
lean_dec(v_a_1592_);
v_res_1596_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(v_00_u03b2_1591_, v_a_boxed_1595_, v_b_1593_, v_x_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_1597_, lean_object* v_i_1598_, lean_object* v_source_1599_, lean_object* v_target_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v_i_1598_, v_source_1599_, v_target_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1602_, lean_object* v_x_1603_, lean_object* v_x_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(v_x_1603_, v_x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1606_, lean_object* v_stopPos_1607_, lean_object* v_i_1608_){
_start:
{
uint8_t v___y_1610_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1613_ = lean_unsigned_to_nat(1u);
v___x_1614_ = lean_nat_add(v_i_1608_, v___x_1613_);
v___x_1615_ = lean_nat_dec_le(v___x_1614_, v_stopPos_1607_);
lean_dec(v___x_1614_);
if (v___x_1615_ == 0)
{
return v_i_1608_;
}
else
{
if (v___x_1615_ == 0)
{
v___y_1610_ = v___x_1615_;
goto v___jp_1609_;
}
else
{
uint32_t v___x_1616_; uint32_t v___x_1617_; uint8_t v___x_1618_; 
v___x_1616_ = lean_string_utf8_get(v_s_1606_, v_i_1608_);
v___x_1617_ = 32;
v___x_1618_ = lean_uint32_dec_eq(v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
uint32_t v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = 9;
v___x_1620_ = lean_uint32_dec_eq(v___x_1616_, v___x_1619_);
if (v___x_1620_ == 0)
{
uint32_t v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = 13;
v___x_1622_ = lean_uint32_dec_eq(v___x_1616_, v___x_1621_);
if (v___x_1622_ == 0)
{
uint32_t v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = 10;
v___x_1624_ = lean_uint32_dec_eq(v___x_1616_, v___x_1623_);
v___y_1610_ = v___x_1624_;
goto v___jp_1609_;
}
else
{
v___y_1610_ = v___x_1622_;
goto v___jp_1609_;
}
}
else
{
v___y_1610_ = v___x_1620_;
goto v___jp_1609_;
}
}
else
{
v___y_1610_ = v___x_1618_;
goto v___jp_1609_;
}
}
}
v___jp_1609_:
{
if (v___y_1610_ == 0)
{
return v_i_1608_;
}
else
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_string_utf8_next(v_s_1606_, v_i_1608_);
lean_dec(v_i_1608_);
v_i_1608_ = v___x_1611_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1625_, lean_object* v_stopPos_1626_, lean_object* v_i_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1625_, v_stopPos_1626_, v_i_1627_);
lean_dec(v_stopPos_1626_);
lean_dec_ref(v_s_1625_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1629_, lean_object* v_b_1630_, lean_object* v_i_1631_, lean_object* v_r_1632_, lean_object* v_ws_1633_){
_start:
{
uint8_t v___x_1642_; 
v___x_1642_ = lean_string_utf8_at_end(v_s_1629_, v_i_1631_);
if (v___x_1642_ == 0)
{
uint32_t v___x_1643_; uint32_t v___x_1644_; uint8_t v___x_1645_; 
v___x_1643_ = lean_string_utf8_get(v_s_1629_, v_i_1631_);
v___x_1644_ = 32;
v___x_1645_ = lean_uint32_dec_eq(v___x_1643_, v___x_1644_);
if (v___x_1645_ == 0)
{
uint32_t v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = 9;
v___x_1647_ = lean_uint32_dec_eq(v___x_1643_, v___x_1646_);
if (v___x_1647_ == 0)
{
uint32_t v___x_1648_; uint8_t v___x_1649_; 
v___x_1648_ = 13;
v___x_1649_ = lean_uint32_dec_eq(v___x_1643_, v___x_1648_);
if (v___x_1649_ == 0)
{
uint32_t v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = 10;
v___x_1651_ = lean_uint32_dec_eq(v___x_1643_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_string_utf8_next(v_s_1629_, v_i_1631_);
lean_dec(v_i_1631_);
v_i_1631_ = v___x_1652_;
goto _start;
}
else
{
goto v___jp_1634_;
}
}
else
{
goto v___jp_1634_;
}
}
else
{
goto v___jp_1634_;
}
}
else
{
goto v___jp_1634_;
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_string_utf8_extract(v_s_1629_, v_b_1630_, v_i_1631_);
lean_dec(v_i_1631_);
lean_dec(v_b_1630_);
v___x_1655_ = lean_array_push(v_r_1632_, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v_ws_1633_);
return v___x_1656_;
}
v___jp_1634_:
{
lean_object* v___x_1635_; lean_object* v_e_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1635_ = lean_string_utf8_byte_size(v_s_1629_);
lean_inc(v_i_1631_);
v_e_1636_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1629_, v___x_1635_, v_i_1631_);
v___x_1637_ = lean_string_utf8_extract(v_s_1629_, v_b_1630_, v_i_1631_);
lean_dec(v_b_1630_);
v___x_1638_ = lean_array_push(v_r_1632_, v___x_1637_);
v___x_1639_ = lean_string_utf8_extract(v_s_1629_, v_i_1631_, v_e_1636_);
lean_dec(v_i_1631_);
v___x_1640_ = lean_array_push(v_ws_1633_, v___x_1639_);
lean_inc(v_e_1636_);
v_b_1630_ = v_e_1636_;
v_i_1631_ = v_e_1636_;
v_r_1632_ = v___x_1638_;
v_ws_1633_ = v___x_1640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1657_, lean_object* v_b_1658_, lean_object* v_i_1659_, lean_object* v_r_1660_, lean_object* v_ws_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1657_, v_b_1658_, v_i_1659_, v_r_1660_, v_ws_1661_);
lean_dec_ref(v_s_1657_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = lean_unsigned_to_nat(0u);
v___x_1667_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1668_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1665_, v___x_1666_, v___x_1666_, v___x_1667_, v___x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1669_);
lean_dec_ref(v_s_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_1671_, size_t v_i_1672_, lean_object* v_bs_1673_){
_start:
{
uint8_t v___x_1674_; 
v___x_1674_ = lean_usize_dec_lt(v_i_1672_, v_sz_1671_);
if (v___x_1674_ == 0)
{
return v_bs_1673_;
}
else
{
lean_object* v_v_1675_; lean_object* v_fst_1676_; lean_object* v_snd_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1711_; 
v_v_1675_ = lean_array_uget(v_bs_1673_, v_i_1672_);
v_fst_1676_ = lean_ctor_get(v_v_1675_, 0);
v_snd_1677_ = lean_ctor_get(v_v_1675_, 1);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_v_1675_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1679_ = v_v_1675_;
v_isShared_1680_ = v_isSharedCheck_1711_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_snd_1677_);
lean_inc(v_fst_1676_);
lean_dec(v_v_1675_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1711_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v_bs_x27_1682_; lean_object* v___y_1684_; lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1681_ = lean_unsigned_to_nat(0u);
v_bs_x27_1682_ = lean_array_uset(v_bs_1673_, v_i_1672_, v___x_1681_);
v___x_1689_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1690_ = lean_array_get_size(v_snd_1677_);
v___x_1691_ = lean_nat_dec_lt(v___x_1681_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1693_; 
lean_dec(v_snd_1677_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v___x_1689_);
v___x_1693_ = v___x_1679_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_fst_1676_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1689_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
v___y_1684_ = v___x_1693_;
goto v___jp_1683_;
}
}
else
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_nat_dec_le(v___x_1690_, v___x_1690_);
if (v___x_1695_ == 0)
{
if (v___x_1691_ == 0)
{
lean_object* v___x_1697_; 
lean_dec(v_snd_1677_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v___x_1689_);
v___x_1697_ = v___x_1679_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_fst_1676_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v___x_1689_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
v___y_1684_ = v___x_1697_;
goto v___jp_1683_;
}
}
else
{
size_t v___x_1699_; size_t v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1699_ = ((size_t)0ULL);
v___x_1700_ = lean_usize_of_nat(v___x_1690_);
v___x_1701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1677_, v___x_1699_, v___x_1700_, v___x_1689_);
lean_dec(v_snd_1677_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v___x_1701_);
v___x_1703_ = v___x_1679_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_fst_1676_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
v___y_1684_ = v___x_1703_;
goto v___jp_1683_;
}
}
}
else
{
size_t v___x_1705_; size_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = lean_usize_of_nat(v___x_1690_);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1677_, v___x_1705_, v___x_1706_, v___x_1689_);
lean_dec(v_snd_1677_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v___x_1707_);
v___x_1709_ = v___x_1679_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_fst_1676_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
v___y_1684_ = v___x_1709_;
goto v___jp_1683_;
}
}
}
v___jp_1683_:
{
size_t v___x_1685_; size_t v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1672_, v___x_1685_);
v___x_1687_ = lean_array_uset(v_bs_x27_1682_, v_i_1672_, v___y_1684_);
v_i_1672_ = v___x_1686_;
v_bs_1673_ = v___x_1687_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_1712_, lean_object* v_i_1713_, lean_object* v_bs_1714_){
_start:
{
size_t v_sz_boxed_1715_; size_t v_i_boxed_1716_; lean_object* v_res_1717_; 
v_sz_boxed_1715_ = lean_unbox_usize(v_sz_1712_);
lean_dec(v_sz_1712_);
v_i_boxed_1716_ = lean_unbox_usize(v_i_1713_);
lean_dec(v_i_1713_);
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_1715_, v_i_boxed_1716_, v_bs_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1718_, size_t v_i_1719_, lean_object* v_bs_1720_){
_start:
{
uint8_t v___x_1721_; 
v___x_1721_ = lean_usize_dec_lt(v_i_1719_, v_sz_1718_);
if (v___x_1721_ == 0)
{
return v_bs_1720_;
}
else
{
lean_object* v_v_1722_; lean_object* v___x_1723_; lean_object* v_bs_x27_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; size_t v___x_1728_; size_t v___x_1729_; lean_object* v___x_1730_; 
v_v_1722_ = lean_array_uget(v_bs_1720_, v_i_1719_);
v___x_1723_ = lean_unsigned_to_nat(0u);
v_bs_x27_1724_ = lean_array_uset(v_bs_1720_, v_i_1719_, v___x_1723_);
v___x_1725_ = 0;
v___x_1726_ = lean_box(v___x_1725_);
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v_v_1722_);
v___x_1728_ = ((size_t)1ULL);
v___x_1729_ = lean_usize_add(v_i_1719_, v___x_1728_);
v___x_1730_ = lean_array_uset(v_bs_x27_1724_, v_i_1719_, v___x_1727_);
v_i_1719_ = v___x_1729_;
v_bs_1720_ = v___x_1730_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1732_, lean_object* v_i_1733_, lean_object* v_bs_1734_){
_start:
{
size_t v_sz_boxed_1735_; size_t v_i_boxed_1736_; lean_object* v_res_1737_; 
v_sz_boxed_1735_ = lean_unbox_usize(v_sz_1732_);
lean_dec(v_sz_1732_);
v_i_boxed_1736_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_res_1737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1735_, v_i_boxed_1736_, v_bs_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(lean_object* v_x_1738_, lean_object* v_x_1739_){
_start:
{
if (lean_obj_tag(v_x_1739_) == 0)
{
lean_inc(v_x_1738_);
return v_x_1738_;
}
else
{
lean_object* v_key_1740_; lean_object* v_value_1741_; lean_object* v_tail_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_key_1740_ = lean_ctor_get(v_x_1739_, 0);
v_value_1741_ = lean_ctor_get(v_x_1739_, 1);
v_tail_1742_ = lean_ctor_get(v_x_1739_, 2);
v___x_1743_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1738_, v_tail_1742_);
lean_inc(v_value_1741_);
lean_inc(v_key_1740_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v_key_1740_);
lean_ctor_set(v___x_1744_, 1, v_value_1741_);
v___x_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v___x_1743_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7___boxed(lean_object* v_x_1746_, lean_object* v_x_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1746_, v_x_1747_);
lean_dec(v_x_1747_);
lean_dec(v_x_1746_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(lean_object* v_as_1749_, size_t v_i_1750_, size_t v_stop_1751_, lean_object* v_b_1752_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_eq(v_i_1750_, v_stop_1751_);
if (v___x_1753_ == 0)
{
size_t v___x_1754_; size_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1754_ = ((size_t)1ULL);
v___x_1755_ = lean_usize_sub(v_i_1750_, v___x_1754_);
v___x_1756_ = lean_array_uget_borrowed(v_as_1749_, v___x_1755_);
v___x_1757_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_b_1752_, v___x_1756_);
lean_dec(v_b_1752_);
v_i_1750_ = v___x_1755_;
v_b_1752_ = v___x_1757_;
goto _start;
}
else
{
return v_b_1752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8___boxed(lean_object* v_as_1759_, lean_object* v_i_1760_, lean_object* v_stop_1761_, lean_object* v_b_1762_){
_start:
{
size_t v_i_boxed_1763_; size_t v_stop_boxed_1764_; lean_object* v_res_1765_; 
v_i_boxed_1763_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_stop_boxed_1764_ = lean_unbox_usize(v_stop_1761_);
lean_dec(v_stop_1761_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_as_1759_, v_i_boxed_1763_, v_stop_boxed_1764_, v_b_1762_);
lean_dec_ref(v_as_1759_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(lean_object* v_left_1766_, lean_object* v_right_1767_, lean_object* v_pref_1768_){
_start:
{
lean_object* v_start_1769_; lean_object* v_stop_1770_; lean_object* v_i_1771_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v_start_1769_ = lean_ctor_get(v_left_1766_, 1);
v_stop_1770_ = lean_ctor_get(v_left_1766_, 2);
v_i_1771_ = lean_array_get_size(v_pref_1768_);
v___x_1777_ = lean_nat_sub(v_stop_1770_, v_start_1769_);
v___x_1778_ = lean_nat_dec_lt(v_i_1771_, v___x_1777_);
lean_dec(v___x_1777_);
if (v___x_1778_ == 0)
{
goto v___jp_1772_;
}
else
{
lean_object* v_start_1779_; lean_object* v_stop_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_start_1779_ = lean_ctor_get(v_right_1767_, 1);
v_stop_1780_ = lean_ctor_get(v_right_1767_, 2);
v___x_1781_ = lean_nat_sub(v_stop_1780_, v_start_1779_);
v___x_1782_ = lean_nat_dec_lt(v_i_1771_, v___x_1781_);
lean_dec(v___x_1781_);
if (v___x_1782_ == 0)
{
goto v___jp_1772_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1783_ = l_Subarray_get___redArg(v_left_1766_, v_i_1771_);
v___x_1784_ = l_Subarray_get___redArg(v_right_1767_, v_i_1771_);
v___x_1785_ = lean_string_dec_eq(v___x_1783_, v___x_1784_);
lean_dec(v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec(v___x_1783_);
v___x_1786_ = l_Subarray_drop___redArg(v_left_1766_, v_i_1771_);
v___x_1787_ = l_Subarray_drop___redArg(v_right_1767_, v_i_1771_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_pref_1768_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_array_push(v_pref_1768_, v___x_1783_);
v_pref_1768_ = v___x_1790_;
goto _start;
}
}
}
v___jp_1772_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1773_ = l_Subarray_drop___redArg(v_left_1766_, v_i_1771_);
v___x_1774_ = l_Subarray_drop___redArg(v_right_1767_, v_i_1771_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_pref_1768_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
return v___x_1776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(lean_object* v_left_1792_, lean_object* v_right_1793_){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1795_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(v_left_1792_, v_right_1793_, v___x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(lean_object* v_a_1796_, lean_object* v_x_1797_){
_start:
{
if (lean_obj_tag(v_x_1797_) == 0)
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_box(0);
return v___x_1798_;
}
else
{
lean_object* v_key_1799_; lean_object* v_value_1800_; lean_object* v_tail_1801_; uint8_t v___x_1802_; 
v_key_1799_ = lean_ctor_get(v_x_1797_, 0);
v_value_1800_ = lean_ctor_get(v_x_1797_, 1);
v_tail_1801_ = lean_ctor_get(v_x_1797_, 2);
v___x_1802_ = lean_string_dec_eq(v_key_1799_, v_a_1796_);
if (v___x_1802_ == 0)
{
v_x_1797_ = v_tail_1801_;
goto _start;
}
else
{
lean_object* v___x_1804_; 
lean_inc(v_value_1800_);
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_value_1800_);
return v___x_1804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg___boxed(lean_object* v_a_1805_, lean_object* v_x_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1805_, v_x_1806_);
lean_dec(v_x_1806_);
lean_dec_ref(v_a_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_m_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_buckets_1810_; lean_object* v___x_1811_; uint64_t v___x_1812_; uint64_t v___x_1813_; uint64_t v___x_1814_; uint64_t v_fold_1815_; uint64_t v___x_1816_; uint64_t v___x_1817_; uint64_t v___x_1818_; size_t v___x_1819_; size_t v___x_1820_; size_t v___x_1821_; size_t v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_buckets_1810_ = lean_ctor_get(v_m_1808_, 1);
v___x_1811_ = lean_array_get_size(v_buckets_1810_);
v___x_1812_ = lean_string_hash(v_a_1809_);
v___x_1813_ = 32ULL;
v___x_1814_ = lean_uint64_shift_right(v___x_1812_, v___x_1813_);
v_fold_1815_ = lean_uint64_xor(v___x_1812_, v___x_1814_);
v___x_1816_ = 16ULL;
v___x_1817_ = lean_uint64_shift_right(v_fold_1815_, v___x_1816_);
v___x_1818_ = lean_uint64_xor(v_fold_1815_, v___x_1817_);
v___x_1819_ = lean_uint64_to_usize(v___x_1818_);
v___x_1820_ = lean_usize_of_nat(v___x_1811_);
v___x_1821_ = ((size_t)1ULL);
v___x_1822_ = lean_usize_sub(v___x_1820_, v___x_1821_);
v___x_1823_ = lean_usize_land(v___x_1819_, v___x_1822_);
v___x_1824_ = lean_array_uget_borrowed(v_buckets_1810_, v___x_1823_);
v___x_1825_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1809_, v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg___boxed(lean_object* v_m_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_1826_, v_a_1827_);
lean_dec_ref(v_a_1827_);
lean_dec_ref(v_m_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(lean_object* v_x_1829_, lean_object* v_x_1830_){
_start:
{
if (lean_obj_tag(v_x_1830_) == 0)
{
return v_x_1829_;
}
else
{
lean_object* v_key_1831_; lean_object* v_value_1832_; lean_object* v_tail_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1856_; 
v_key_1831_ = lean_ctor_get(v_x_1830_, 0);
v_value_1832_ = lean_ctor_get(v_x_1830_, 1);
v_tail_1833_ = lean_ctor_get(v_x_1830_, 2);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_x_1830_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1835_ = v_x_1830_;
v_isShared_1836_ = v_isSharedCheck_1856_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_tail_1833_);
lean_inc(v_value_1832_);
lean_inc(v_key_1831_);
lean_dec(v_x_1830_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1856_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; uint64_t v___x_1838_; uint64_t v___x_1839_; uint64_t v___x_1840_; uint64_t v_fold_1841_; uint64_t v___x_1842_; uint64_t v___x_1843_; uint64_t v___x_1844_; size_t v___x_1845_; size_t v___x_1846_; size_t v___x_1847_; size_t v___x_1848_; size_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1837_ = lean_array_get_size(v_x_1829_);
v___x_1838_ = lean_string_hash(v_key_1831_);
v___x_1839_ = 32ULL;
v___x_1840_ = lean_uint64_shift_right(v___x_1838_, v___x_1839_);
v_fold_1841_ = lean_uint64_xor(v___x_1838_, v___x_1840_);
v___x_1842_ = 16ULL;
v___x_1843_ = lean_uint64_shift_right(v_fold_1841_, v___x_1842_);
v___x_1844_ = lean_uint64_xor(v_fold_1841_, v___x_1843_);
v___x_1845_ = lean_uint64_to_usize(v___x_1844_);
v___x_1846_ = lean_usize_of_nat(v___x_1837_);
v___x_1847_ = ((size_t)1ULL);
v___x_1848_ = lean_usize_sub(v___x_1846_, v___x_1847_);
v___x_1849_ = lean_usize_land(v___x_1845_, v___x_1848_);
v___x_1850_ = lean_array_uget_borrowed(v_x_1829_, v___x_1849_);
lean_inc(v___x_1850_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 2, v___x_1850_);
v___x_1852_ = v___x_1835_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_key_1831_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_value_1832_);
lean_ctor_set(v_reuseFailAlloc_1855_, 2, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_array_uset(v_x_1829_, v___x_1849_, v___x_1852_);
v_x_1829_ = v___x_1853_;
v_x_1830_ = v_tail_1833_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(lean_object* v_i_1857_, lean_object* v_source_1858_, lean_object* v_target_1859_){
_start:
{
lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1860_ = lean_array_get_size(v_source_1858_);
v___x_1861_ = lean_nat_dec_lt(v_i_1857_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_dec_ref(v_source_1858_);
lean_dec(v_i_1857_);
return v_target_1859_;
}
else
{
lean_object* v_es_1862_; lean_object* v___x_1863_; lean_object* v_source_1864_; lean_object* v_target_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_es_1862_ = lean_array_fget(v_source_1858_, v_i_1857_);
v___x_1863_ = lean_box(0);
v_source_1864_ = lean_array_fset(v_source_1858_, v_i_1857_, v___x_1863_);
v_target_1865_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_target_1859_, v_es_1862_);
v___x_1866_ = lean_unsigned_to_nat(1u);
v___x_1867_ = lean_nat_add(v_i_1857_, v___x_1866_);
lean_dec(v_i_1857_);
v_i_1857_ = v___x_1867_;
v_source_1858_ = v_source_1864_;
v_target_1859_ = v_target_1865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(lean_object* v_data_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v_nbuckets_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1870_ = lean_array_get_size(v_data_1869_);
v___x_1871_ = lean_unsigned_to_nat(2u);
v_nbuckets_1872_ = lean_nat_mul(v___x_1870_, v___x_1871_);
v___x_1873_ = lean_unsigned_to_nat(0u);
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_mk_array(v_nbuckets_1872_, v___x_1874_);
v___x_1876_ = lean_array_propagate_mark(v_data_1869_, v___x_1875_);
v___x_1877_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v___x_1873_, v_data_1869_, v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(lean_object* v_a_1878_, lean_object* v_b_1879_, lean_object* v_x_1880_){
_start:
{
if (lean_obj_tag(v_x_1880_) == 0)
{
lean_dec(v_b_1879_);
lean_dec_ref(v_a_1878_);
return v_x_1880_;
}
else
{
lean_object* v_key_1881_; lean_object* v_value_1882_; lean_object* v_tail_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1895_; 
v_key_1881_ = lean_ctor_get(v_x_1880_, 0);
v_value_1882_ = lean_ctor_get(v_x_1880_, 1);
v_tail_1883_ = lean_ctor_get(v_x_1880_, 2);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_x_1880_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1885_ = v_x_1880_;
v_isShared_1886_ = v_isSharedCheck_1895_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_tail_1883_);
lean_inc(v_value_1882_);
lean_inc(v_key_1881_);
lean_dec(v_x_1880_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1895_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
uint8_t v___x_1887_; 
v___x_1887_ = lean_string_dec_eq(v_key_1881_, v_a_1878_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1878_, v_b_1879_, v_tail_1883_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 2, v___x_1888_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_key_1881_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_value_1882_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
else
{
lean_object* v___x_1893_; 
lean_dec(v_value_1882_);
lean_dec(v_key_1881_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v_b_1879_);
lean_ctor_set(v___x_1885_, 0, v_a_1878_);
v___x_1893_ = v___x_1885_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1878_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_b_1879_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_tail_1883_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(lean_object* v_a_1896_, lean_object* v_x_1897_){
_start:
{
if (lean_obj_tag(v_x_1897_) == 0)
{
uint8_t v___x_1898_; 
v___x_1898_ = 0;
return v___x_1898_;
}
else
{
lean_object* v_key_1899_; lean_object* v_tail_1900_; uint8_t v___x_1901_; 
v_key_1899_ = lean_ctor_get(v_x_1897_, 0);
v_tail_1900_ = lean_ctor_get(v_x_1897_, 2);
v___x_1901_ = lean_string_dec_eq(v_key_1899_, v_a_1896_);
if (v___x_1901_ == 0)
{
v_x_1897_ = v_tail_1900_;
goto _start;
}
else
{
return v___x_1901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg___boxed(lean_object* v_a_1903_, lean_object* v_x_1904_){
_start:
{
uint8_t v_res_1905_; lean_object* v_r_1906_; 
v_res_1905_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1903_, v_x_1904_);
lean_dec(v_x_1904_);
lean_dec_ref(v_a_1903_);
v_r_1906_ = lean_box(v_res_1905_);
return v_r_1906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(lean_object* v_m_1907_, lean_object* v_a_1908_, lean_object* v_b_1909_){
_start:
{
lean_object* v_size_1910_; lean_object* v_buckets_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1954_; 
v_size_1910_ = lean_ctor_get(v_m_1907_, 0);
v_buckets_1911_ = lean_ctor_get(v_m_1907_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_m_1907_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1913_ = v_m_1907_;
v_isShared_1914_ = v_isSharedCheck_1954_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_buckets_1911_);
lean_inc(v_size_1910_);
lean_dec(v_m_1907_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1954_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; uint64_t v___x_1916_; uint64_t v___x_1917_; uint64_t v___x_1918_; uint64_t v_fold_1919_; uint64_t v___x_1920_; uint64_t v___x_1921_; uint64_t v___x_1922_; size_t v___x_1923_; size_t v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; lean_object* v_bkt_1928_; uint8_t v___x_1929_; 
v___x_1915_ = lean_array_get_size(v_buckets_1911_);
v___x_1916_ = lean_string_hash(v_a_1908_);
v___x_1917_ = 32ULL;
v___x_1918_ = lean_uint64_shift_right(v___x_1916_, v___x_1917_);
v_fold_1919_ = lean_uint64_xor(v___x_1916_, v___x_1918_);
v___x_1920_ = 16ULL;
v___x_1921_ = lean_uint64_shift_right(v_fold_1919_, v___x_1920_);
v___x_1922_ = lean_uint64_xor(v_fold_1919_, v___x_1921_);
v___x_1923_ = lean_uint64_to_usize(v___x_1922_);
v___x_1924_ = lean_usize_of_nat(v___x_1915_);
v___x_1925_ = ((size_t)1ULL);
v___x_1926_ = lean_usize_sub(v___x_1924_, v___x_1925_);
v___x_1927_ = lean_usize_land(v___x_1923_, v___x_1926_);
v_bkt_1928_ = lean_array_uget_borrowed(v_buckets_1911_, v___x_1927_);
v___x_1929_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1908_, v_bkt_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; lean_object* v_size_x27_1931_; lean_object* v___x_1932_; lean_object* v_buckets_x27_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1930_ = lean_unsigned_to_nat(1u);
v_size_x27_1931_ = lean_nat_add(v_size_1910_, v___x_1930_);
lean_dec(v_size_1910_);
lean_inc(v_bkt_1928_);
v___x_1932_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1932_, 0, v_a_1908_);
lean_ctor_set(v___x_1932_, 1, v_b_1909_);
lean_ctor_set(v___x_1932_, 2, v_bkt_1928_);
v_buckets_x27_1933_ = lean_array_uset(v_buckets_1911_, v___x_1927_, v___x_1932_);
v___x_1934_ = lean_unsigned_to_nat(4u);
v___x_1935_ = lean_nat_mul(v_size_x27_1931_, v___x_1934_);
v___x_1936_ = lean_unsigned_to_nat(3u);
v___x_1937_ = lean_nat_div(v___x_1935_, v___x_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_array_get_size(v_buckets_x27_1933_);
v___x_1939_ = lean_nat_dec_le(v___x_1937_, v___x_1938_);
lean_dec(v___x_1937_);
if (v___x_1939_ == 0)
{
lean_object* v_val_1940_; lean_object* v___x_1942_; 
v_val_1940_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_buckets_x27_1933_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v_val_1940_);
lean_ctor_set(v___x_1913_, 0, v_size_x27_1931_);
v___x_1942_ = v___x_1913_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_size_x27_1931_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_val_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
else
{
lean_object* v___x_1945_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v_buckets_x27_1933_);
lean_ctor_set(v___x_1913_, 0, v_size_x27_1931_);
v___x_1945_ = v___x_1913_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_size_x27_1931_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_buckets_x27_1933_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_object* v___x_1947_; lean_object* v_buckets_x27_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
lean_inc(v_bkt_1928_);
v___x_1947_ = lean_box(0);
v_buckets_x27_1948_ = lean_array_uset(v_buckets_1911_, v___x_1927_, v___x_1947_);
v___x_1949_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1908_, v_b_1909_, v_bkt_1928_);
v___x_1950_ = lean_array_uset(v_buckets_x27_1948_, v___x_1927_, v___x_1949_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v___x_1950_);
v___x_1952_ = v___x_1913_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_size_1910_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(lean_object* v_histogram_1955_, lean_object* v_index_1956_, lean_object* v_val_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_1955_, v_val_1957_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_box(0);
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1962_, 0, v_index_1956_);
v___x_1963_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1959_);
lean_ctor_set(v___x_1963_, 1, v___x_1960_);
lean_ctor_set(v___x_1963_, 2, v___x_1961_);
lean_ctor_set(v___x_1963_, 3, v___x_1962_);
v___x_1964_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1955_, v_val_1957_, v___x_1963_);
return v___x_1964_;
}
else
{
lean_object* v_val_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1986_; 
v_val_1965_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1967_ = v___x_1958_;
v_isShared_1968_ = v_isSharedCheck_1986_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_val_1965_);
lean_dec(v___x_1958_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1986_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_leftCount_1969_; lean_object* v_leftIndex_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1983_; 
v_leftCount_1969_ = lean_ctor_get(v_val_1965_, 0);
v_leftIndex_1970_ = lean_ctor_get(v_val_1965_, 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_val_1965_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; lean_object* v_unused_1985_; 
v_unused_1984_ = lean_ctor_get(v_val_1965_, 3);
lean_dec(v_unused_1984_);
v_unused_1985_ = lean_ctor_get(v_val_1965_, 2);
lean_dec(v_unused_1985_);
v___x_1972_ = v_val_1965_;
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_leftIndex_1970_);
lean_inc(v_leftCount_1969_);
lean_dec(v_val_1965_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1983_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = lean_nat_add(v_leftCount_1969_, v___x_1974_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v_index_1956_);
v___x_1977_ = v___x_1967_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_index_1956_);
v___x_1977_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1979_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 3, v___x_1977_);
lean_ctor_set(v___x_1972_, 2, v___x_1975_);
v___x_1979_ = v___x_1972_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_leftCount_1969_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_leftIndex_1970_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1955_, v_val_1957_, v___x_1979_);
return v___x_1980_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(lean_object* v_upperBound_1987_, lean_object* v___x_1988_, lean_object* v_fst_1989_, lean_object* v___x_1990_, lean_object* v_a_1991_, lean_object* v_b_1992_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_nat_dec_lt(v_a_1991_, v_upperBound_1987_);
if (v___x_1993_ == 0)
{
lean_dec(v_a_1991_);
return v_b_1992_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1994_ = l_Subarray_get___redArg(v_fst_1989_, v_a_1991_);
lean_inc(v_a_1991_);
v___x_1995_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_b_1992_, v_a_1991_, v___x_1994_);
v___x_1996_ = lean_unsigned_to_nat(1u);
v___x_1997_ = lean_nat_add(v_a_1991_, v___x_1996_);
lean_dec(v_a_1991_);
v_a_1991_ = v___x_1997_;
v_b_1992_ = v___x_1995_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_upperBound_1999_, lean_object* v___x_2000_, lean_object* v_fst_2001_, lean_object* v___x_2002_, lean_object* v_a_2003_, lean_object* v_b_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_1999_, v___x_2000_, v_fst_2001_, v___x_2002_, v_a_2003_, v_b_2004_);
lean_dec(v___x_2002_);
lean_dec_ref(v_fst_2001_);
lean_dec(v___x_2000_);
lean_dec(v_upperBound_1999_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(lean_object* v_as_x27_2006_, lean_object* v_b_2007_){
_start:
{
if (lean_obj_tag(v_as_x27_2006_) == 0)
{
return v_b_2007_;
}
else
{
lean_object* v_head_2008_; lean_object* v_snd_2009_; lean_object* v_leftIndex_2010_; 
v_head_2008_ = lean_ctor_get(v_as_x27_2006_, 0);
v_snd_2009_ = lean_ctor_get(v_head_2008_, 1);
v_leftIndex_2010_ = lean_ctor_get(v_snd_2009_, 1);
if (lean_obj_tag(v_leftIndex_2010_) == 1)
{
lean_object* v_rightIndex_2011_; 
v_rightIndex_2011_ = lean_ctor_get(v_snd_2009_, 3);
if (lean_obj_tag(v_rightIndex_2011_) == 1)
{
if (lean_obj_tag(v_b_2007_) == 0)
{
lean_object* v_tail_2012_; lean_object* v_fst_2013_; lean_object* v_leftCount_2014_; lean_object* v_rightCount_2015_; lean_object* v_val_2016_; lean_object* v_val_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v_tail_2012_ = lean_ctor_get(v_as_x27_2006_, 1);
v_fst_2013_ = lean_ctor_get(v_head_2008_, 0);
v_leftCount_2014_ = lean_ctor_get(v_snd_2009_, 0);
v_rightCount_2015_ = lean_ctor_get(v_snd_2009_, 2);
v_val_2016_ = lean_ctor_get(v_leftIndex_2010_, 0);
v_val_2017_ = lean_ctor_get(v_rightIndex_2011_, 0);
v___x_2018_ = lean_nat_add(v_leftCount_2014_, v_rightCount_2015_);
lean_inc(v_val_2017_);
lean_inc(v_val_2016_);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v_val_2016_);
lean_ctor_set(v___x_2019_, 1, v_val_2017_);
lean_inc(v_fst_2013_);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v_fst_2013_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2018_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
v_as_x27_2006_ = v_tail_2012_;
v_b_2007_ = v___x_2022_;
goto _start;
}
else
{
lean_object* v_val_2024_; lean_object* v_tail_2025_; lean_object* v_fst_2026_; lean_object* v_leftCount_2027_; lean_object* v_rightCount_2028_; lean_object* v_val_2029_; lean_object* v_val_2030_; lean_object* v_fst_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2052_; 
v_val_2024_ = lean_ctor_get(v_b_2007_, 0);
lean_inc(v_val_2024_);
v_tail_2025_ = lean_ctor_get(v_as_x27_2006_, 1);
v_fst_2026_ = lean_ctor_get(v_head_2008_, 0);
v_leftCount_2027_ = lean_ctor_get(v_snd_2009_, 0);
v_rightCount_2028_ = lean_ctor_get(v_snd_2009_, 2);
v_val_2029_ = lean_ctor_get(v_leftIndex_2010_, 0);
v_val_2030_ = lean_ctor_get(v_rightIndex_2011_, 0);
v_fst_2031_ = lean_ctor_get(v_val_2024_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_val_2024_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v_val_2024_, 1);
lean_dec(v_unused_2053_);
v___x_2033_ = v_val_2024_;
v_isShared_2034_ = v_isSharedCheck_2052_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_fst_2031_);
lean_dec(v_val_2024_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2052_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = lean_nat_add(v_leftCount_2027_, v_rightCount_2028_);
v___x_2036_ = lean_nat_dec_lt(v___x_2035_, v_fst_2031_);
lean_dec(v_fst_2031_);
if (v___x_2036_ == 0)
{
lean_dec(v___x_2035_);
lean_del_object(v___x_2033_);
v_as_x27_2006_ = v_tail_2025_;
goto _start;
}
else
{
lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2050_; 
v_isSharedCheck_2050_ = !lean_is_exclusive(v_b_2007_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v_b_2007_, 0);
lean_dec(v_unused_2051_);
v___x_2039_ = v_b_2007_;
v_isShared_2040_ = v_isSharedCheck_2050_;
goto v_resetjp_2038_;
}
else
{
lean_dec(v_b_2007_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2050_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
lean_inc(v_val_2030_);
lean_inc(v_val_2029_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v_val_2030_);
lean_ctor_set(v___x_2033_, 0, v_val_2029_);
v___x_2042_ = v___x_2033_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_val_2029_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_val_2030_);
v___x_2042_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
lean_inc(v_fst_2026_);
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v_fst_2026_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2035_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2044_);
v___x_2046_ = v___x_2039_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
v_as_x27_2006_ = v_tail_2025_;
v_b_2007_ = v___x_2046_;
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
lean_object* v_tail_2054_; 
v_tail_2054_ = lean_ctor_get(v_as_x27_2006_, 1);
v_as_x27_2006_ = v_tail_2054_;
goto _start;
}
}
else
{
lean_object* v_tail_2056_; 
v_tail_2056_ = lean_ctor_get(v_as_x27_2006_, 1);
v_as_x27_2006_ = v_tail_2056_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_x27_2058_, lean_object* v_b_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2058_, v_b_2059_);
lean_dec(v_as_x27_2058_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(lean_object* v_a_2061_, lean_object* v_b_2062_){
_start:
{
lean_object* v_array_2063_; lean_object* v_start_2064_; lean_object* v_stop_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2078_; 
v_array_2063_ = lean_ctor_get(v_a_2061_, 0);
v_start_2064_ = lean_ctor_get(v_a_2061_, 1);
v_stop_2065_ = lean_ctor_get(v_a_2061_, 2);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_a_2061_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2067_ = v_a_2061_;
v_isShared_2068_ = v_isSharedCheck_2078_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_stop_2065_);
lean_inc(v_start_2064_);
lean_inc(v_array_2063_);
lean_dec(v_a_2061_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2078_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
uint8_t v___x_2069_; 
v___x_2069_ = lean_nat_dec_lt(v_start_2064_, v_stop_2065_);
if (v___x_2069_ == 0)
{
lean_del_object(v___x_2067_);
lean_dec(v_stop_2065_);
lean_dec(v_start_2064_);
lean_dec_ref(v_array_2063_);
return v_b_2062_;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2070_ = lean_unsigned_to_nat(1u);
v___x_2071_ = lean_nat_add(v_start_2064_, v___x_2070_);
lean_inc_ref(v_array_2063_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2071_);
v___x_2073_ = v___x_2067_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_array_2063_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_stop_2065_);
v___x_2073_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_array_fget(v_array_2063_, v_start_2064_);
lean_dec(v_start_2064_);
lean_dec_ref(v_array_2063_);
v___x_2075_ = lean_array_push(v_b_2062_, v___x_2074_);
v_a_2061_ = v___x_2073_;
v_b_2062_ = v___x_2075_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(lean_object* v_left_2079_, lean_object* v_right_2080_, lean_object* v_i_2081_){
_start:
{
lean_object* v_start_2082_; lean_object* v_stop_2083_; lean_object* v___x_2084_; uint8_t v___x_2098_; 
v_start_2082_ = lean_ctor_get(v_left_2079_, 1);
v_stop_2083_ = lean_ctor_get(v_left_2079_, 2);
v___x_2084_ = lean_nat_sub(v_stop_2083_, v_start_2082_);
v___x_2098_ = lean_nat_dec_lt(v_i_2081_, v___x_2084_);
if (v___x_2098_ == 0)
{
goto v___jp_2085_;
}
else
{
lean_object* v_start_2099_; lean_object* v_stop_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v_start_2099_ = lean_ctor_get(v_right_2080_, 1);
v_stop_2100_ = lean_ctor_get(v_right_2080_, 2);
v___x_2101_ = lean_nat_sub(v_stop_2100_, v_start_2099_);
v___x_2102_ = lean_nat_dec_lt(v_i_2081_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_dec(v___x_2101_);
goto v___jp_2085_;
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2103_ = lean_nat_sub(v___x_2084_, v_i_2081_);
lean_dec(v___x_2084_);
v___x_2104_ = lean_unsigned_to_nat(1u);
v___x_2105_ = lean_nat_sub(v___x_2103_, v___x_2104_);
v___x_2106_ = l_Subarray_get___redArg(v_left_2079_, v___x_2105_);
lean_dec(v___x_2105_);
v___x_2107_ = lean_nat_sub(v___x_2101_, v_i_2081_);
lean_dec(v___x_2101_);
v___x_2108_ = lean_nat_sub(v___x_2107_, v___x_2104_);
v___x_2109_ = l_Subarray_get___redArg(v_right_2080_, v___x_2108_);
lean_dec(v___x_2108_);
v___x_2110_ = lean_string_dec_eq(v___x_2106_, v___x_2109_);
lean_dec(v___x_2109_);
lean_dec(v___x_2106_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec(v_i_2081_);
lean_inc_ref(v_left_2079_);
v___x_2111_ = l_Subarray_take___redArg(v_left_2079_, v___x_2103_);
v___x_2112_ = l_Subarray_take___redArg(v_right_2080_, v___x_2107_);
lean_dec(v___x_2107_);
v___x_2113_ = l_Subarray_drop___redArg(v_left_2079_, v___x_2103_);
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
v___x_2118_ = lean_nat_add(v_i_2081_, v___x_2104_);
lean_dec(v_i_2081_);
v_i_2081_ = v___x_2118_;
goto _start;
}
}
}
v___jp_2085_:
{
lean_object* v_start_2086_; lean_object* v_stop_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_start_2086_ = lean_ctor_get(v_right_2080_, 1);
v_stop_2087_ = lean_ctor_get(v_right_2080_, 2);
v___x_2088_ = lean_nat_sub(v___x_2084_, v_i_2081_);
lean_dec(v___x_2084_);
lean_inc_ref(v_left_2079_);
v___x_2089_ = l_Subarray_take___redArg(v_left_2079_, v___x_2088_);
v___x_2090_ = lean_nat_sub(v_stop_2087_, v_start_2086_);
v___x_2091_ = lean_nat_sub(v___x_2090_, v_i_2081_);
lean_dec(v_i_2081_);
lean_dec(v___x_2090_);
v___x_2092_ = l_Subarray_take___redArg(v_right_2080_, v___x_2091_);
lean_dec(v___x_2091_);
v___x_2093_ = l_Subarray_drop___redArg(v_left_2079_, v___x_2088_);
lean_dec(v___x_2088_);
v___x_2094_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2095_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v___x_2093_, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2092_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2089_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(lean_object* v_left_2120_, lean_object* v_right_2121_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(v_left_2120_, v_right_2121_, v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(lean_object* v_histogram_2124_, lean_object* v_index_2125_, lean_object* v_val_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_2124_, v_val_2126_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2128_ = lean_unsigned_to_nat(1u);
v___x_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2129_, 0, v_index_2125_);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = lean_box(0);
v___x_2132_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2128_);
lean_ctor_set(v___x_2132_, 1, v___x_2129_);
lean_ctor_set(v___x_2132_, 2, v___x_2130_);
lean_ctor_set(v___x_2132_, 3, v___x_2131_);
v___x_2133_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2124_, v_val_2126_, v___x_2132_);
return v___x_2133_;
}
else
{
lean_object* v_val_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2155_; 
v_val_2134_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2136_ = v___x_2127_;
v_isShared_2137_ = v_isSharedCheck_2155_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_val_2134_);
lean_dec(v___x_2127_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2155_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_leftCount_2138_; lean_object* v_rightCount_2139_; lean_object* v_rightIndex_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2153_; 
v_leftCount_2138_ = lean_ctor_get(v_val_2134_, 0);
v_rightCount_2139_ = lean_ctor_get(v_val_2134_, 2);
v_rightIndex_2140_ = lean_ctor_get(v_val_2134_, 3);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_val_2134_);
if (v_isSharedCheck_2153_ == 0)
{
lean_object* v_unused_2154_; 
v_unused_2154_ = lean_ctor_get(v_val_2134_, 1);
lean_dec(v_unused_2154_);
v___x_2142_ = v_val_2134_;
v_isShared_2143_ = v_isSharedCheck_2153_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_rightIndex_2140_);
lean_inc(v_rightCount_2139_);
lean_inc(v_leftCount_2138_);
lean_dec(v_val_2134_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2153_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2144_ = lean_unsigned_to_nat(1u);
v___x_2145_ = lean_nat_add(v_leftCount_2138_, v___x_2144_);
lean_dec(v_leftCount_2138_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v_index_2125_);
v___x_2147_ = v___x_2136_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_index_2125_);
v___x_2147_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2149_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 1, v___x_2147_);
lean_ctor_set(v___x_2142_, 0, v___x_2145_);
v___x_2149_ = v___x_2142_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v_rightCount_2139_);
lean_ctor_set(v_reuseFailAlloc_2151_, 3, v_rightIndex_2140_);
v___x_2149_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2124_, v_val_2126_, v___x_2149_);
return v___x_2150_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(lean_object* v_upperBound_2156_, lean_object* v_fst_2157_, lean_object* v___x_2158_, lean_object* v_fst_2159_, lean_object* v_a_2160_, lean_object* v_b_2161_){
_start:
{
uint8_t v___x_2162_; 
v___x_2162_ = lean_nat_dec_lt(v_a_2160_, v_upperBound_2156_);
if (v___x_2162_ == 0)
{
lean_dec(v_a_2160_);
return v_b_2161_;
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2163_ = l_Subarray_get___redArg(v_fst_2159_, v_a_2160_);
lean_inc(v_a_2160_);
v___x_2164_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_b_2161_, v_a_2160_, v___x_2163_);
v___x_2165_ = lean_unsigned_to_nat(1u);
v___x_2166_ = lean_nat_add(v_a_2160_, v___x_2165_);
lean_dec(v_a_2160_);
v_a_2160_ = v___x_2166_;
v_b_2161_ = v___x_2164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg___boxed(lean_object* v_upperBound_2168_, lean_object* v_fst_2169_, lean_object* v___x_2170_, lean_object* v_fst_2171_, lean_object* v_a_2172_, lean_object* v_b_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2168_, v_fst_2169_, v___x_2170_, v_fst_2171_, v_a_2172_, v_b_2173_);
lean_dec_ref(v_fst_2171_);
lean_dec(v___x_2170_);
lean_dec_ref(v_fst_2169_);
lean_dec(v_upperBound_2168_);
return v_res_2174_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = lean_box(0);
v___x_2176_ = lean_unsigned_to_nat(16u);
v___x_2177_ = lean_mk_array(v___x_2176_, v___x_2175_);
return v___x_2177_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v_hist_2180_; 
v___x_2178_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0);
v___x_2179_ = lean_unsigned_to_nat(0u);
v_hist_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2180_, 0, v___x_2179_);
lean_ctor_set(v_hist_2180_, 1, v___x_2178_);
return v_hist_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_left_2181_, lean_object* v_right_2182_){
_start:
{
lean_object* v___x_2183_; lean_object* v_snd_2184_; lean_object* v_fst_2185_; lean_object* v_fst_2186_; lean_object* v_snd_2187_; lean_object* v___x_2188_; lean_object* v_snd_2189_; lean_object* v_fst_2190_; lean_object* v_fst_2191_; lean_object* v_snd_2192_; lean_object* v_start_2193_; lean_object* v_stop_2194_; lean_object* v___x_2195_; lean_object* v_hist_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v_start_2199_; lean_object* v_stop_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_buckets_2203_; lean_object* v___x_2204_; lean_object* v___y_2206_; lean_object* v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2183_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(v_left_2181_, v_right_2182_);
v_snd_2184_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_snd_2184_);
v_fst_2185_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_fst_2185_);
lean_dec_ref(v___x_2183_);
v_fst_2186_ = lean_ctor_get(v_snd_2184_, 0);
lean_inc(v_fst_2186_);
v_snd_2187_ = lean_ctor_get(v_snd_2184_, 1);
lean_inc(v_snd_2187_);
lean_dec(v_snd_2184_);
v___x_2188_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(v_fst_2186_, v_snd_2187_);
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
v_start_2193_ = lean_ctor_get(v_fst_2190_, 1);
v_stop_2194_ = lean_ctor_get(v_fst_2190_, 2);
v___x_2195_ = lean_unsigned_to_nat(0u);
v_hist_2196_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1);
v___x_2197_ = lean_nat_sub(v_stop_2194_, v_start_2193_);
v___x_2198_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v___x_2197_, v_fst_2191_, v___x_2197_, v_fst_2190_, v___x_2195_, v_hist_2196_);
v_start_2199_ = lean_ctor_get(v_fst_2191_, 1);
v_stop_2200_ = lean_ctor_get(v_fst_2191_, 2);
v___x_2201_ = lean_nat_sub(v_stop_2200_, v_start_2199_);
v___x_2202_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v___x_2201_, v___x_2201_, v_fst_2191_, v___x_2197_, v___x_2195_, v___x_2198_);
lean_dec(v___x_2197_);
lean_dec(v___x_2201_);
v_buckets_2203_ = lean_ctor_get(v___x_2202_, 1);
lean_inc_ref(v_buckets_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = lean_box(0);
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_array_get_size(v_buckets_2203_);
v___x_2234_ = lean_nat_dec_lt(v___x_2195_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_dec_ref(v_buckets_2203_);
v___y_2206_ = v___x_2232_;
goto v___jp_2205_;
}
else
{
size_t v___x_2235_; size_t v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = lean_usize_of_nat(v___x_2233_);
v___x_2236_ = ((size_t)0ULL);
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_buckets_2203_, v___x_2235_, v___x_2236_, v___x_2232_);
lean_dec_ref(v_buckets_2203_);
v___y_2206_ = v___x_2237_;
goto v___jp_2205_;
}
v___jp_2205_:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v___y_2206_, v___x_2204_);
lean_dec(v___y_2206_);
if (lean_obj_tag(v___x_2207_) == 1)
{
lean_object* v_val_2208_; lean_object* v_snd_2209_; lean_object* v_snd_2210_; lean_object* v_fst_2211_; lean_object* v_fst_2212_; lean_object* v_snd_2213_; lean_object* v___x_2214_; lean_object* v_fst_2215_; lean_object* v_snd_2216_; lean_object* v___x_2217_; lean_object* v_fst_2218_; lean_object* v_snd_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v_val_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_val_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v_snd_2209_ = lean_ctor_get(v_val_2208_, 1);
lean_inc(v_snd_2209_);
lean_dec(v_val_2208_);
v_snd_2210_ = lean_ctor_get(v_snd_2209_, 1);
lean_inc(v_snd_2210_);
v_fst_2211_ = lean_ctor_get(v_snd_2209_, 0);
lean_inc(v_fst_2211_);
lean_dec(v_snd_2209_);
v_fst_2212_ = lean_ctor_get(v_snd_2210_, 0);
lean_inc(v_fst_2212_);
v_snd_2213_ = lean_ctor_get(v_snd_2210_, 1);
lean_inc(v_snd_2213_);
lean_dec(v_snd_2210_);
v___x_2214_ = l_Subarray_split___redArg(v_fst_2190_, v_fst_2212_);
lean_dec(v_fst_2212_);
v_fst_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_fst_2215_);
v_snd_2216_ = lean_ctor_get(v___x_2214_, 1);
lean_inc(v_snd_2216_);
lean_dec_ref(v___x_2214_);
v___x_2217_ = l_Subarray_split___redArg(v_fst_2191_, v_snd_2213_);
lean_dec(v_snd_2213_);
v_fst_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_fst_2218_);
v_snd_2219_ = lean_ctor_get(v___x_2217_, 1);
lean_inc(v_snd_2219_);
lean_dec_ref(v___x_2217_);
v___x_2220_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_fst_2215_, v_fst_2218_);
v___x_2221_ = l_Array_append___redArg(v_fst_2185_, v___x_2220_);
lean_dec_ref(v___x_2220_);
v___x_2222_ = lean_unsigned_to_nat(1u);
v___x_2223_ = lean_mk_empty_array_with_capacity(v___x_2222_);
v___x_2224_ = lean_array_push(v___x_2223_, v_fst_2211_);
v___x_2225_ = l_Array_append___redArg(v___x_2221_, v___x_2224_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = l_Subarray_drop___redArg(v_snd_2216_, v___x_2222_);
v___x_2227_ = l_Subarray_drop___redArg(v_snd_2219_, v___x_2222_);
v___x_2228_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2226_, v___x_2227_);
v___x_2229_ = l_Array_append___redArg(v___x_2225_, v___x_2228_);
lean_dec_ref(v___x_2228_);
v___x_2230_ = l_Array_append___redArg(v___x_2229_, v_snd_2192_);
lean_dec(v_snd_2192_);
return v___x_2230_;
}
else
{
lean_object* v___x_2231_; 
lean_dec(v___x_2207_);
lean_dec(v_fst_2191_);
lean_dec(v_fst_2190_);
v___x_2231_ = l_Array_append___redArg(v_fst_2185_, v_snd_2192_);
lean_dec(v_snd_2192_);
return v___x_2231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object* v___x_2238_, lean_object* v_original_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_fst_2241_; lean_object* v_snd_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2261_; 
v_fst_2241_ = lean_ctor_get(v_a_2240_, 0);
v_snd_2242_ = lean_ctor_get(v_a_2240_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_a_2240_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2244_ = v_a_2240_;
v_isShared_2245_ = v_isSharedCheck_2261_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_snd_2242_);
lean_inc(v_fst_2241_);
lean_dec(v_a_2240_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2261_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
uint8_t v___x_2246_; 
v___x_2246_ = lean_nat_dec_lt(v_snd_2242_, v___x_2238_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2248_; 
if (v_isShared_2245_ == 0)
{
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_fst_2241_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_snd_2242_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
else
{
uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2250_ = 1;
v___x_2251_ = lean_array_fget_borrowed(v_original_2239_, v_snd_2242_);
v___x_2252_ = lean_box(v___x_2250_);
lean_inc(v___x_2251_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 1, v___x_2251_);
lean_ctor_set(v___x_2244_, 0, v___x_2252_);
v___x_2254_ = v___x_2244_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___x_2251_);
v___x_2254_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2255_ = lean_array_push(v_fst_2241_, v___x_2254_);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_nat_add(v_snd_2242_, v___x_2256_);
lean_dec(v_snd_2242_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2255_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v_a_2240_ = v___x_2258_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object* v___x_2262_, lean_object* v_original_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2262_, v_original_2263_, v_a_2264_);
lean_dec_ref(v_original_2263_);
lean_dec(v___x_2262_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object* v___x_2266_, lean_object* v_edited_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_fst_2269_; lean_object* v_snd_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2289_; 
v_fst_2269_ = lean_ctor_get(v_a_2268_, 0);
v_snd_2270_ = lean_ctor_get(v_a_2268_, 1);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_a_2268_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2272_ = v_a_2268_;
v_isShared_2273_ = v_isSharedCheck_2289_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_snd_2270_);
lean_inc(v_fst_2269_);
lean_dec(v_a_2268_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2289_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
uint8_t v___x_2274_; 
v___x_2274_ = lean_nat_dec_lt(v_snd_2270_, v___x_2266_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2276_; 
if (v_isShared_2273_ == 0)
{
v___x_2276_ = v___x_2272_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_fst_2269_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_snd_2270_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
else
{
uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2278_ = 0;
v___x_2279_ = lean_array_fget_borrowed(v_edited_2267_, v_snd_2270_);
v___x_2280_ = lean_box(v___x_2278_);
lean_inc(v___x_2279_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 1, v___x_2279_);
lean_ctor_set(v___x_2272_, 0, v___x_2280_);
v___x_2282_ = v___x_2272_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2279_);
v___x_2282_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2283_ = lean_array_push(v_fst_2269_, v___x_2282_);
v___x_2284_ = lean_unsigned_to_nat(1u);
v___x_2285_ = lean_nat_add(v_snd_2270_, v___x_2284_);
lean_dec(v_snd_2270_);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2283_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v_a_2268_ = v___x_2286_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_2290_, lean_object* v_edited_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2290_, v_edited_2291_, v_a_2292_);
lean_dec_ref(v_edited_2291_);
lean_dec(v___x_2290_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(lean_object* v___x_2294_, lean_object* v_original_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_fst_2298_; lean_object* v_snd_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2323_; 
v_fst_2298_ = lean_ctor_get(v_a_2297_, 0);
v_snd_2299_ = lean_ctor_get(v_a_2297_, 1);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_a_2297_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2301_ = v_a_2297_;
v_isShared_2302_ = v_isSharedCheck_2323_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_snd_2299_);
lean_inc(v_fst_2298_);
lean_dec(v_a_2297_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2323_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
uint8_t v___x_2303_; 
v___x_2303_ = lean_nat_dec_lt(v_snd_2299_, v___x_2294_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2305_; 
if (v_isShared_2302_ == 0)
{
v___x_2305_ = v___x_2301_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_fst_2298_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_snd_2299_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2308_ = lean_array_get_borrowed(v___x_2307_, v_original_2295_, v_snd_2299_);
v___x_2309_ = lean_string_dec_eq(v___x_2308_, v_a_2296_);
if (v___x_2309_ == 0)
{
uint8_t v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2310_ = 1;
v___x_2311_ = lean_box(v___x_2310_);
lean_inc(v___x_2308_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 1, v___x_2308_);
lean_ctor_set(v___x_2301_, 0, v___x_2311_);
v___x_2313_ = v___x_2301_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2308_);
v___x_2313_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2314_ = lean_array_push(v_fst_2298_, v___x_2313_);
v___x_2315_ = lean_unsigned_to_nat(1u);
v___x_2316_ = lean_nat_add(v_snd_2299_, v___x_2315_);
lean_dec(v_snd_2299_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2314_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v_a_2297_ = v___x_2317_;
goto _start;
}
}
else
{
lean_object* v___x_2321_; 
if (v_isShared_2302_ == 0)
{
v___x_2321_ = v___x_2301_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_fst_2298_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_snd_2299_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg___boxed(lean_object* v___x_2324_, lean_object* v_original_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2324_, v_original_2325_, v_a_2326_, v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec_ref(v_original_2325_);
lean_dec(v___x_2324_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object* v___x_2329_, lean_object* v_edited_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_fst_2333_; lean_object* v_snd_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2358_; 
v_fst_2333_ = lean_ctor_get(v_a_2332_, 0);
v_snd_2334_ = lean_ctor_get(v_a_2332_, 1);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_a_2332_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2336_ = v_a_2332_;
v_isShared_2337_ = v_isSharedCheck_2358_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_snd_2334_);
lean_inc(v_fst_2333_);
lean_dec(v_a_2332_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2358_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
uint8_t v___x_2338_; 
v___x_2338_ = lean_nat_dec_lt(v_snd_2334_, v___x_2329_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2340_; 
if (v_isShared_2337_ == 0)
{
v___x_2340_ = v___x_2336_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_fst_2333_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_snd_2334_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2342_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2343_ = lean_array_get_borrowed(v___x_2342_, v_edited_2330_, v_snd_2334_);
v___x_2344_ = lean_string_dec_eq(v___x_2343_, v_a_2331_);
if (v___x_2344_ == 0)
{
uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2345_ = 0;
v___x_2346_ = lean_box(v___x_2345_);
lean_inc(v___x_2343_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v___x_2343_);
lean_ctor_set(v___x_2336_, 0, v___x_2346_);
v___x_2348_ = v___x_2336_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2346_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v___x_2343_);
v___x_2348_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2349_ = lean_array_push(v_fst_2333_, v___x_2348_);
v___x_2350_ = lean_unsigned_to_nat(1u);
v___x_2351_ = lean_nat_add(v_snd_2334_, v___x_2350_);
lean_dec(v_snd_2334_);
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2349_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v_a_2332_ = v___x_2352_;
goto _start;
}
}
else
{
lean_object* v___x_2356_; 
if (v_isShared_2337_ == 0)
{
v___x_2356_ = v___x_2336_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_fst_2333_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_snd_2334_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_2359_, lean_object* v_edited_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2359_, v_edited_2360_, v_a_2361_, v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec_ref(v_edited_2360_);
lean_dec(v___x_2359_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v___x_2364_, lean_object* v_original_2365_, lean_object* v___x_2366_, lean_object* v_edited_2367_, lean_object* v_as_2368_, size_t v_sz_2369_, size_t v_i_2370_, lean_object* v_b_2371_){
_start:
{
uint8_t v___x_2372_; 
v___x_2372_ = lean_usize_dec_lt(v_i_2370_, v_sz_2369_);
if (v___x_2372_ == 0)
{
return v_b_2371_;
}
else
{
lean_object* v_snd_2373_; lean_object* v_fst_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2421_; 
v_snd_2373_ = lean_ctor_get(v_b_2371_, 1);
v_fst_2374_ = lean_ctor_get(v_b_2371_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_b_2371_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2376_ = v_b_2371_;
v_isShared_2377_ = v_isSharedCheck_2421_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_snd_2373_);
lean_inc(v_fst_2374_);
lean_dec(v_b_2371_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2421_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v_fst_2378_; lean_object* v_snd_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2420_; 
v_fst_2378_ = lean_ctor_get(v_snd_2373_, 0);
v_snd_2379_ = lean_ctor_get(v_snd_2373_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_snd_2373_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2381_ = v_snd_2373_;
v_isShared_2382_ = v_isSharedCheck_2420_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_snd_2379_);
lean_inc(v_fst_2378_);
lean_dec(v_snd_2373_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2420_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v_a_2383_; lean_object* v___x_2385_; 
v_a_2383_ = lean_array_uget_borrowed(v_as_2368_, v_i_2370_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 1, v_fst_2378_);
lean_ctor_set(v___x_2381_, 0, v_fst_2374_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_fst_2374_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_fst_2378_);
v___x_2385_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v_fst_2387_; lean_object* v_snd_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2418_; 
v___x_2386_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2364_, v_original_2365_, v_a_2383_, v___x_2385_);
v_fst_2387_ = lean_ctor_get(v___x_2386_, 0);
v_snd_2388_ = lean_ctor_get(v___x_2386_, 1);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2390_ = v___x_2386_;
v_isShared_2391_ = v_isSharedCheck_2418_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_snd_2388_);
lean_inc(v_fst_2387_);
lean_dec(v___x_2386_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2418_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v_snd_2379_);
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_fst_2387_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_snd_2379_);
v___x_2393_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2394_; lean_object* v_fst_2395_; lean_object* v_snd_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2416_; 
v___x_2394_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2366_, v_edited_2367_, v_a_2383_, v___x_2393_);
v_fst_2395_ = lean_ctor_get(v___x_2394_, 0);
v_snd_2396_ = lean_ctor_get(v___x_2394_, 1);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2398_ = v___x_2394_;
v_isShared_2399_ = v_isSharedCheck_2416_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_snd_2396_);
lean_inc(v_fst_2395_);
lean_dec(v___x_2394_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2416_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2400_ = 2;
v___x_2401_ = lean_box(v___x_2400_);
lean_inc(v_a_2383_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v_a_2383_);
lean_ctor_set(v___x_2398_, 0, v___x_2401_);
v___x_2403_ = v___x_2398_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_a_2383_);
v___x_2403_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2404_ = lean_array_push(v_fst_2395_, v___x_2403_);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_nat_add(v_snd_2388_, v___x_2405_);
lean_dec(v_snd_2388_);
v___x_2407_ = lean_nat_add(v_snd_2396_, v___x_2405_);
lean_dec(v_snd_2396_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 1, v___x_2407_);
lean_ctor_set(v___x_2376_, 0, v___x_2406_);
v___x_2409_ = v___x_2376_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; size_t v___x_2411_; size_t v___x_2412_; 
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2404_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = ((size_t)1ULL);
v___x_2412_ = lean_usize_add(v_i_2370_, v___x_2411_);
v_i_2370_ = v___x_2412_;
v_b_2371_ = v___x_2410_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v___x_2422_, lean_object* v_original_2423_, lean_object* v___x_2424_, lean_object* v_edited_2425_, lean_object* v_as_2426_, lean_object* v_sz_2427_, lean_object* v_i_2428_, lean_object* v_b_2429_){
_start:
{
size_t v_sz_boxed_2430_; size_t v_i_boxed_2431_; lean_object* v_res_2432_; 
v_sz_boxed_2430_ = lean_unbox_usize(v_sz_2427_);
lean_dec(v_sz_2427_);
v_i_boxed_2431_ = lean_unbox_usize(v_i_2428_);
lean_dec(v_i_2428_);
v_res_2432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2422_, v_original_2423_, v___x_2424_, v_edited_2425_, v_as_2426_, v_sz_boxed_2430_, v_i_boxed_2431_, v_b_2429_);
lean_dec_ref(v_as_2426_);
lean_dec_ref(v_edited_2425_);
lean_dec(v___x_2424_);
lean_dec_ref(v_original_2423_);
lean_dec(v___x_2422_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v___x_2433_, lean_object* v_edited_2434_, lean_object* v___x_2435_, lean_object* v_original_2436_, lean_object* v_as_2437_, size_t v_sz_2438_, size_t v_i_2439_, lean_object* v_b_2440_){
_start:
{
uint8_t v___x_2441_; 
v___x_2441_ = lean_usize_dec_lt(v_i_2439_, v_sz_2438_);
if (v___x_2441_ == 0)
{
return v_b_2440_;
}
else
{
lean_object* v_snd_2442_; lean_object* v_fst_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2490_; 
v_snd_2442_ = lean_ctor_get(v_b_2440_, 1);
v_fst_2443_ = lean_ctor_get(v_b_2440_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_b_2440_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2445_ = v_b_2440_;
v_isShared_2446_ = v_isSharedCheck_2490_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_snd_2442_);
lean_inc(v_fst_2443_);
lean_dec(v_b_2440_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2490_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_fst_2447_; lean_object* v_snd_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2489_; 
v_fst_2447_ = lean_ctor_get(v_snd_2442_, 0);
v_snd_2448_ = lean_ctor_get(v_snd_2442_, 1);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_snd_2442_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2450_ = v_snd_2442_;
v_isShared_2451_ = v_isSharedCheck_2489_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_snd_2448_);
lean_inc(v_fst_2447_);
lean_dec(v_snd_2442_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2489_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_a_2452_; lean_object* v___x_2454_; 
v_a_2452_ = lean_array_uget_borrowed(v_as_2437_, v_i_2439_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 1, v_fst_2447_);
lean_ctor_set(v___x_2450_, 0, v_fst_2443_);
v___x_2454_ = v___x_2450_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_fst_2443_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_fst_2447_);
v___x_2454_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2487_; 
v___x_2455_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2435_, v_original_2436_, v_a_2452_, v___x_2454_);
v_fst_2456_ = lean_ctor_get(v___x_2455_, 0);
v_snd_2457_ = lean_ctor_get(v___x_2455_, 1);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2459_ = v___x_2455_;
v_isShared_2460_ = v_isSharedCheck_2487_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_snd_2457_);
lean_inc(v_fst_2456_);
lean_dec(v___x_2455_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2487_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 1, v_snd_2448_);
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_fst_2456_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_snd_2448_);
v___x_2462_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2463_; lean_object* v_fst_2464_; lean_object* v_snd_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2485_; 
v___x_2463_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2433_, v_edited_2434_, v_a_2452_, v___x_2462_);
v_fst_2464_ = lean_ctor_get(v___x_2463_, 0);
v_snd_2465_ = lean_ctor_get(v___x_2463_, 1);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2467_ = v___x_2463_;
v_isShared_2468_ = v_isSharedCheck_2485_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_snd_2465_);
lean_inc(v_fst_2464_);
lean_dec(v___x_2463_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2485_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2469_ = 2;
v___x_2470_ = lean_box(v___x_2469_);
lean_inc(v_a_2452_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 1, v_a_2452_);
lean_ctor_set(v___x_2467_, 0, v___x_2470_);
v___x_2472_ = v___x_2467_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_a_2452_);
v___x_2472_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2473_ = lean_array_push(v_fst_2464_, v___x_2472_);
v___x_2474_ = lean_unsigned_to_nat(1u);
v___x_2475_ = lean_nat_add(v_snd_2457_, v___x_2474_);
lean_dec(v_snd_2457_);
v___x_2476_ = lean_nat_add(v_snd_2465_, v___x_2474_);
lean_dec(v_snd_2465_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 1, v___x_2476_);
lean_ctor_set(v___x_2445_, 0, v___x_2475_);
v___x_2478_ = v___x_2445_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; size_t v___x_2480_; size_t v___x_2481_; lean_object* v___x_2482_; 
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2473_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = ((size_t)1ULL);
v___x_2481_ = lean_usize_add(v_i_2439_, v___x_2480_);
v___x_2482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2435_, v_original_2436_, v___x_2433_, v_edited_2434_, v_as_2437_, v_sz_2438_, v___x_2481_, v___x_2479_);
return v___x_2482_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v___x_2491_, lean_object* v_edited_2492_, lean_object* v___x_2493_, lean_object* v_original_2494_, lean_object* v_as_2495_, lean_object* v_sz_2496_, lean_object* v_i_2497_, lean_object* v_b_2498_){
_start:
{
size_t v_sz_boxed_2499_; size_t v_i_boxed_2500_; lean_object* v_res_2501_; 
v_sz_boxed_2499_ = lean_unbox_usize(v_sz_2496_);
lean_dec(v_sz_2496_);
v_i_boxed_2500_ = lean_unbox_usize(v_i_2497_);
lean_dec(v_i_2497_);
v_res_2501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2491_, v_edited_2492_, v___x_2493_, v_original_2494_, v_as_2495_, v_sz_boxed_2499_, v_i_boxed_2500_, v_b_2498_);
lean_dec_ref(v_as_2495_);
lean_dec_ref(v_original_2494_);
lean_dec(v___x_2493_);
lean_dec_ref(v_edited_2492_);
lean_dec(v___x_2491_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2502_, size_t v_i_2503_, lean_object* v_bs_2504_){
_start:
{
uint8_t v___x_2505_; 
v___x_2505_ = lean_usize_dec_lt(v_i_2503_, v_sz_2502_);
if (v___x_2505_ == 0)
{
return v_bs_2504_;
}
else
{
lean_object* v_v_2506_; lean_object* v___x_2507_; lean_object* v_bs_x27_2508_; uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; size_t v___x_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
v_v_2506_ = lean_array_uget(v_bs_2504_, v_i_2503_);
v___x_2507_ = lean_unsigned_to_nat(0u);
v_bs_x27_2508_ = lean_array_uset(v_bs_2504_, v_i_2503_, v___x_2507_);
v___x_2509_ = 1;
v___x_2510_ = lean_box(v___x_2509_);
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v_v_2506_);
v___x_2512_ = ((size_t)1ULL);
v___x_2513_ = lean_usize_add(v_i_2503_, v___x_2512_);
v___x_2514_ = lean_array_uset(v_bs_x27_2508_, v_i_2503_, v___x_2511_);
v_i_2503_ = v___x_2513_;
v_bs_2504_ = v___x_2514_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2516_, lean_object* v_i_2517_, lean_object* v_bs_2518_){
_start:
{
size_t v_sz_boxed_2519_; size_t v_i_boxed_2520_; lean_object* v_res_2521_; 
v_sz_boxed_2519_ = lean_unbox_usize(v_sz_2516_);
lean_dec(v_sz_2516_);
v_i_boxed_2520_ = lean_unbox_usize(v_i_2517_);
lean_dec(v_i_2517_);
v_res_2521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2519_, v_i_boxed_2520_, v_bs_2518_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2527_, lean_object* v_edited_2528_){
_start:
{
lean_object* v_i_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v_i_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = lean_array_get_size(v_original_2527_);
v___x_2531_ = lean_nat_dec_lt(v_i_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
size_t v_sz_2532_; size_t v___x_2533_; lean_object* v___x_2534_; 
lean_dec_ref(v_original_2527_);
v_sz_2532_ = lean_array_size(v_edited_2528_);
v___x_2533_ = ((size_t)0ULL);
v___x_2534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2532_, v___x_2533_, v_edited_2528_);
return v___x_2534_;
}
else
{
lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2535_ = lean_array_get_size(v_edited_2528_);
v___x_2536_ = lean_nat_dec_lt(v_i_2529_, v___x_2535_);
if (v___x_2536_ == 0)
{
size_t v_sz_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
lean_dec_ref(v_edited_2528_);
v_sz_2537_ = lean_array_size(v_original_2527_);
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2537_, v___x_2538_, v_original_2527_);
return v___x_2539_;
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v_ds_2542_; lean_object* v___x_2543_; size_t v_sz_2544_; size_t v___x_2545_; lean_object* v___x_2546_; lean_object* v_snd_2547_; lean_object* v_fst_2548_; lean_object* v_fst_2549_; lean_object* v_snd_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2569_; 
lean_inc_ref(v_original_2527_);
v___x_2540_ = l_Array_toSubarray___redArg(v_original_2527_, v_i_2529_, v___x_2530_);
lean_inc_ref(v_edited_2528_);
v___x_2541_ = l_Array_toSubarray___redArg(v_edited_2528_, v_i_2529_, v___x_2535_);
v_ds_2542_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2540_, v___x_2541_);
v___x_2543_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2544_ = lean_array_size(v_ds_2542_);
v___x_2545_ = ((size_t)0ULL);
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2535_, v_edited_2528_, v___x_2530_, v_original_2527_, v_ds_2542_, v_sz_2544_, v___x_2545_, v___x_2543_);
lean_dec_ref(v_ds_2542_);
v_snd_2547_ = lean_ctor_get(v___x_2546_, 1);
lean_inc(v_snd_2547_);
v_fst_2548_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_fst_2548_);
lean_dec_ref(v___x_2546_);
v_fst_2549_ = lean_ctor_get(v_snd_2547_, 0);
v_snd_2550_ = lean_ctor_get(v_snd_2547_, 1);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_snd_2547_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2552_ = v_snd_2547_;
v_isShared_2553_ = v_isSharedCheck_2569_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_snd_2550_);
lean_inc(v_fst_2549_);
lean_dec(v_snd_2547_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2569_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v_fst_2549_);
lean_ctor_set(v___x_2552_, 0, v_fst_2548_);
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_fst_2548_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_fst_2549_);
v___x_2555_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2556_; lean_object* v_fst_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2566_; 
v___x_2556_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2530_, v_original_2527_, v___x_2555_);
lean_dec_ref(v_original_2527_);
v_fst_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2566_ == 0)
{
lean_object* v_unused_2567_; 
v_unused_2567_ = lean_ctor_get(v___x_2556_, 1);
lean_dec(v_unused_2567_);
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2566_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_fst_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2566_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 1, v_snd_2550_);
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_fst_2557_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_snd_2550_);
v___x_2562_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2563_; lean_object* v_fst_2564_; 
v___x_2563_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2535_, v_edited_2528_, v___x_2562_);
lean_dec_ref(v_edited_2528_);
v_fst_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_fst_2564_);
lean_dec_ref(v___x_2563_);
return v_fst_2564_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2570_, uint8_t v_inSubst_2571_, lean_object* v___x_2572_, lean_object* v_____r_2573_, lean_object* v_wssIdx_2574_){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2575_ = lean_box(v_inSubst_2571_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2570_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v_wssIdx_2574_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2572_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2580_, lean_object* v_inSubst_2581_, lean_object* v___x_2582_, lean_object* v_____r_2583_, lean_object* v_wssIdx_2584_){
_start:
{
uint8_t v_inSubst_boxed_2585_; lean_object* v_res_2586_; 
v_inSubst_boxed_2585_ = lean_unbox(v_inSubst_2581_);
v_res_2586_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2580_, v_inSubst_boxed_2585_, v___x_2582_, v_____r_2583_, v_wssIdx_2584_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2587_, uint8_t v___x_2588_, lean_object* v_fst_2589_, lean_object* v___x_2590_, lean_object* v_00___2591_){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2592_ = lean_box(v___x_2588_);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v_fst_2587_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v_fst_2589_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2590_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2597_, lean_object* v___x_2598_, lean_object* v_fst_2599_, lean_object* v___x_2600_, lean_object* v_00___2601_){
_start:
{
uint8_t v___x_9152__boxed_2602_; lean_object* v_res_2603_; 
v___x_9152__boxed_2602_ = lean_unbox(v___x_2598_);
v_res_2603_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2597_, v___x_9152__boxed_2602_, v_fst_2599_, v___x_2600_, v_00___2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2604_, lean_object* v_snd_2605_, lean_object* v_fst_2606_, lean_object* v_____r_2607_, lean_object* v_withWs_2608_, lean_object* v_wssIdx_2609_){
_start:
{
lean_object* v_wss_x27Idx_2611_; uint8_t v___x_2617_; 
v___x_2617_ = lean_unbox(v_snd_2605_);
if (v___x_2617_ == 0)
{
v_wss_x27Idx_2611_ = v_fst_2606_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_unsigned_to_nat(1u);
v___x_2619_ = lean_nat_add(v_fst_2606_, v___x_2618_);
lean_dec(v_fst_2606_);
v_wss_x27Idx_2611_ = v___x_2619_;
goto v___jp_2610_;
}
v___jp_2610_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2612_ = lean_box(v_inSubst_2604_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v_wss_x27Idx_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v_wssIdx_2609_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v_withWs_2608_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
return v___x_2616_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2620_, lean_object* v_snd_2621_, lean_object* v_fst_2622_, lean_object* v_____r_2623_, lean_object* v_withWs_2624_, lean_object* v_wssIdx_2625_){
_start:
{
uint8_t v_inSubst_boxed_2626_; lean_object* v_res_2627_; 
v_inSubst_boxed_2626_ = lean_unbox(v_inSubst_2620_);
v_res_2627_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2626_, v_snd_2621_, v_fst_2622_, v_____r_2623_, v_withWs_2624_, v_wssIdx_2625_);
lean_dec(v_snd_2621_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2628_, lean_object* v_diff_2629_, lean_object* v_snd_2630_, lean_object* v_snd_2631_, lean_object* v_a_2632_, lean_object* v_b_2633_){
_start:
{
lean_object* v_a_2635_; lean_object* v___y_2640_; uint8_t v___x_2643_; 
v___x_2643_ = lean_nat_dec_lt(v_a_2632_, v_upperBound_2628_);
if (v___x_2643_ == 0)
{
lean_dec(v_a_2632_);
return v_b_2633_;
}
else
{
lean_object* v___x_2644_; lean_object* v_snd_2645_; lean_object* v_snd_2646_; lean_object* v_fst_2647_; lean_object* v_fst_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2788_; 
v___x_2644_ = lean_array_fget_borrowed(v_diff_2629_, v_a_2632_);
v_snd_2645_ = lean_ctor_get(v_b_2633_, 1);
lean_inc(v_snd_2645_);
v_snd_2646_ = lean_ctor_get(v_snd_2645_, 1);
lean_inc(v_snd_2646_);
v_fst_2647_ = lean_ctor_get(v___x_2644_, 0);
v_fst_2648_ = lean_ctor_get(v_b_2633_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_b_2633_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; 
v_unused_2789_ = lean_ctor_get(v_b_2633_, 1);
lean_dec(v_unused_2789_);
v___x_2650_ = v_b_2633_;
v_isShared_2651_ = v_isSharedCheck_2788_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_fst_2648_);
lean_dec(v_b_2633_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2788_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v_fst_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2786_; 
v_fst_2652_ = lean_ctor_get(v_snd_2645_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_snd_2645_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v_snd_2645_, 1);
lean_dec(v_unused_2787_);
v___x_2654_ = v_snd_2645_;
v_isShared_2655_ = v_isSharedCheck_2786_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_fst_2652_);
lean_dec(v_snd_2645_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2786_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v_fst_2656_; lean_object* v_snd_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2785_; 
v_fst_2656_ = lean_ctor_get(v_snd_2646_, 0);
v_snd_2657_ = lean_ctor_get(v_snd_2646_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_snd_2646_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2659_ = v_snd_2646_;
v_isShared_2660_ = v_isSharedCheck_2785_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_snd_2657_);
lean_inc(v_fst_2656_);
lean_dec(v_snd_2646_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2785_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___y_2663_; lean_object* v___y_2678_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
lean_inc(v___x_2644_);
v___x_2661_ = lean_array_push(v_fst_2648_, v___x_2644_);
v___x_2686_ = lean_unsigned_to_nat(1u);
v___x_2687_ = lean_nat_add(v_a_2632_, v___x_2686_);
v___x_2688_ = lean_array_get_size(v_diff_2629_);
v___x_2689_ = lean_nat_dec_lt(v___x_2687_, v___x_2688_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec(v___x_2687_);
lean_del_object(v___x_2659_);
lean_del_object(v___x_2654_);
lean_del_object(v___x_2650_);
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v_fst_2656_);
lean_ctor_set(v___x_2690_, 1, v_snd_2657_);
v___x_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2691_, 0, v_fst_2652_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2661_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v_a_2635_ = v___x_2692_;
goto v___jp_2634_;
}
else
{
lean_object* v___x_2693_; lean_object* v_fst_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2783_; 
v___x_2693_ = lean_array_fget(v_diff_2629_, v___x_2687_);
lean_dec(v___x_2687_);
v_fst_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2783_ == 0)
{
lean_object* v_unused_2784_; 
v_unused_2784_ = lean_ctor_get(v___x_2693_, 1);
lean_dec(v_unused_2784_);
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2783_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_fst_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2783_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
uint8_t v_inSubst_2698_; lean_object* v___y_2700_; lean_object* v___x_2709_; uint8_t v___x_2710_; 
v_inSubst_2698_ = 0;
v___x_2709_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2710_ = lean_unbox(v_fst_2647_);
switch(v___x_2710_)
{
case 0:
{
uint8_t v___x_2711_; 
lean_del_object(v___x_2659_);
lean_del_object(v___x_2654_);
lean_del_object(v___x_2650_);
v___x_2711_ = lean_unbox(v_fst_2694_);
switch(v___x_2711_)
{
case 0:
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2712_ = lean_array_get_borrowed(v___x_2709_, v_snd_2630_, v_fst_2656_);
lean_inc(v___x_2712_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 1, v___x_2712_);
v___x_2714_ = v___x_2696_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_fst_2694_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2715_ = lean_array_push(v___x_2661_, v___x_2714_);
v___x_2716_ = lean_nat_add(v_fst_2656_, v___x_2686_);
lean_dec(v_fst_2656_);
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v_snd_2657_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_fst_2652_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2715_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v_a_2635_ = v___x_2719_;
goto v___jp_2634_;
}
}
case 1:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_del_object(v___x_2696_);
lean_dec(v_fst_2694_);
lean_dec(v_snd_2657_);
v___x_2721_ = lean_box(0);
v___x_2722_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2656_, v___x_2643_, v_fst_2652_, v___x_2661_, v___x_2721_);
v___y_2640_ = v___x_2722_;
goto v___jp_2639_;
}
default: 
{
lean_object* v___x_2723_; uint8_t v___x_2724_; 
lean_dec(v_fst_2694_);
v___x_2723_ = lean_array_get_borrowed(v___x_2709_, v_snd_2630_, v_fst_2656_);
v___x_2724_ = lean_unbox(v_snd_2657_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2726_; 
lean_inc(v___x_2723_);
lean_inc(v_fst_2647_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 1, v___x_2723_);
lean_ctor_set(v___x_2696_, 0, v_fst_2647_);
v___x_2726_ = v___x_2696_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_fst_2647_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v___x_2723_);
v___x_2726_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = lean_mk_empty_array_with_capacity(v___x_2686_);
v___x_2728_ = lean_array_push(v___x_2727_, v___x_2726_);
v___y_2700_ = v___x_2728_;
goto v___jp_2699_;
}
}
else
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
lean_del_object(v___x_2696_);
v___x_2730_ = lean_array_get_borrowed(v___x_2709_, v_snd_2631_, v_fst_2652_);
lean_inc(v___x_2723_);
lean_inc(v___x_2730_);
v___x_2731_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2730_, v___x_2723_);
v___y_2700_ = v___x_2731_;
goto v___jp_2699_;
}
}
}
}
case 1:
{
uint8_t v___x_2732_; 
lean_del_object(v___x_2659_);
lean_del_object(v___x_2654_);
lean_del_object(v___x_2650_);
v___x_2732_ = lean_unbox(v_fst_2694_);
switch(v___x_2732_)
{
case 0:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
lean_del_object(v___x_2696_);
lean_dec(v_fst_2694_);
lean_dec(v_snd_2657_);
v___x_2733_ = lean_box(0);
v___x_2734_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2656_, v___x_2643_, v_fst_2652_, v___x_2661_, v___x_2733_);
v___y_2640_ = v___x_2734_;
goto v___jp_2639_;
}
case 1:
{
lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2735_ = lean_array_get_borrowed(v___x_2709_, v_snd_2631_, v_fst_2652_);
lean_inc(v___x_2735_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 1, v___x_2735_);
v___x_2737_ = v___x_2696_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_fst_2694_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2738_ = lean_array_push(v___x_2661_, v___x_2737_);
v___x_2739_ = lean_nat_add(v_fst_2652_, v___x_2686_);
lean_dec(v_fst_2652_);
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v_fst_2656_);
lean_ctor_set(v___x_2740_, 1, v_snd_2657_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2738_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v_a_2635_ = v___x_2742_;
goto v___jp_2634_;
}
}
default: 
{
uint8_t v___x_2747_; 
lean_dec(v_fst_2694_);
v___x_2747_ = lean_unbox(v_snd_2657_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; 
v___x_2748_ = lean_array_get_borrowed(v___x_2709_, v_snd_2631_, v_fst_2652_);
v___x_2749_ = lean_unsigned_to_nat(0u);
v___x_2750_ = lean_string_utf8_byte_size(v___x_2748_);
lean_inc(v___x_2748_);
v___x_2751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2748_);
lean_ctor_set(v___x_2751_, 1, v___x_2749_);
lean_ctor_set(v___x_2751_, 2, v___x_2750_);
v___x_2752_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2751_);
lean_dec_ref_known(v___x_2751_, 3);
if (v___x_2752_ == 0)
{
lean_object* v___x_2754_; 
lean_inc(v___x_2748_);
lean_inc(v_fst_2647_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 1, v___x_2748_);
lean_ctor_set(v___x_2696_, 0, v_fst_2647_);
v___x_2754_ = v___x_2696_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_fst_2647_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v___x_2748_);
v___x_2754_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2755_ = lean_array_push(v___x_2661_, v___x_2754_);
v___x_2756_ = lean_nat_add(v_fst_2652_, v___x_2686_);
lean_dec(v_fst_2652_);
v___x_2757_ = lean_box(0);
v___x_2758_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2698_, v_snd_2657_, v_fst_2656_, v___x_2757_, v___x_2755_, v___x_2756_);
lean_dec(v_snd_2657_);
v___y_2640_ = v___x_2758_;
goto v___jp_2639_;
}
}
else
{
lean_del_object(v___x_2696_);
goto v___jp_2744_;
}
}
else
{
lean_del_object(v___x_2696_);
goto v___jp_2744_;
}
v___jp_2744_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = lean_box(0);
v___x_2746_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2698_, v_snd_2657_, v_fst_2656_, v___x_2745_, v___x_2661_, v_fst_2652_);
lean_dec(v_snd_2657_);
v___y_2640_ = v___x_2746_;
goto v___jp_2639_;
}
}
}
}
default: 
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_unbox(v_fst_2694_);
if (v___x_2760_ == 1)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v___x_2761_ = lean_array_get_borrowed(v___x_2709_, v_snd_2631_, v_fst_2652_);
v___x_2762_ = lean_array_get_size(v_snd_2630_);
v___x_2763_ = lean_nat_dec_lt(v_fst_2656_, v___x_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2765_; 
lean_inc(v___x_2761_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 1, v___x_2761_);
v___x_2765_ = v___x_2696_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_fst_2694_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v___x_2761_);
v___x_2765_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_mk_empty_array_with_capacity(v___x_2686_);
v___x_2767_ = lean_array_push(v___x_2766_, v___x_2765_);
v___y_2663_ = v___x_2767_;
goto v___jp_2662_;
}
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_del_object(v___x_2696_);
lean_dec(v_fst_2694_);
v___x_2769_ = lean_array_fget_borrowed(v_snd_2630_, v_fst_2656_);
lean_inc(v___x_2769_);
lean_inc(v___x_2761_);
v___x_2770_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2761_, v___x_2769_);
v___y_2663_ = v___x_2770_;
goto v___jp_2662_;
}
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
lean_dec(v_fst_2694_);
lean_del_object(v___x_2659_);
lean_del_object(v___x_2654_);
lean_del_object(v___x_2650_);
v___x_2771_ = lean_array_get_borrowed(v___x_2709_, v_snd_2630_, v_fst_2656_);
v___x_2772_ = lean_array_get_size(v_snd_2631_);
v___x_2773_ = lean_nat_dec_lt(v_fst_2652_, v___x_2772_);
if (v___x_2773_ == 0)
{
uint8_t v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2774_ = 0;
v___x_2775_ = lean_box(v___x_2774_);
lean_inc(v___x_2771_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 1, v___x_2771_);
lean_ctor_set(v___x_2696_, 0, v___x_2775_);
v___x_2777_ = v___x_2696_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v___x_2771_);
v___x_2777_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_mk_empty_array_with_capacity(v___x_2686_);
v___x_2779_ = lean_array_push(v___x_2778_, v___x_2777_);
v___y_2678_ = v___x_2779_;
goto v___jp_2677_;
}
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
lean_del_object(v___x_2696_);
v___x_2781_ = lean_array_fget_borrowed(v_snd_2631_, v_fst_2652_);
lean_inc(v___x_2771_);
lean_inc(v___x_2781_);
v___x_2782_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2781_, v___x_2771_);
v___y_2678_ = v___x_2782_;
goto v___jp_2677_;
}
}
}
}
v___jp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2701_ = l_Array_append___redArg(v___x_2661_, v___y_2700_);
lean_dec_ref(v___y_2700_);
v___x_2702_ = lean_nat_add(v_fst_2656_, v___x_2686_);
lean_dec(v_fst_2656_);
v___x_2703_ = lean_unbox(v_snd_2657_);
lean_dec(v_snd_2657_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = lean_box(0);
v___x_2705_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2702_, v_inSubst_2698_, v___x_2701_, v___x_2704_, v_fst_2652_);
v___y_2640_ = v___x_2705_;
goto v___jp_2639_;
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = lean_nat_add(v_fst_2652_, v___x_2686_);
lean_dec(v_fst_2652_);
v___x_2707_ = lean_box(0);
v___x_2708_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2702_, v_inSubst_2698_, v___x_2701_, v___x_2707_, v___x_2706_);
v___y_2640_ = v___x_2708_;
goto v___jp_2639_;
}
}
}
}
v___jp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2664_ = l_Array_append___redArg(v___x_2661_, v___y_2663_);
lean_dec_ref(v___y_2663_);
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_nat_add(v_fst_2652_, v___x_2665_);
lean_dec(v_fst_2652_);
v___x_2667_ = lean_nat_add(v_fst_2656_, v___x_2665_);
lean_dec(v_fst_2656_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___x_2667_);
v___x_2669_ = v___x_2659_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_snd_2657_);
v___x_2669_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2671_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 1, v___x_2669_);
lean_ctor_set(v___x_2654_, 0, v___x_2666_);
v___x_2671_ = v___x_2654_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2673_; 
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 1, v___x_2671_);
lean_ctor_set(v___x_2650_, 0, v___x_2664_);
v___x_2673_ = v___x_2650_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
v_a_2635_ = v___x_2673_;
goto v___jp_2634_;
}
}
}
}
v___jp_2677_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2679_ = l_Array_append___redArg(v___x_2661_, v___y_2678_);
lean_dec_ref(v___y_2678_);
v___x_2680_ = lean_unsigned_to_nat(1u);
v___x_2681_ = lean_nat_add(v_fst_2652_, v___x_2680_);
lean_dec(v_fst_2652_);
v___x_2682_ = lean_nat_add(v_fst_2656_, v___x_2680_);
lean_dec(v_fst_2656_);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v_snd_2657_);
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2681_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2679_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v_a_2635_ = v___x_2685_;
goto v___jp_2634_;
}
}
}
}
}
v___jp_2634_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_unsigned_to_nat(1u);
v___x_2637_ = lean_nat_add(v_a_2632_, v___x_2636_);
lean_dec(v_a_2632_);
v_a_2632_ = v___x_2637_;
v_b_2633_ = v_a_2635_;
goto _start;
}
v___jp_2639_:
{
if (lean_obj_tag(v___y_2640_) == 0)
{
lean_object* v_a_2641_; 
lean_dec(v_a_2632_);
v_a_2641_ = lean_ctor_get(v___y_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___y_2640_, 1);
return v_a_2641_;
}
else
{
lean_object* v_a_2642_; 
v_a_2642_ = lean_ctor_get(v___y_2640_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___y_2640_, 1);
v_a_2635_ = v_a_2642_;
goto v___jp_2634_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2790_, lean_object* v_diff_2791_, lean_object* v_snd_2792_, lean_object* v_snd_2793_, lean_object* v_a_2794_, lean_object* v_b_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2790_, v_diff_2791_, v_snd_2792_, v_snd_2793_, v_a_2794_, v_b_2795_);
lean_dec_ref(v_snd_2793_);
lean_dec_ref(v_snd_2792_);
lean_dec_ref(v_diff_2791_);
lean_dec(v_upperBound_2790_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2807_, lean_object* v_s_x27_2808_){
_start:
{
lean_object* v___x_2809_; lean_object* v_fst_2810_; lean_object* v_snd_2811_; lean_object* v___x_2812_; lean_object* v_fst_2813_; lean_object* v_snd_2814_; lean_object* v_diff_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v_fst_2820_; lean_object* v___x_2821_; size_t v_sz_2822_; size_t v___x_2823_; lean_object* v___x_2824_; 
v___x_2809_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2807_);
v_fst_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_fst_2810_);
v_snd_2811_ = lean_ctor_get(v___x_2809_, 1);
lean_inc(v_snd_2811_);
lean_dec_ref(v___x_2809_);
v___x_2812_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2808_);
v_fst_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_fst_2813_);
v_snd_2814_ = lean_ctor_get(v___x_2812_, 1);
lean_inc(v_snd_2814_);
lean_dec_ref(v___x_2812_);
v_diff_2815_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_2810_, v_fst_2813_);
v___x_2816_ = lean_unsigned_to_nat(0u);
v___x_2817_ = lean_array_get_size(v_diff_2815_);
v___x_2818_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2819_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2817_, v_diff_2815_, v_snd_2814_, v_snd_2811_, v___x_2816_, v___x_2818_);
lean_dec(v_snd_2811_);
lean_dec(v_snd_2814_);
lean_dec_ref(v_diff_2815_);
v_fst_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_fst_2820_);
lean_dec_ref(v___x_2819_);
v___x_2821_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2820_);
lean_dec(v_fst_2820_);
v_sz_2822_ = lean_array_size(v___x_2821_);
v___x_2823_ = ((size_t)0ULL);
v___x_2824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2822_, v___x_2823_, v___x_2821_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2825_, lean_object* v_s_x27_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2825_, v_s_x27_2826_);
lean_dec_ref(v_s_x27_2826_);
lean_dec_ref(v_s_2825_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2828_, lean_object* v_diff_2829_, lean_object* v_snd_2830_, lean_object* v_snd_2831_, lean_object* v_inst_2832_, lean_object* v_R_2833_, lean_object* v_a_2834_, lean_object* v_b_2835_, lean_object* v_c_2836_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2828_, v_diff_2829_, v_snd_2830_, v_snd_2831_, v_a_2834_, v_b_2835_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2838_, lean_object* v_diff_2839_, lean_object* v_snd_2840_, lean_object* v_snd_2841_, lean_object* v_inst_2842_, lean_object* v_R_2843_, lean_object* v_a_2844_, lean_object* v_b_2845_, lean_object* v_c_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2838_, v_diff_2839_, v_snd_2840_, v_snd_2841_, v_inst_2842_, v_R_2843_, v_a_2844_, v_b_2845_, v_c_2846_);
lean_dec_ref(v_snd_2841_);
lean_dec_ref(v_snd_2840_);
lean_dec_ref(v_diff_2839_);
lean_dec(v_upperBound_2838_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v___x_2848_, lean_object* v_original_2849_, lean_object* v_a_2850_, lean_object* v_inst_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2848_, v_original_2849_, v_a_2850_, v_a_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___boxed(lean_object* v___x_2854_, lean_object* v_original_2855_, lean_object* v_a_2856_, lean_object* v_inst_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2854_, v_original_2855_, v_a_2856_, v_inst_2857_, v_a_2858_);
lean_dec_ref(v_a_2856_);
lean_dec_ref(v_original_2855_);
lean_dec(v___x_2854_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v___x_2860_, lean_object* v_edited_2861_, lean_object* v_a_2862_, lean_object* v_inst_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2860_, v_edited_2861_, v_a_2862_, v_a_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v___x_2866_, lean_object* v_edited_2867_, lean_object* v_a_2868_, lean_object* v_inst_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v___x_2866_, v_edited_2867_, v_a_2868_, v_inst_2869_, v_a_2870_);
lean_dec_ref(v_a_2868_);
lean_dec_ref(v_edited_2867_);
lean_dec(v___x_2866_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2872_, lean_object* v_original_2873_, lean_object* v_inst_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2872_, v_original_2873_, v_a_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2877_, lean_object* v_original_2878_, lean_object* v_inst_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2877_, v_original_2878_, v_inst_2879_, v_a_2880_);
lean_dec_ref(v_original_2878_);
lean_dec(v___x_2877_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2882_, lean_object* v_edited_2883_, lean_object* v_inst_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2882_, v_edited_2883_, v_a_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2887_, lean_object* v_edited_2888_, lean_object* v_inst_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2887_, v_edited_2888_, v_inst_2889_, v_a_2890_);
lean_dec_ref(v_edited_2888_);
lean_dec(v___x_2887_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(lean_object* v_as_2892_, lean_object* v_as_x27_2893_, lean_object* v_b_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2893_, v_b_2894_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___boxed(lean_object* v_as_2897_, lean_object* v_as_x27_2898_, lean_object* v_b_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(v_as_2897_, v_as_x27_2898_, v_b_2899_, v_a_2900_);
lean_dec(v_as_x27_2898_);
lean_dec(v_as_2897_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(lean_object* v_lsize_2902_, lean_object* v_rsize_2903_, lean_object* v_histogram_2904_, lean_object* v_index_2905_, lean_object* v_val_2906_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_histogram_2904_, v_index_2905_, v_val_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___boxed(lean_object* v_lsize_2908_, lean_object* v_rsize_2909_, lean_object* v_histogram_2910_, lean_object* v_index_2911_, lean_object* v_val_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(v_lsize_2908_, v_rsize_2909_, v_histogram_2910_, v_index_2911_, v_val_2912_);
lean_dec(v_rsize_2909_);
lean_dec(v_lsize_2908_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(lean_object* v_upperBound_2914_, lean_object* v___x_2915_, lean_object* v_fst_2916_, lean_object* v___x_2917_, lean_object* v_inst_2918_, lean_object* v_R_2919_, lean_object* v_a_2920_, lean_object* v_b_2921_, lean_object* v_c_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_2914_, v___x_2915_, v_fst_2916_, v___x_2917_, v_a_2920_, v_b_2921_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___boxed(lean_object* v_upperBound_2924_, lean_object* v___x_2925_, lean_object* v_fst_2926_, lean_object* v___x_2927_, lean_object* v_inst_2928_, lean_object* v_R_2929_, lean_object* v_a_2930_, lean_object* v_b_2931_, lean_object* v_c_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(v_upperBound_2924_, v___x_2925_, v_fst_2926_, v___x_2927_, v_inst_2928_, v_R_2929_, v_a_2930_, v_b_2931_, v_c_2932_);
lean_dec(v___x_2927_);
lean_dec_ref(v_fst_2926_);
lean_dec(v___x_2925_);
lean_dec(v_upperBound_2924_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(lean_object* v_lsize_2934_, lean_object* v_rsize_2935_, lean_object* v_histogram_2936_, lean_object* v_index_2937_, lean_object* v_val_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_histogram_2936_, v_index_2937_, v_val_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___boxed(lean_object* v_lsize_2940_, lean_object* v_rsize_2941_, lean_object* v_histogram_2942_, lean_object* v_index_2943_, lean_object* v_val_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(v_lsize_2940_, v_rsize_2941_, v_histogram_2942_, v_index_2943_, v_val_2944_);
lean_dec(v_rsize_2941_);
lean_dec(v_lsize_2940_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(lean_object* v_upperBound_2946_, lean_object* v_fst_2947_, lean_object* v___x_2948_, lean_object* v_fst_2949_, lean_object* v_inst_2950_, lean_object* v_R_2951_, lean_object* v_a_2952_, lean_object* v_b_2953_, lean_object* v_c_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2946_, v_fst_2947_, v___x_2948_, v_fst_2949_, v_a_2952_, v_b_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___boxed(lean_object* v_upperBound_2956_, lean_object* v_fst_2957_, lean_object* v___x_2958_, lean_object* v_fst_2959_, lean_object* v_inst_2960_, lean_object* v_R_2961_, lean_object* v_a_2962_, lean_object* v_b_2963_, lean_object* v_c_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(v_upperBound_2956_, v_fst_2957_, v___x_2958_, v_fst_2959_, v_inst_2960_, v_R_2961_, v_a_2962_, v_b_2963_, v_c_2964_);
lean_dec_ref(v_fst_2959_);
lean_dec(v___x_2958_);
lean_dec_ref(v_fst_2957_);
lean_dec(v_upperBound_2956_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_2966_, lean_object* v_m_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_2967_, v_a_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2970_, lean_object* v_m_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(v_00_u03b2_2970_, v_m_2971_, v_a_2972_);
lean_dec_ref(v_a_2972_);
lean_dec_ref(v_m_2971_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_2974_, lean_object* v_m_2975_, lean_object* v_a_2976_, lean_object* v_b_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_m_2975_, v_a_2976_, v_b_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14(lean_object* v_inst_2979_, lean_object* v_R_2980_, lean_object* v_a_2981_, lean_object* v_b_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v_a_2981_, v_b_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(lean_object* v_00_u03b2_2984_, lean_object* v_a_2985_, lean_object* v_x_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_2985_, v_x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___boxed(lean_object* v_00_u03b2_2988_, lean_object* v_a_2989_, lean_object* v_x_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(v_00_u03b2_2988_, v_a_2989_, v_x_2990_);
lean_dec(v_x_2990_);
lean_dec_ref(v_a_2989_);
return v_res_2991_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(lean_object* v_00_u03b2_2992_, lean_object* v_a_2993_, lean_object* v_x_2994_){
_start:
{
uint8_t v___x_2995_; 
v___x_2995_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_2993_, v_x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___boxed(lean_object* v_00_u03b2_2996_, lean_object* v_a_2997_, lean_object* v_x_2998_){
_start:
{
uint8_t v_res_2999_; lean_object* v_r_3000_; 
v_res_2999_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(v_00_u03b2_2996_, v_a_2997_, v_x_2998_);
lean_dec(v_x_2998_);
lean_dec_ref(v_a_2997_);
v_r_3000_ = lean_box(v_res_2999_);
return v_r_3000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23(lean_object* v_00_u03b2_3001_, lean_object* v_data_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_data_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24(lean_object* v_00_u03b2_3004_, lean_object* v_a_3005_, lean_object* v_b_3006_, lean_object* v_x_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_3005_, v_b_3006_, v_x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_3009_, lean_object* v_i_3010_, lean_object* v_source_3011_, lean_object* v_target_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v_i_3010_, v_source_3011_, v_target_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_3014_, lean_object* v_x_3015_, lean_object* v_x_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_x_3015_, v_x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3018_){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_string_data(v_s_3018_);
v___x_3020_ = lean_array_mk(v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3021_, lean_object* v_s_x27_3022_){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3023_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3021_);
v___x_3024_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3022_);
v___x_3025_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3023_, v___x_3024_);
v___x_3026_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3025_);
lean_dec_ref(v___x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3027_, lean_object* v_s_x27_3028_){
_start:
{
uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3029_ = 1;
v___x_3030_ = lean_box(v___x_3029_);
v___x_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set(v___x_3031_, 1, v_s_3027_);
v___x_3032_ = 0;
v___x_3033_ = lean_box(v___x_3032_);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v_s_x27_3028_);
v___x_3035_ = lean_unsigned_to_nat(2u);
v___x_3036_ = lean_mk_empty_array_with_capacity(v___x_3035_);
v___x_3037_ = lean_array_push(v___x_3036_, v___x_3031_);
v___x_3038_ = lean_array_push(v___x_3037_, v___x_3034_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3039_, size_t v_i_3040_, size_t v_stop_3041_, lean_object* v_b_3042_){
_start:
{
lean_object* v___y_3044_; uint8_t v___x_3048_; 
v___x_3048_ = lean_usize_dec_eq(v_i_3040_, v_stop_3041_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v_fst_3050_; uint8_t v___x_3051_; uint8_t v___x_3052_; uint8_t v___x_3053_; 
v___x_3049_ = lean_array_uget_borrowed(v_as_3039_, v_i_3040_);
v_fst_3050_ = lean_ctor_get(v___x_3049_, 0);
v___x_3051_ = 2;
v___x_3052_ = lean_unbox(v_fst_3050_);
v___x_3053_ = l_Lean_Diff_instBEqAction_beq(v___x_3052_, v___x_3051_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; 
lean_inc(v___x_3049_);
v___x_3054_ = lean_array_push(v_b_3042_, v___x_3049_);
v___y_3044_ = v___x_3054_;
goto v___jp_3043_;
}
else
{
v___y_3044_ = v_b_3042_;
goto v___jp_3043_;
}
}
else
{
return v_b_3042_;
}
v___jp_3043_:
{
size_t v___x_3045_; size_t v___x_3046_; 
v___x_3045_ = ((size_t)1ULL);
v___x_3046_ = lean_usize_add(v_i_3040_, v___x_3045_);
v_i_3040_ = v___x_3046_;
v_b_3042_ = v___y_3044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3055_, lean_object* v_i_3056_, lean_object* v_stop_3057_, lean_object* v_b_3058_){
_start:
{
size_t v_i_boxed_3059_; size_t v_stop_boxed_3060_; lean_object* v_res_3061_; 
v_i_boxed_3059_ = lean_unbox_usize(v_i_3056_);
lean_dec(v_i_3056_);
v_stop_boxed_3060_ = lean_unbox_usize(v_stop_3057_);
lean_dec(v_stop_3057_);
v_res_3061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3055_, v_i_boxed_3059_, v_stop_boxed_3060_, v_b_3058_);
lean_dec_ref(v_as_3055_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3062_, lean_object* v_s_x27_3063_, uint8_t v_granularity_3064_){
_start:
{
lean_object* v___y_3066_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; 
switch(v_granularity_3064_)
{
case 0:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___y_3108_; uint8_t v___x_3114_; 
v___x_3105_ = lean_string_length(v_s_3062_);
v___x_3106_ = lean_string_length(v_s_x27_3063_);
v___x_3114_ = lean_nat_dec_le(v___x_3105_, v___x_3106_);
if (v___x_3114_ == 0)
{
v___y_3108_ = v___x_3106_;
goto v___jp_3107_;
}
else
{
v___y_3108_ = v___x_3105_;
goto v___jp_3107_;
}
v___jp_3107_:
{
lean_object* v___x_3109_; lean_object* v_maxCharDiffDistance_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3109_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3110_ = lean_nat_div(v___y_3108_, v___x_3109_);
v___x_3111_ = lean_unsigned_to_nat(1u);
v___x_3112_ = lean_nat_shiftr(v___y_3108_, v___x_3111_);
lean_dec(v___y_3108_);
v___x_3113_ = lean_nat_dec_le(v___x_3105_, v___x_3106_);
if (v___x_3113_ == 0)
{
v___y_3085_ = v___x_3111_;
v___y_3086_ = v_maxCharDiffDistance_3110_;
v___y_3087_ = v___x_3112_;
v___y_3088_ = v___x_3105_;
goto v___jp_3084_;
}
else
{
v___y_3085_ = v___x_3111_;
v___y_3086_ = v_maxCharDiffDistance_3110_;
v___y_3087_ = v___x_3112_;
v___y_3088_ = v___x_3106_;
goto v___jp_3084_;
}
}
}
case 1:
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3062_, v_s_x27_3063_);
return v___x_3115_;
}
case 2:
{
lean_object* v___x_3116_; 
v___x_3116_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3062_, v_s_x27_3063_);
lean_dec_ref(v_s_x27_3063_);
lean_dec_ref(v_s_3062_);
return v___x_3116_;
}
case 3:
{
lean_object* v___x_3117_; 
v___x_3117_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3062_, v_s_x27_3063_);
return v___x_3117_;
}
default: 
{
uint8_t v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_dec_ref(v_s_3062_);
v___x_3118_ = 0;
v___x_3119_ = lean_box(v___x_3118_);
v___x_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
lean_ctor_set(v___x_3120_, 1, v_s_x27_3063_);
v___x_3121_ = lean_unsigned_to_nat(1u);
v___x_3122_ = lean_mk_empty_array_with_capacity(v___x_3121_);
v___x_3123_ = lean_array_push(v___x_3122_, v___x_3120_);
return v___x_3123_;
}
}
v___jp_3065_:
{
size_t v_sz_3067_; size_t v___x_3068_; lean_object* v___x_3069_; 
v_sz_3067_ = lean_array_size(v___y_3066_);
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3067_, v___x_3068_, v___y_3066_);
return v___x_3069_;
}
v___jp_3070_:
{
lean_object* v_charArrDiff_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; 
v_charArrDiff_3075_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3072_);
lean_dec_ref(v___y_3072_);
v___x_3076_ = lean_array_get_size(v_charArrDiff_3075_);
v___x_3077_ = lean_unsigned_to_nat(3u);
v___x_3078_ = lean_nat_dec_le(v___x_3076_, v___x_3077_);
if (v___x_3078_ == 0)
{
lean_object* v_approxEditDistance_3079_; uint8_t v___x_3080_; 
v_approxEditDistance_3079_ = lean_array_get_size(v___y_3074_);
lean_dec_ref(v___y_3074_);
v___x_3080_ = lean_nat_dec_le(v_approxEditDistance_3079_, v___y_3073_);
lean_dec(v___y_3073_);
if (v___x_3080_ == 0)
{
uint8_t v___x_3081_; 
lean_dec_ref(v_charArrDiff_3075_);
v___x_3081_ = lean_nat_dec_le(v_approxEditDistance_3079_, v___y_3071_);
lean_dec(v___y_3071_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; 
v___x_3082_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3062_, v_s_x27_3063_);
return v___x_3082_;
}
else
{
lean_object* v___x_3083_; 
v___x_3083_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3062_, v_s_x27_3063_);
lean_dec_ref(v_s_x27_3063_);
lean_dec_ref(v_s_3062_);
return v___x_3083_;
}
}
else
{
lean_dec(v___y_3071_);
lean_dec_ref(v_s_x27_3063_);
lean_dec_ref(v_s_3062_);
v___y_3066_ = v_charArrDiff_3075_;
goto v___jp_3065_;
}
}
else
{
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec(v___y_3071_);
lean_dec_ref(v_s_x27_3063_);
lean_dec_ref(v_s_3062_);
v___y_3066_ = v_charArrDiff_3075_;
goto v___jp_3065_;
}
}
v___jp_3084_:
{
lean_object* v___x_3089_; lean_object* v_maxWordDiffDistance_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v_charDiffRaw_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3089_ = lean_nat_shiftr(v___y_3088_, v___y_3085_);
lean_dec(v___y_3088_);
v_maxWordDiffDistance_3090_ = lean_nat_add(v___y_3087_, v___x_3089_);
lean_dec(v___x_3089_);
lean_dec(v___y_3087_);
lean_inc_ref(v_s_3062_);
v___x_3091_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3062_);
lean_inc_ref(v_s_x27_3063_);
v___x_3092_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3063_);
v_charDiffRaw_3093_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3091_, v___x_3092_);
v___x_3094_ = lean_unsigned_to_nat(0u);
v___x_3095_ = lean_array_get_size(v_charDiffRaw_3093_);
v___x_3096_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3097_ = lean_nat_dec_lt(v___x_3094_, v___x_3095_);
if (v___x_3097_ == 0)
{
v___y_3071_ = v_maxWordDiffDistance_3090_;
v___y_3072_ = v_charDiffRaw_3093_;
v___y_3073_ = v___y_3086_;
v___y_3074_ = v___x_3096_;
goto v___jp_3070_;
}
else
{
uint8_t v___x_3098_; 
v___x_3098_ = lean_nat_dec_le(v___x_3095_, v___x_3095_);
if (v___x_3098_ == 0)
{
if (v___x_3097_ == 0)
{
v___y_3071_ = v_maxWordDiffDistance_3090_;
v___y_3072_ = v_charDiffRaw_3093_;
v___y_3073_ = v___y_3086_;
v___y_3074_ = v___x_3096_;
goto v___jp_3070_;
}
else
{
size_t v___x_3099_; size_t v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = ((size_t)0ULL);
v___x_3100_ = lean_usize_of_nat(v___x_3095_);
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3093_, v___x_3099_, v___x_3100_, v___x_3096_);
v___y_3071_ = v_maxWordDiffDistance_3090_;
v___y_3072_ = v_charDiffRaw_3093_;
v___y_3073_ = v___y_3086_;
v___y_3074_ = v___x_3101_;
goto v___jp_3070_;
}
}
else
{
size_t v___x_3102_; size_t v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = ((size_t)0ULL);
v___x_3103_ = lean_usize_of_nat(v___x_3095_);
v___x_3104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3093_, v___x_3102_, v___x_3103_, v___x_3096_);
v___y_3071_ = v_maxWordDiffDistance_3090_;
v___y_3072_ = v_charDiffRaw_3093_;
v___y_3073_ = v___y_3086_;
v___y_3074_ = v___x_3104_;
goto v___jp_3070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3124_, lean_object* v_s_x27_3125_, lean_object* v_granularity_3126_){
_start:
{
uint8_t v_granularity_boxed_3127_; lean_object* v_res_3128_; 
v_granularity_boxed_3127_ = lean_unbox(v_granularity_3126_);
v_res_3128_ = l_Lean_Meta_Hint_readableDiff(v_s_3124_, v_s_x27_3125_, v_granularity_boxed_3127_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3129_, size_t v_i_3130_, size_t v_stop_3131_, lean_object* v_b_3132_){
_start:
{
uint8_t v___x_3133_; 
v___x_3133_ = lean_usize_dec_eq(v_i_3130_, v_stop_3131_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; lean_object* v_snd_3135_; lean_object* v___x_3136_; size_t v___x_3137_; size_t v___x_3138_; 
v___x_3134_ = lean_array_uget_borrowed(v_as_3129_, v_i_3130_);
v_snd_3135_ = lean_ctor_get(v___x_3134_, 1);
v___x_3136_ = lean_string_append(v_b_3132_, v_snd_3135_);
v___x_3137_ = ((size_t)1ULL);
v___x_3138_ = lean_usize_add(v_i_3130_, v___x_3137_);
v_i_3130_ = v___x_3138_;
v_b_3132_ = v___x_3136_;
goto _start;
}
else
{
return v_b_3132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3140_, lean_object* v_i_3141_, lean_object* v_stop_3142_, lean_object* v_b_3143_){
_start:
{
size_t v_i_boxed_3144_; size_t v_stop_boxed_3145_; lean_object* v_res_3146_; 
v_i_boxed_3144_ = lean_unbox_usize(v_i_3141_);
lean_dec(v_i_3141_);
v_stop_boxed_3145_ = lean_unbox_usize(v_stop_3142_);
lean_dec(v_stop_3142_);
v_res_3146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3140_, v_i_boxed_3144_, v_stop_boxed_3145_, v_b_3143_);
lean_dec_ref(v_as_3140_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; lean_object* v_infoState_3151_; uint8_t v_enabled_3152_; 
v___x_3150_ = lean_st_ref_get(v___y_3148_);
v_infoState_3151_ = lean_ctor_get(v___x_3150_, 8);
lean_inc_ref(v_infoState_3151_);
lean_dec(v___x_3150_);
v_enabled_3152_ = lean_ctor_get_uint8(v_infoState_3151_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3151_);
if (v_enabled_3152_ == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec_ref(v_t_3147_);
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
else
{
lean_object* v___x_3155_; lean_object* v_infoState_3156_; lean_object* v_env_3157_; lean_object* v_nextMacroScope_3158_; lean_object* v_ngen_3159_; lean_object* v_auxDeclNGen_3160_; lean_object* v_traceState_3161_; lean_object* v_cache_3162_; lean_object* v_recordedDeps_3163_; lean_object* v_messages_3164_; lean_object* v_snapshotTasks_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3187_; 
v___x_3155_ = lean_st_ref_take(v___y_3148_);
v_infoState_3156_ = lean_ctor_get(v___x_3155_, 8);
v_env_3157_ = lean_ctor_get(v___x_3155_, 0);
v_nextMacroScope_3158_ = lean_ctor_get(v___x_3155_, 1);
v_ngen_3159_ = lean_ctor_get(v___x_3155_, 2);
v_auxDeclNGen_3160_ = lean_ctor_get(v___x_3155_, 3);
v_traceState_3161_ = lean_ctor_get(v___x_3155_, 4);
v_cache_3162_ = lean_ctor_get(v___x_3155_, 5);
v_recordedDeps_3163_ = lean_ctor_get(v___x_3155_, 6);
v_messages_3164_ = lean_ctor_get(v___x_3155_, 7);
v_snapshotTasks_3165_ = lean_ctor_get(v___x_3155_, 9);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3167_ = v___x_3155_;
v_isShared_3168_ = v_isSharedCheck_3187_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_snapshotTasks_3165_);
lean_inc(v_infoState_3156_);
lean_inc(v_messages_3164_);
lean_inc(v_recordedDeps_3163_);
lean_inc(v_cache_3162_);
lean_inc(v_traceState_3161_);
lean_inc(v_auxDeclNGen_3160_);
lean_inc(v_ngen_3159_);
lean_inc(v_nextMacroScope_3158_);
lean_inc(v_env_3157_);
lean_dec(v___x_3155_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3187_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
uint8_t v_enabled_3169_; lean_object* v_assignment_3170_; lean_object* v_lazyAssignment_3171_; lean_object* v_trees_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3186_; 
v_enabled_3169_ = lean_ctor_get_uint8(v_infoState_3156_, sizeof(void*)*3);
v_assignment_3170_ = lean_ctor_get(v_infoState_3156_, 0);
v_lazyAssignment_3171_ = lean_ctor_get(v_infoState_3156_, 1);
v_trees_3172_ = lean_ctor_get(v_infoState_3156_, 2);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_infoState_3156_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3174_ = v_infoState_3156_;
v_isShared_3175_ = v_isSharedCheck_3186_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_trees_3172_);
lean_inc(v_lazyAssignment_3171_);
lean_inc(v_assignment_3170_);
lean_dec(v_infoState_3156_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3186_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3176_ = lean_box(0);
v___x_3177_ = l_Lean_PersistentArray_push___redArg(v_trees_3172_, v_t_3147_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 2, v___x_3177_);
v___x_3179_ = v___x_3174_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_assignment_3170_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_lazyAssignment_3171_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v___x_3177_);
lean_ctor_set_uint8(v_reuseFailAlloc_3185_, sizeof(void*)*3, v_enabled_3169_);
v___x_3179_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3181_; 
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 8, v___x_3179_);
v___x_3181_ = v___x_3167_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_env_3157_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_nextMacroScope_3158_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_ngen_3159_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_auxDeclNGen_3160_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v_traceState_3161_);
lean_ctor_set(v_reuseFailAlloc_3184_, 5, v_cache_3162_);
lean_ctor_set(v_reuseFailAlloc_3184_, 6, v_recordedDeps_3163_);
lean_ctor_set(v_reuseFailAlloc_3184_, 7, v_messages_3164_);
lean_ctor_set(v_reuseFailAlloc_3184_, 8, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3184_, 9, v_snapshotTasks_3165_);
v___x_3181_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_st_ref_put(v___y_3148_, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3176_);
return v___x_3183_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3188_, v___y_3189_);
lean_dec(v___y_3189_);
return v_res_3191_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = lean_unsigned_to_nat(32u);
v___x_3193_ = lean_mk_empty_array_with_capacity(v___x_3192_);
v___x_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
return v___x_3194_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3195_ = ((size_t)5ULL);
v___x_3196_ = lean_unsigned_to_nat(0u);
v___x_3197_ = lean_unsigned_to_nat(32u);
v___x_3198_ = lean_mk_empty_array_with_capacity(v___x_3197_);
v___x_3199_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3200_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
lean_ctor_set(v___x_3200_, 1, v___x_3198_);
lean_ctor_set(v___x_3200_, 2, v___x_3196_);
lean_ctor_set(v___x_3200_, 3, v___x_3196_);
lean_ctor_set_usize(v___x_3200_, 4, v___x_3195_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; lean_object* v_infoState_3206_; uint8_t v_enabled_3207_; 
v___x_3205_ = lean_st_ref_get(v___y_3203_);
v_infoState_3206_ = lean_ctor_get(v___x_3205_, 8);
lean_inc_ref(v_infoState_3206_);
lean_dec(v___x_3205_);
v_enabled_3207_ = lean_ctor_get_uint8(v_infoState_3206_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3206_);
if (v_enabled_3207_ == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_dec_ref(v_t_3201_);
v___x_3208_ = lean_box(0);
v___x_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
return v___x_3209_;
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3211_, 0, v_t_3201_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3211_, v___y_3203_);
return v___x_3212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v___y_3219_);
return v___x_3220_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3223_ = l_Lean_stringToMessageData(v___x_3222_);
return v___x_3223_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3226_ = l_Lean_stringToMessageData(v___x_3225_);
return v___x_3226_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3276_ = l_Lean_Json_mkObj(v___x_3275_);
return v___x_3276_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3277_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v___x_3277_);
return v___x_3279_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = lean_box(0);
v___x_3281_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v___x_3280_);
return v___x_3282_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3286_ = l_Lean_MessageData_ofFormat(v___x_3285_);
return v___x_3286_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3289_ = l_Lean_stringToMessageData(v___x_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3291_, uint8_t v_forceList_3292_, lean_object* v_codeActionPrefix_x3f_3293_, lean_object* v_ref_3294_, lean_object* v_as_3295_, size_t v_sz_3296_, size_t v_i_3297_, lean_object* v_b_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_a_3303_; lean_object* v___y_3308_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3319_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; uint8_t v___x_3347_; 
v___x_3347_ = lean_usize_dec_lt(v_i_3297_, v_sz_3296_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; 
lean_dec(v_ref_3294_);
lean_dec(v_codeActionPrefix_x3f_3293_);
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v_b_3298_);
return v___x_3348_;
}
else
{
lean_object* v_a_3349_; lean_object* v_span_x3f_3350_; lean_object* v___x_3351_; lean_object* v___y_3353_; uint8_t v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3386_; uint8_t v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; uint8_t v___y_3439_; lean_object* v___y_3442_; uint8_t v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; uint8_t v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3452_; uint8_t v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v_postInfo_x3f_3456_; uint8_t v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3463_; uint8_t v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; uint8_t v___y_3467_; lean_object* v___y_3468_; lean_object* v_edits_3469_; lean_object* v___y_3475_; lean_object* v___y_3476_; uint8_t v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v_stop_3480_; lean_object* v___y_3481_; uint8_t v___y_3482_; lean_object* v___y_3483_; lean_object* v_edits_3484_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; uint8_t v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; uint8_t v___y_3502_; lean_object* v___y_3503_; lean_object* v_edits_3504_; lean_object* v___y_3505_; lean_object* v___x_3531_; lean_object* v___y_3533_; uint8_t v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3579_; uint8_t v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; uint8_t v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3597_; 
v_a_3349_ = lean_array_uget_borrowed(v_as_3295_, v_i_3297_);
v_span_x3f_3350_ = lean_ctor_get(v_a_3349_, 1);
v___x_3351_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3531_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3350_) == 0)
{
lean_inc(v_ref_3294_);
v___y_3597_ = v_ref_3294_;
goto v___jp_3596_;
}
else
{
lean_object* v_val_3618_; 
v_val_3618_ = lean_ctor_get(v_span_x3f_3350_, 0);
lean_inc(v_val_3618_);
v___y_3597_ = v_val_3618_;
goto v___jp_3596_;
}
v___jp_3352_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___f_3373_; 
lean_inc_ref(v___y_3358_);
v___x_3359_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3358_);
v___x_3360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
lean_ctor_set(v___x_3361_, 1, v___x_3359_);
v___x_3362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___y_3353_);
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3362_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3366_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3356_);
v___x_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3365_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = lean_box(0);
v___x_3369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3364_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3361_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = l_Lean_Json_mkObj(v___x_3371_);
lean_dec_ref_known(v___x_3371_, 2);
v___f_3373_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3373_, 0, v___x_3372_);
if (v___y_3354_ == 0)
{
lean_object* v___x_3374_; 
v___x_3374_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3358_);
v___y_3327_ = v___y_3355_;
v___y_3328_ = v___y_3357_;
v___y_3329_ = v___f_3373_;
v___y_3330_ = v___x_3374_;
goto v___jp_3326_;
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; 
v___x_3375_ = lean_unsigned_to_nat(0u);
v___x_3376_ = lean_array_get_size(v___y_3358_);
v___x_3377_ = lean_nat_dec_lt(v___x_3375_, v___x_3376_);
if (v___x_3377_ == 0)
{
lean_dec_ref(v___y_3358_);
v___y_3327_ = v___y_3355_;
v___y_3328_ = v___y_3357_;
v___y_3329_ = v___f_3373_;
v___y_3330_ = v___x_3351_;
goto v___jp_3326_;
}
else
{
uint8_t v___x_3378_; 
v___x_3378_ = lean_nat_dec_le(v___x_3376_, v___x_3376_);
if (v___x_3378_ == 0)
{
if (v___x_3377_ == 0)
{
lean_dec_ref(v___y_3358_);
v___y_3327_ = v___y_3355_;
v___y_3328_ = v___y_3357_;
v___y_3329_ = v___f_3373_;
v___y_3330_ = v___x_3351_;
goto v___jp_3326_;
}
else
{
size_t v___x_3379_; size_t v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = ((size_t)0ULL);
v___x_3380_ = lean_usize_of_nat(v___x_3376_);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3358_, v___x_3379_, v___x_3380_, v___x_3351_);
lean_dec_ref(v___y_3358_);
v___y_3327_ = v___y_3355_;
v___y_3328_ = v___y_3357_;
v___y_3329_ = v___f_3373_;
v___y_3330_ = v___x_3381_;
goto v___jp_3326_;
}
}
else
{
size_t v___x_3382_; size_t v___x_3383_; lean_object* v___x_3384_; 
v___x_3382_ = ((size_t)0ULL);
v___x_3383_ = lean_usize_of_nat(v___x_3376_);
v___x_3384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3358_, v___x_3382_, v___x_3383_, v___x_3351_);
lean_dec_ref(v___y_3358_);
v___y_3327_ = v___y_3355_;
v___y_3328_ = v___y_3357_;
v___y_3329_ = v___f_3373_;
v___y_3330_ = v___x_3384_;
goto v___jp_3326_;
}
}
}
}
v___jp_3385_:
{
if (lean_obj_tag(v___y_3392_) == 0)
{
lean_object* v___x_3394_; uint64_t v_javascriptHash_3395_; lean_object* v_suggestion_3396_; lean_object* v_messageData_x3f_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___f_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec_ref(v___y_3393_);
v___x_3394_ = ((lean_object*)(l_Lean_Meta_Hint_textInsertionWidget));
v_javascriptHash_3395_ = lean_ctor_get_uint64(v___x_3394_, sizeof(void*)*1);
v_suggestion_3396_ = lean_ctor_get(v___y_3390_, 0);
lean_inc_ref(v_suggestion_3396_);
v_messageData_x3f_3397_ = lean_ctor_get(v___y_3390_, 4);
lean_inc(v_messageData_x3f_3397_);
lean_dec_ref(v___y_3390_);
v___x_3398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3400_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3389_);
v___x_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3403_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___y_3386_);
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3402_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
v___x_3405_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3401_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = l_Lean_Json_mkObj(v___x_3407_);
lean_dec_ref_known(v___x_3407_, 2);
v___f_3409_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3409_, 0, v___x_3408_);
v___x_3410_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3410_, 0, v___x_3398_);
lean_ctor_set(v___x_3410_, 1, v___f_3409_);
lean_ctor_set_uint64(v___x_3410_, sizeof(void*)*2, v_javascriptHash_3395_);
v___x_3411_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3410_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
v___x_3413_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
lean_ctor_set(v___x_3414_, 1, v___x_3412_);
v___x_3415_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3414_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = l_Lean_stringToMessageData(v___y_3391_);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
if (lean_obj_tag(v_messageData_x3f_3397_) == 0)
{
if (lean_obj_tag(v_suggestion_3396_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3420_; 
v_a_3419_ = lean_ctor_get(v_suggestion_3396_, 1);
lean_inc(v_a_3419_);
lean_dec_ref_known(v_suggestion_3396_, 2);
v___x_3420_ = l_Lean_MessageData_ofSyntax(v_a_3419_);
v___y_3312_ = v___x_3418_;
v___y_3313_ = v___y_3388_;
v___y_3314_ = v___x_3420_;
goto v___jp_3311_;
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3429_; 
v_a_3421_ = lean_ctor_get(v_suggestion_3396_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_suggestion_3396_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3423_ = v_suggestion_3396_;
v_isShared_3424_ = v_isSharedCheck_3429_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v_suggestion_3396_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3429_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 3);
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_MessageData_ofFormat(v___x_3426_);
v___y_3312_ = v___x_3418_;
v___y_3313_ = v___y_3388_;
v___y_3314_ = v___x_3427_;
goto v___jp_3311_;
}
}
}
}
else
{
lean_object* v_val_3430_; 
lean_dec_ref(v_suggestion_3396_);
v_val_3430_ = lean_ctor_get(v_messageData_x3f_3397_, 0);
lean_inc(v_val_3430_);
lean_dec_ref_known(v_messageData_x3f_3397_, 1);
v___y_3312_ = v___x_3418_;
v___y_3313_ = v___y_3388_;
v___y_3314_ = v_val_3430_;
goto v___jp_3311_;
}
}
else
{
lean_dec_ref_known(v___y_3392_, 1);
lean_dec_ref(v___y_3390_);
v___y_3353_ = v___y_3386_;
v___y_3354_ = v___y_3387_;
v___y_3355_ = v___y_3388_;
v___y_3356_ = v___y_3389_;
v___y_3357_ = v___y_3391_;
v___y_3358_ = v___y_3393_;
goto v___jp_3352_;
}
}
v___jp_3431_:
{
if (v___y_3439_ == 0)
{
lean_object* v_messageData_x3f_3440_; 
v_messageData_x3f_3440_ = lean_ctor_get(v___y_3435_, 4);
if (lean_obj_tag(v_messageData_x3f_3440_) == 0)
{
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3435_);
v___y_3353_ = v___y_3432_;
v___y_3354_ = v___y_3439_;
v___y_3355_ = v___y_3433_;
v___y_3356_ = v___y_3434_;
v___y_3357_ = v___y_3436_;
v___y_3358_ = v___y_3438_;
goto v___jp_3352_;
}
else
{
v___y_3386_ = v___y_3432_;
v___y_3387_ = v___y_3439_;
v___y_3388_ = v___y_3433_;
v___y_3389_ = v___y_3434_;
v___y_3390_ = v___y_3435_;
v___y_3391_ = v___y_3436_;
v___y_3392_ = v___y_3437_;
v___y_3393_ = v___y_3438_;
goto v___jp_3385_;
}
}
else
{
v___y_3386_ = v___y_3432_;
v___y_3387_ = v___y_3439_;
v___y_3388_ = v___y_3433_;
v___y_3389_ = v___y_3434_;
v___y_3390_ = v___y_3435_;
v___y_3391_ = v___y_3436_;
v___y_3392_ = v___y_3437_;
v___y_3393_ = v___y_3438_;
goto v___jp_3385_;
}
}
v___jp_3441_:
{
if (v___y_3447_ == 4)
{
v___y_3432_ = v___y_3442_;
v___y_3433_ = v___y_3450_;
v___y_3434_ = v___y_3444_;
v___y_3435_ = v___y_3446_;
v___y_3436_ = v___y_3445_;
v___y_3437_ = v___y_3448_;
v___y_3438_ = v___y_3449_;
v___y_3439_ = v___x_3347_;
goto v___jp_3431_;
}
else
{
v___y_3432_ = v___y_3442_;
v___y_3433_ = v___y_3450_;
v___y_3434_ = v___y_3444_;
v___y_3435_ = v___y_3446_;
v___y_3436_ = v___y_3445_;
v___y_3437_ = v___y_3448_;
v___y_3438_ = v___y_3449_;
v___y_3439_ = v___y_3443_;
goto v___jp_3431_;
}
}
v___jp_3451_:
{
if (lean_obj_tag(v_postInfo_x3f_3456_) == 0)
{
v___y_3442_ = v___y_3452_;
v___y_3443_ = v___y_3453_;
v___y_3444_ = v___y_3454_;
v___y_3445_ = v___y_3460_;
v___y_3446_ = v___y_3455_;
v___y_3447_ = v___y_3457_;
v___y_3448_ = v___y_3458_;
v___y_3449_ = v___y_3459_;
v___y_3450_ = v___x_3351_;
goto v___jp_3441_;
}
else
{
lean_object* v_val_3461_; 
v_val_3461_ = lean_ctor_get(v_postInfo_x3f_3456_, 0);
lean_inc(v_val_3461_);
lean_dec_ref_known(v_postInfo_x3f_3456_, 1);
v___y_3442_ = v___y_3452_;
v___y_3443_ = v___y_3453_;
v___y_3444_ = v___y_3454_;
v___y_3445_ = v___y_3460_;
v___y_3446_ = v___y_3455_;
v___y_3447_ = v___y_3457_;
v___y_3448_ = v___y_3458_;
v___y_3449_ = v___y_3459_;
v___y_3450_ = v_val_3461_;
goto v___jp_3441_;
}
}
v___jp_3462_:
{
lean_object* v_preInfo_x3f_3470_; 
v_preInfo_x3f_3470_ = lean_ctor_get(v___y_3466_, 1);
if (lean_obj_tag(v_preInfo_x3f_3470_) == 0)
{
lean_object* v_postInfo_x3f_3471_; 
v_postInfo_x3f_3471_ = lean_ctor_get(v___y_3466_, 2);
lean_inc(v_postInfo_x3f_3471_);
v___y_3452_ = v___y_3463_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3465_;
v___y_3455_ = v___y_3466_;
v_postInfo_x3f_3456_ = v_postInfo_x3f_3471_;
v___y_3457_ = v___y_3467_;
v___y_3458_ = v___y_3468_;
v___y_3459_ = v_edits_3469_;
v___y_3460_ = v___x_3351_;
goto v___jp_3451_;
}
else
{
lean_object* v_postInfo_x3f_3472_; lean_object* v_val_3473_; 
v_postInfo_x3f_3472_ = lean_ctor_get(v___y_3466_, 2);
lean_inc(v_postInfo_x3f_3472_);
v_val_3473_ = lean_ctor_get(v_preInfo_x3f_3470_, 0);
lean_inc(v_val_3473_);
v___y_3452_ = v___y_3463_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3465_;
v___y_3455_ = v___y_3466_;
v_postInfo_x3f_3456_ = v_postInfo_x3f_3472_;
v___y_3457_ = v___y_3467_;
v___y_3458_ = v___y_3468_;
v___y_3459_ = v_edits_3469_;
v___y_3460_ = v_val_3473_;
goto v___jp_3451_;
}
}
v___jp_3474_:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3485_ = lean_unsigned_to_nat(1u);
v___x_3486_ = lean_nat_add(v___y_3476_, v___x_3485_);
v___x_3487_ = lean_nat_dec_le(v___x_3486_, v_stop_3480_);
lean_dec(v___x_3486_);
if (v___x_3487_ == 0)
{
lean_dec(v_stop_3480_);
lean_dec(v___y_3476_);
v___y_3463_ = v___y_3475_;
v___y_3464_ = v___y_3477_;
v___y_3465_ = v___y_3479_;
v___y_3466_ = v___y_3481_;
v___y_3467_ = v___y_3482_;
v___y_3468_ = v___y_3483_;
v_edits_3469_ = v_edits_3484_;
goto v___jp_3462_;
}
else
{
lean_object* v_source_3488_; uint8_t v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v_source_3488_ = lean_ctor_get(v___y_3478_, 0);
v___x_3489_ = 2;
v___x_3490_ = lean_string_utf8_extract(v_source_3488_, v___y_3476_, v_stop_3480_);
lean_dec(v_stop_3480_);
lean_dec(v___y_3476_);
v___x_3491_ = lean_box(v___x_3489_);
v___x_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
lean_ctor_set(v___x_3492_, 1, v___x_3490_);
v___x_3493_ = lean_array_push(v_edits_3484_, v___x_3492_);
v___y_3463_ = v___y_3475_;
v___y_3464_ = v___y_3477_;
v___y_3465_ = v___y_3479_;
v___y_3466_ = v___y_3481_;
v___y_3467_ = v___y_3482_;
v___y_3468_ = v___y_3483_;
v_edits_3469_ = v___x_3493_;
goto v___jp_3462_;
}
}
v___jp_3494_:
{
if (lean_obj_tag(v___y_3503_) == 0)
{
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3496_);
lean_dec(v___y_3495_);
v___y_3463_ = v___y_3497_;
v___y_3464_ = v___y_3498_;
v___y_3465_ = v___y_3499_;
v___y_3466_ = v___y_3500_;
v___y_3467_ = v___y_3502_;
v___y_3468_ = v___y_3503_;
v_edits_3469_ = v_edits_3504_;
goto v___jp_3462_;
}
else
{
lean_object* v_val_3506_; lean_object* v___x_3507_; 
v_val_3506_ = lean_ctor_get(v___y_3503_, 0);
v___x_3507_ = l_Lean_Syntax_getRange_x3f(v_val_3506_, v___y_3498_);
if (lean_obj_tag(v___x_3507_) == 1)
{
lean_object* v_val_3508_; uint8_t v___x_3509_; 
v_val_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_val_3508_);
lean_dec_ref_known(v___x_3507_, 1);
v___x_3509_ = l_Lean_Syntax_Range_includes(v_val_3508_, v___y_3501_, v___y_3498_, v___y_3498_);
lean_dec_ref(v___y_3501_);
if (v___x_3509_ == 0)
{
lean_dec(v_val_3508_);
lean_dec(v___y_3496_);
lean_dec(v___y_3495_);
v___y_3463_ = v___y_3497_;
v___y_3464_ = v___y_3498_;
v___y_3465_ = v___y_3499_;
v___y_3466_ = v___y_3500_;
v___y_3467_ = v___y_3502_;
v___y_3468_ = v___y_3503_;
v_edits_3469_ = v_edits_3504_;
goto v___jp_3462_;
}
else
{
lean_object* v_toCold_3510_; lean_object* v_fileMap_3511_; lean_object* v_start_3512_; lean_object* v_stop_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3530_; 
v_toCold_3510_ = lean_ctor_get(v___y_3505_, 0);
v_fileMap_3511_ = lean_ctor_get(v_toCold_3510_, 1);
v_start_3512_ = lean_ctor_get(v_val_3508_, 0);
v_stop_3513_ = lean_ctor_get(v_val_3508_, 1);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_val_3508_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3515_ = v_val_3508_;
v_isShared_3516_ = v_isSharedCheck_3530_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_stop_3513_);
lean_inc(v_start_3512_);
lean_dec(v_val_3508_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3530_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; uint8_t v___x_3519_; 
v___x_3517_ = lean_unsigned_to_nat(1u);
v___x_3518_ = lean_nat_add(v_start_3512_, v___x_3517_);
v___x_3519_ = lean_nat_dec_le(v___x_3518_, v___y_3495_);
lean_dec(v___x_3518_);
if (v___x_3519_ == 0)
{
lean_del_object(v___x_3515_);
lean_dec(v_start_3512_);
lean_dec(v___y_3495_);
v___y_3475_ = v___y_3497_;
v___y_3476_ = v___y_3496_;
v___y_3477_ = v___y_3498_;
v___y_3478_ = v_fileMap_3511_;
v___y_3479_ = v___y_3499_;
v_stop_3480_ = v_stop_3513_;
v___y_3481_ = v___y_3500_;
v___y_3482_ = v___y_3502_;
v___y_3483_ = v___y_3503_;
v_edits_3484_ = v_edits_3504_;
goto v___jp_3474_;
}
else
{
lean_object* v_source_3520_; uint8_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3525_; 
v_source_3520_ = lean_ctor_get(v_fileMap_3511_, 0);
v___x_3521_ = 2;
v___x_3522_ = lean_string_utf8_extract(v_source_3520_, v_start_3512_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec(v_start_3512_);
v___x_3523_ = lean_box(v___x_3521_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 1, v___x_3522_);
lean_ctor_set(v___x_3515_, 0, v___x_3523_);
v___x_3525_ = v___x_3515_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3523_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v___x_3522_);
v___x_3525_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3526_ = lean_mk_empty_array_with_capacity(v___x_3517_);
v___x_3527_ = lean_array_push(v___x_3526_, v___x_3525_);
v___x_3528_ = l_Array_append___redArg(v___x_3527_, v_edits_3504_);
lean_dec_ref(v_edits_3504_);
v___y_3475_ = v___y_3497_;
v___y_3476_ = v___y_3496_;
v___y_3477_ = v___y_3498_;
v___y_3478_ = v_fileMap_3511_;
v___y_3479_ = v___y_3499_;
v_stop_3480_ = v_stop_3513_;
v___y_3481_ = v___y_3500_;
v___y_3482_ = v___y_3502_;
v___y_3483_ = v___y_3503_;
v_edits_3484_ = v___x_3528_;
goto v___jp_3474_;
}
}
}
}
}
else
{
lean_dec(v___x_3507_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3496_);
lean_dec(v___y_3495_);
v___y_3463_ = v___y_3497_;
v___y_3464_ = v___y_3498_;
v___y_3465_ = v___y_3499_;
v___y_3466_ = v___y_3500_;
v___y_3467_ = v___y_3502_;
v___y_3468_ = v___y_3503_;
v_edits_3469_ = v_edits_3504_;
goto v___jp_3462_;
}
}
}
v___jp_3532_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
lean_inc_ref(v___y_3537_);
v___x_3543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3543_, 0, v___y_3535_);
lean_ctor_set(v___x_3543_, 1, v___y_3542_);
lean_ctor_set(v___x_3543_, 2, v___y_3537_);
v___x_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3531_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___y_3541_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
v___x_3547_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3546_, v___y_3299_, v___y_3300_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_messageData_x3f_3548_; 
lean_dec_ref_known(v___x_3547_, 1);
v_messageData_x3f_3548_ = lean_ctor_get(v___y_3537_, 4);
if (lean_obj_tag(v_messageData_x3f_3548_) == 1)
{
lean_object* v_start_3549_; lean_object* v_stop_3550_; lean_object* v_val_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_start_3549_ = lean_ctor_get(v___y_3539_, 0);
lean_inc(v_start_3549_);
v_stop_3550_ = lean_ctor_get(v___y_3539_, 1);
lean_inc(v_stop_3550_);
v_val_3551_ = lean_ctor_get(v_messageData_x3f_3548_, 0);
v___x_3552_ = lean_box(0);
lean_inc(v_val_3551_);
v___x_3553_ = l_Lean_MessageData_format(v_val_3551_, v___x_3552_);
v___x_3554_ = 0;
v___x_3555_ = l_Std_Format_defWidth;
v___x_3556_ = lean_unsigned_to_nat(0u);
v___x_3557_ = l_Std_Format_pretty(v___x_3553_, v___x_3555_, v___x_3556_, v___x_3556_);
v___x_3558_ = lean_box(v___x_3554_);
v___x_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
lean_ctor_set(v___x_3559_, 1, v___x_3557_);
v___x_3560_ = lean_unsigned_to_nat(1u);
v___x_3561_ = lean_mk_empty_array_with_capacity(v___x_3560_);
v___x_3562_ = lean_array_push(v___x_3561_, v___x_3559_);
v___y_3495_ = v_start_3549_;
v___y_3496_ = v_stop_3550_;
v___y_3497_ = v___y_3533_;
v___y_3498_ = v___y_3534_;
v___y_3499_ = v___y_3536_;
v___y_3500_ = v___y_3537_;
v___y_3501_ = v___y_3539_;
v___y_3502_ = v___y_3538_;
v___y_3503_ = v___y_3540_;
v_edits_3504_ = v___x_3562_;
v___y_3505_ = v___y_3299_;
goto v___jp_3494_;
}
else
{
lean_object* v_toCold_3563_; lean_object* v_fileMap_3564_; lean_object* v_start_3565_; lean_object* v_stop_3566_; lean_object* v_source_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_toCold_3563_ = lean_ctor_get(v___y_3299_, 0);
v_fileMap_3564_ = lean_ctor_get(v_toCold_3563_, 1);
v_start_3565_ = lean_ctor_get(v___y_3539_, 0);
lean_inc(v_start_3565_);
v_stop_3566_ = lean_ctor_get(v___y_3539_, 1);
lean_inc(v_stop_3566_);
v_source_3567_ = lean_ctor_get(v_fileMap_3564_, 0);
v___x_3568_ = lean_string_utf8_extract(v_source_3567_, v_start_3565_, v_stop_3566_);
lean_inc_ref(v___y_3533_);
v___x_3569_ = l_Lean_Meta_Hint_readableDiff(v___x_3568_, v___y_3533_, v___y_3538_);
v___y_3495_ = v_start_3565_;
v___y_3496_ = v_stop_3566_;
v___y_3497_ = v___y_3533_;
v___y_3498_ = v___y_3534_;
v___y_3499_ = v___y_3536_;
v___y_3500_ = v___y_3537_;
v___y_3501_ = v___y_3539_;
v___y_3502_ = v___y_3538_;
v___y_3503_ = v___y_3540_;
v_edits_3504_ = v___x_3569_;
v___y_3505_ = v___y_3299_;
goto v___jp_3494_;
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec_ref(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v_b_3298_);
lean_dec(v_ref_3294_);
lean_dec(v_codeActionPrefix_x3f_3293_);
v_a_3570_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3547_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3547_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
v___jp_3578_:
{
lean_object* v_toCodeActionTitle_x3f_3588_; lean_object* v___x_3589_; 
v_toCodeActionTitle_x3f_3588_ = lean_ctor_get(v___y_3583_, 5);
v___x_3589_ = l_Lean_Syntax_ofRange(v___y_3587_, v___x_3347_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3588_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3293_) == 0)
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3591_ = lean_string_append(v___x_3590_, v___y_3579_);
v___y_3533_ = v___y_3579_;
v___y_3534_ = v___y_3580_;
v___y_3535_ = v___y_3581_;
v___y_3536_ = v___y_3582_;
v___y_3537_ = v___y_3583_;
v___y_3538_ = v___y_3585_;
v___y_3539_ = v___y_3584_;
v___y_3540_ = v___y_3586_;
v___y_3541_ = v___x_3589_;
v___y_3542_ = v___x_3591_;
goto v___jp_3532_;
}
else
{
lean_object* v_val_3592_; lean_object* v___x_3593_; 
v_val_3592_ = lean_ctor_get(v_codeActionPrefix_x3f_3293_, 0);
lean_inc(v_val_3592_);
v___x_3593_ = lean_string_append(v_val_3592_, v___y_3579_);
v___y_3533_ = v___y_3579_;
v___y_3534_ = v___y_3580_;
v___y_3535_ = v___y_3581_;
v___y_3536_ = v___y_3582_;
v___y_3537_ = v___y_3583_;
v___y_3538_ = v___y_3585_;
v___y_3539_ = v___y_3584_;
v___y_3540_ = v___y_3586_;
v___y_3541_ = v___x_3589_;
v___y_3542_ = v___x_3593_;
goto v___jp_3532_;
}
}
else
{
lean_object* v_val_3594_; lean_object* v___x_3595_; 
v_val_3594_ = lean_ctor_get(v_toCodeActionTitle_x3f_3588_, 0);
lean_inc(v_val_3594_);
lean_inc_ref(v___y_3579_);
v___x_3595_ = lean_apply_1(v_val_3594_, v___y_3579_);
v___y_3533_ = v___y_3579_;
v___y_3534_ = v___y_3580_;
v___y_3535_ = v___y_3581_;
v___y_3536_ = v___y_3582_;
v___y_3537_ = v___y_3583_;
v___y_3538_ = v___y_3585_;
v___y_3539_ = v___y_3584_;
v___y_3540_ = v___y_3586_;
v___y_3541_ = v___x_3589_;
v___y_3542_ = v___x_3595_;
goto v___jp_3532_;
}
}
v___jp_3596_:
{
uint8_t v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = 0;
v___x_3599_ = l_Lean_Syntax_getRange_x3f(v___y_3597_, v___x_3598_);
lean_dec(v___y_3597_);
if (lean_obj_tag(v___x_3599_) == 1)
{
lean_object* v_val_3600_; lean_object* v_toTryThisSuggestion_3601_; lean_object* v_previewSpan_x3f_3602_; uint8_t v_diffGranularity_3603_; lean_object* v___x_3604_; 
v_val_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc_n(v_val_3600_, 2);
lean_dec_ref_known(v___x_3599_, 1);
v_toTryThisSuggestion_3601_ = lean_ctor_get(v_a_3349_, 0);
v_previewSpan_x3f_3602_ = lean_ctor_get(v_a_3349_, 2);
v_diffGranularity_3603_ = lean_ctor_get_uint8(v_a_3349_, sizeof(void*)*3);
lean_inc_ref(v_toTryThisSuggestion_3601_);
v___x_3604_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3601_, v_val_3600_, v___y_3299_, v___y_3300_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v_range_3606_; lean_object* v_newText_3607_; lean_object* v___x_3608_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref_known(v___x_3604_, 1);
v_range_3606_ = lean_ctor_get(v_a_3605_, 0);
lean_inc_ref(v_range_3606_);
v_newText_3607_ = lean_ctor_get(v_a_3605_, 1);
lean_inc_ref(v_newText_3607_);
v___x_3608_ = l_Lean_Syntax_getRange_x3f(v_ref_3294_, v___x_3598_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_inc(v_previewSpan_x3f_3602_);
lean_inc(v_val_3600_);
lean_inc_ref(v_toTryThisSuggestion_3601_);
v___y_3579_ = v_newText_3607_;
v___y_3580_ = v___x_3598_;
v___y_3581_ = v_a_3605_;
v___y_3582_ = v_range_3606_;
v___y_3583_ = v_toTryThisSuggestion_3601_;
v___y_3584_ = v_val_3600_;
v___y_3585_ = v_diffGranularity_3603_;
v___y_3586_ = v_previewSpan_x3f_3602_;
v___y_3587_ = v_val_3600_;
goto v___jp_3578_;
}
else
{
lean_object* v_val_3609_; 
v_val_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_val_3609_);
lean_dec_ref_known(v___x_3608_, 1);
lean_inc(v_previewSpan_x3f_3602_);
lean_inc_ref(v_toTryThisSuggestion_3601_);
v___y_3579_ = v_newText_3607_;
v___y_3580_ = v___x_3598_;
v___y_3581_ = v_a_3605_;
v___y_3582_ = v_range_3606_;
v___y_3583_ = v_toTryThisSuggestion_3601_;
v___y_3584_ = v_val_3600_;
v___y_3585_ = v_diffGranularity_3603_;
v___y_3586_ = v_previewSpan_x3f_3602_;
v___y_3587_ = v_val_3609_;
goto v___jp_3578_;
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec(v_val_3600_);
lean_dec_ref(v_b_3298_);
lean_dec(v_ref_3294_);
lean_dec(v_codeActionPrefix_x3f_3293_);
v_a_3610_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3604_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3604_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_dec(v___x_3599_);
v_a_3303_ = v_b_3298_;
goto v___jp_3302_;
}
}
}
v___jp_3302_:
{
size_t v___x_3304_; size_t v___x_3305_; 
v___x_3304_ = ((size_t)1ULL);
v___x_3305_ = lean_usize_add(v_i_3297_, v___x_3304_);
v_i_3297_ = v___x_3305_;
v_b_3298_ = v_a_3303_;
goto _start;
}
v___jp_3307_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = l_Lean_MessageData_nestD(v___y_3308_);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v_b_3298_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v_a_3303_ = v___x_3310_;
goto v___jp_3302_;
}
v___jp_3311_:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___y_3312_);
lean_ctor_set(v___x_3315_, 1, v___y_3314_);
v___x_3316_ = l_Lean_stringToMessageData(v___y_3313_);
v___x_3317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
v___y_3308_ = v___x_3317_;
goto v___jp_3307_;
}
v___jp_3318_:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3320_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3321_ = lean_unsigned_to_nat(2u);
v___x_3322_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
lean_ctor_set(v___x_3323_, 1, v___y_3319_);
v___x_3324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3321_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3320_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___y_3308_ = v___x_3325_;
goto v___jp_3307_;
}
v___jp_3326_:
{
lean_object* v___x_3331_; uint64_t v_javascriptHash_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v___x_3331_ = ((lean_object*)(l_Lean_Meta_Hint_tryThisDiffWidget));
v_javascriptHash_3332_ = lean_ctor_get_uint64(v___x_3331_, sizeof(void*)*1);
v___x_3333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3334_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
lean_ctor_set(v___x_3334_, 1, v___y_3329_);
lean_ctor_set_uint64(v___x_3334_, sizeof(void*)*2, v_javascriptHash_3332_);
v___x_3335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___y_3330_);
v___x_3336_ = l_Lean_MessageData_ofFormat(v___x_3335_);
v___x_3337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3334_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = l_Lean_stringToMessageData(v___y_3328_);
v___x_3339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
lean_ctor_set(v___x_3339_, 1, v___x_3337_);
v___x_3340_ = l_Lean_stringToMessageData(v___y_3327_);
v___x_3341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3339_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = lean_array_get_size(v_suggestions_3291_);
v___x_3343_ = lean_unsigned_to_nat(1u);
v___x_3344_ = lean_nat_dec_eq(v___x_3342_, v___x_3343_);
if (v___x_3344_ == 0)
{
v___y_3319_ = v___x_3341_;
goto v___jp_3318_;
}
else
{
if (v_forceList_3292_ == 0)
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
lean_ctor_set(v___x_3346_, 1, v___x_3341_);
v___y_3308_ = v___x_3346_;
goto v___jp_3307_;
}
else
{
v___y_3319_ = v___x_3341_;
goto v___jp_3318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3619_, lean_object* v_forceList_3620_, lean_object* v_codeActionPrefix_x3f_3621_, lean_object* v_ref_3622_, lean_object* v_as_3623_, lean_object* v_sz_3624_, lean_object* v_i_3625_, lean_object* v_b_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
uint8_t v_forceList_boxed_3630_; size_t v_sz_boxed_3631_; size_t v_i_boxed_3632_; lean_object* v_res_3633_; 
v_forceList_boxed_3630_ = lean_unbox(v_forceList_3620_);
v_sz_boxed_3631_ = lean_unbox_usize(v_sz_3624_);
lean_dec(v_sz_3624_);
v_i_boxed_3632_ = lean_unbox_usize(v_i_3625_);
lean_dec(v_i_3625_);
v_res_3633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3619_, v_forceList_boxed_3630_, v_codeActionPrefix_x3f_3621_, v_ref_3622_, v_as_3623_, v_sz_boxed_3631_, v_i_boxed_3632_, v_b_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec_ref(v_as_3623_);
lean_dec_ref(v_suggestions_3619_);
return v_res_3633_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3634_; lean_object* v_msg_3635_; 
v___x_3634_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3635_ = l_Lean_stringToMessageData(v___x_3634_);
return v_msg_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3636_, lean_object* v_ref_3637_, lean_object* v_codeActionPrefix_x3f_3638_, uint8_t v_forceList_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v_msg_3643_; size_t v_sz_3644_; size_t v___x_3645_; lean_object* v___x_3646_; 
v_msg_3643_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3644_ = lean_array_size(v_suggestions_3636_);
v___x_3645_ = ((size_t)0ULL);
v___x_3646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3636_, v_forceList_3639_, v_codeActionPrefix_x3f_3638_, v_ref_3637_, v_suggestions_3636_, v_sz_3644_, v___x_3645_, v_msg_3643_, v_a_3640_, v_a_3641_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3647_, lean_object* v_ref_3648_, lean_object* v_codeActionPrefix_x3f_3649_, lean_object* v_forceList_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
uint8_t v_forceList_boxed_3654_; lean_object* v_res_3655_; 
v_forceList_boxed_3654_ = lean_unbox(v_forceList_3650_);
v_res_3655_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3647_, v_ref_3648_, v_codeActionPrefix_x3f_3649_, v_forceList_boxed_3654_, v_a_3651_, v_a_3652_);
lean_dec(v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec_ref(v_suggestions_3647_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v___x_3660_; 
v___x_3660_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3656_, v___y_3658_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3661_, v___y_3662_, v___y_3663_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
return v_res_3665_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3671_ = l_Lean_stringToMessageData(v___x_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3672_, lean_object* v_suggestions_3673_, lean_object* v_ref_x3f_3674_, lean_object* v_codeActionPrefix_x3f_3675_, uint8_t v_forceList_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v___y_3681_; 
if (lean_obj_tag(v_ref_x3f_3674_) == 0)
{
lean_object* v_ref_3696_; 
v_ref_3696_ = lean_ctor_get(v_a_3677_, 2);
lean_inc(v_ref_3696_);
v___y_3681_ = v_ref_3696_;
goto v___jp_3680_;
}
else
{
lean_object* v_val_3697_; 
v_val_3697_ = lean_ctor_get(v_ref_x3f_3674_, 0);
lean_inc(v_val_3697_);
lean_dec_ref_known(v_ref_x3f_3674_, 1);
v___y_3681_ = v_val_3697_;
goto v___jp_3680_;
}
v___jp_3680_:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3673_, v___y_3681_, v_codeActionPrefix_x3f_3675_, v_forceList_3676_, v_a_3677_, v_a_3678_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3695_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3695_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3695_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3687_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3688_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
lean_ctor_set(v___x_3689_, 1, v_hint_3672_);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
lean_ctor_set(v___x_3690_, 1, v_a_3683_);
v___x_3691_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3687_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 0, v___x_3691_);
v___x_3693_ = v___x_3685_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
else
{
lean_dec_ref(v_hint_3672_);
return v___x_3682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3698_, lean_object* v_suggestions_3699_, lean_object* v_ref_x3f_3700_, lean_object* v_codeActionPrefix_x3f_3701_, lean_object* v_forceList_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
uint8_t v_forceList_boxed_3706_; lean_object* v_res_3707_; 
v_forceList_boxed_3706_ = lean_unbox(v_forceList_3702_);
v_res_3707_ = l_Lean_MessageData_hint(v_hint_3698_, v_suggestions_3699_, v_ref_x3f_3700_, v_codeActionPrefix_x3f_3701_, v_forceList_boxed_3706_, v_a_3703_, v_a_3704_);
lean_dec(v_a_3704_);
lean_dec_ref(v_a_3703_);
lean_dec_ref(v_suggestions_3699_);
return v_res_3707_;
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
