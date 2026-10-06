// Lean compiler output
// Module: Lean.Data.Html.Printer
// Imports: public import Lean.Data.Html.Basic import Init.Data.String.Modify import Init.Data.String.Search import Init.Data.Array.BinSearch
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
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedHtml_default;
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Html_isEmpty(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static const lean_string_object l_Lean_Html_voidElements___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "area"};
static const lean_object* l_Lean_Html_voidElements___closed__0 = (const lean_object*)&l_Lean_Html_voidElements___closed__0_value;
static const lean_string_object l_Lean_Html_voidElements___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "base"};
static const lean_object* l_Lean_Html_voidElements___closed__1 = (const lean_object*)&l_Lean_Html_voidElements___closed__1_value;
static const lean_string_object l_Lean_Html_voidElements___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "br"};
static const lean_object* l_Lean_Html_voidElements___closed__2 = (const lean_object*)&l_Lean_Html_voidElements___closed__2_value;
static const lean_string_object l_Lean_Html_voidElements___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "col"};
static const lean_object* l_Lean_Html_voidElements___closed__3 = (const lean_object*)&l_Lean_Html_voidElements___closed__3_value;
static const lean_string_object l_Lean_Html_voidElements___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "embed"};
static const lean_object* l_Lean_Html_voidElements___closed__4 = (const lean_object*)&l_Lean_Html_voidElements___closed__4_value;
static const lean_string_object l_Lean_Html_voidElements___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "hr"};
static const lean_object* l_Lean_Html_voidElements___closed__5 = (const lean_object*)&l_Lean_Html_voidElements___closed__5_value;
static const lean_string_object l_Lean_Html_voidElements___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "img"};
static const lean_object* l_Lean_Html_voidElements___closed__6 = (const lean_object*)&l_Lean_Html_voidElements___closed__6_value;
static const lean_string_object l_Lean_Html_voidElements___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "input"};
static const lean_object* l_Lean_Html_voidElements___closed__7 = (const lean_object*)&l_Lean_Html_voidElements___closed__7_value;
static const lean_string_object l_Lean_Html_voidElements___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "link"};
static const lean_object* l_Lean_Html_voidElements___closed__8 = (const lean_object*)&l_Lean_Html_voidElements___closed__8_value;
static const lean_string_object l_Lean_Html_voidElements___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Html_voidElements___closed__9 = (const lean_object*)&l_Lean_Html_voidElements___closed__9_value;
static const lean_string_object l_Lean_Html_voidElements___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "param"};
static const lean_object* l_Lean_Html_voidElements___closed__10 = (const lean_object*)&l_Lean_Html_voidElements___closed__10_value;
static const lean_string_object l_Lean_Html_voidElements___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_Lean_Html_voidElements___closed__11 = (const lean_object*)&l_Lean_Html_voidElements___closed__11_value;
static const lean_string_object l_Lean_Html_voidElements___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "track"};
static const lean_object* l_Lean_Html_voidElements___closed__12 = (const lean_object*)&l_Lean_Html_voidElements___closed__12_value;
static const lean_string_object l_Lean_Html_voidElements___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "wbr"};
static const lean_object* l_Lean_Html_voidElements___closed__13 = (const lean_object*)&l_Lean_Html_voidElements___closed__13_value;
static const lean_array_object l_Lean_Html_voidElements___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*14, .m_other = 0, .m_tag = 246}, .m_size = 14, .m_capacity = 14, .m_data = {((lean_object*)&l_Lean_Html_voidElements___closed__0_value),((lean_object*)&l_Lean_Html_voidElements___closed__1_value),((lean_object*)&l_Lean_Html_voidElements___closed__2_value),((lean_object*)&l_Lean_Html_voidElements___closed__3_value),((lean_object*)&l_Lean_Html_voidElements___closed__4_value),((lean_object*)&l_Lean_Html_voidElements___closed__5_value),((lean_object*)&l_Lean_Html_voidElements___closed__6_value),((lean_object*)&l_Lean_Html_voidElements___closed__7_value),((lean_object*)&l_Lean_Html_voidElements___closed__8_value),((lean_object*)&l_Lean_Html_voidElements___closed__9_value),((lean_object*)&l_Lean_Html_voidElements___closed__10_value),((lean_object*)&l_Lean_Html_voidElements___closed__11_value),((lean_object*)&l_Lean_Html_voidElements___closed__12_value),((lean_object*)&l_Lean_Html_voidElements___closed__13_value)}};
static const lean_object* l_Lean_Html_voidElements___closed__14 = (const lean_object*)&l_Lean_Html_voidElements___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Html_voidElements = (const lean_object*)&l_Lean_Html_voidElements___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushHtml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushStr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popKind___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popHtml_x21(lean_object*);
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "&"};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "&amp;"};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__0_value;
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "&quot;"};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "&lt;"};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__0_value;
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "&gt;"};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0;
static lean_once_cell_t l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__1;
static lean_once_cell_t l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2;
static lean_once_cell_t l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__3;
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__4 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__4_value;
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=\""};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__5 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__5_value;
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "</"};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__6 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__6_value;
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "/>"};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__7 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Html_render___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_render___closed__0 = (const lean_object*)&l_Lean_Html_render___closed__0_value;
static const lean_array_object l_Lean_Html_render___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Html_render___closed__1 = (const lean_object*)&l_Lean_Html_render___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_render(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl(uint8_t v_x_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_box(v_x_46_);
v___x_48_ = lean_obj_tag_nat(v___x_47_);
lean_dec(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl___boxed(lean_object* v_x_49_){
_start:
{
uint8_t v_x_4__boxed_50_; lean_object* v_res_51_; 
v_x_4__boxed_50_ = lean_unbox(v_x_49_);
v_res_51_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl(v_x_4__boxed_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___redArg(lean_object* v_k_52_){
_start:
{
lean_inc(v_k_52_);
return v_k_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___redArg___boxed(lean_object* v_k_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___redArg(v_k_53_);
lean_dec(v_k_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim(lean_object* v_motive_55_, lean_object* v_ctorIdx_56_, uint8_t v_t_57_, lean_object* v_h_58_, lean_object* v_k_59_){
_start:
{
lean_inc(v_k_59_);
return v_k_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___boxed(lean_object* v_motive_60_, lean_object* v_ctorIdx_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_k_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim(v_motive_60_, v_ctorIdx_61_, v_t_boxed_65_, v_h_63_, v_k_64_);
lean_dec(v_k_64_);
lean_dec(v_ctorIdx_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___redArg(lean_object* v_html_67_){
_start:
{
lean_inc(v_html_67_);
return v_html_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___redArg___boxed(lean_object* v_html_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___redArg(v_html_68_);
lean_dec(v_html_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim(lean_object* v_motive_70_, uint8_t v_t_71_, lean_object* v_h_72_, lean_object* v_html_73_){
_start:
{
lean_inc(v_html_73_);
return v_html_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_html_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_html_77_);
lean_dec(v_html_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___redArg(lean_object* v_attr_80_){
_start:
{
lean_inc(v_attr_80_);
return v_attr_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___redArg___boxed(lean_object* v_attr_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___redArg(v_attr_81_);
lean_dec(v_attr_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim(lean_object* v_motive_83_, uint8_t v_t_84_, lean_object* v_h_85_, lean_object* v_attr_86_){
_start:
{
lean_inc(v_attr_86_);
return v_attr_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___boxed(lean_object* v_motive_87_, lean_object* v_t_88_, lean_object* v_h_89_, lean_object* v_attr_90_){
_start:
{
uint8_t v_t_boxed_91_; lean_object* v_res_92_; 
v_t_boxed_91_ = lean_unbox(v_t_88_);
v_res_92_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim(v_motive_87_, v_t_boxed_91_, v_h_89_, v_attr_90_);
lean_dec(v_attr_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___redArg(lean_object* v_endAttrs_93_){
_start:
{
lean_inc(v_endAttrs_93_);
return v_endAttrs_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___redArg___boxed(lean_object* v_endAttrs_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___redArg(v_endAttrs_94_);
lean_dec(v_endAttrs_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim(lean_object* v_motive_96_, uint8_t v_t_97_, lean_object* v_h_98_, lean_object* v_endAttrs_99_){
_start:
{
lean_inc(v_endAttrs_99_);
return v_endAttrs_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___boxed(lean_object* v_motive_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_endAttrs_103_){
_start:
{
uint8_t v_t_boxed_104_; lean_object* v_res_105_; 
v_t_boxed_104_ = lean_unbox(v_t_101_);
v_res_105_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim(v_motive_100_, v_t_boxed_104_, v_h_102_, v_endAttrs_103_);
lean_dec(v_endAttrs_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___redArg(lean_object* v_endElement_106_){
_start:
{
lean_inc(v_endElement_106_);
return v_endElement_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___redArg___boxed(lean_object* v_endElement_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___redArg(v_endElement_107_);
lean_dec(v_endElement_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim(lean_object* v_motive_109_, uint8_t v_t_110_, lean_object* v_h_111_, lean_object* v_endElement_112_){
_start:
{
lean_inc(v_endElement_112_);
return v_endElement_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___boxed(lean_object* v_motive_113_, lean_object* v_t_114_, lean_object* v_h_115_, lean_object* v_endElement_116_){
_start:
{
uint8_t v_t_boxed_117_; lean_object* v_res_118_; 
v_t_boxed_117_ = lean_unbox(v_t_114_);
v_res_118_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim(v_motive_113_, v_t_boxed_117_, v_h_115_, v_endElement_116_);
lean_dec(v_endElement_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___redArg(lean_object* v_endVoidElement_119_){
_start:
{
lean_inc(v_endVoidElement_119_);
return v_endVoidElement_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___redArg___boxed(lean_object* v_endVoidElement_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___redArg(v_endVoidElement_120_);
lean_dec(v_endVoidElement_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim(lean_object* v_motive_122_, uint8_t v_t_123_, lean_object* v_h_124_, lean_object* v_endVoidElement_125_){
_start:
{
lean_inc(v_endVoidElement_125_);
return v_endVoidElement_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___boxed(lean_object* v_motive_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_endVoidElement_129_){
_start:
{
uint8_t v_t_boxed_130_; lean_object* v_res_131_; 
v_t_boxed_130_ = lean_unbox(v_t_127_);
v_res_131_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim(v_motive_126_, v_t_boxed_130_, v_h_128_, v_endVoidElement_129_);
lean_dec(v_endVoidElement_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind(lean_object* v_q_132_, uint8_t v_kind_133_){
_start:
{
lean_object* v_kinds_134_; lean_object* v_htmls_135_; lean_object* v_strs_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_145_; 
v_kinds_134_ = lean_ctor_get(v_q_132_, 0);
v_htmls_135_ = lean_ctor_get(v_q_132_, 1);
v_strs_136_ = lean_ctor_get(v_q_132_, 2);
v_isSharedCheck_145_ = !lean_is_exclusive(v_q_132_);
if (v_isSharedCheck_145_ == 0)
{
v___x_138_ = v_q_132_;
v_isShared_139_ = v_isSharedCheck_145_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_strs_136_);
lean_inc(v_htmls_135_);
lean_inc(v_kinds_134_);
lean_dec(v_q_132_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_145_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_140_ = lean_box(v_kind_133_);
v___x_141_ = lean_array_push(v_kinds_134_, v___x_140_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_141_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_htmls_135_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_strs_136_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind___boxed(lean_object* v_q_146_, lean_object* v_kind_147_){
_start:
{
uint8_t v_kind_boxed_148_; lean_object* v_res_149_; 
v_kind_boxed_148_ = lean_unbox(v_kind_147_);
v_res_149_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind(v_q_146_, v_kind_boxed_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushHtml(lean_object* v_q_150_, lean_object* v_value_151_){
_start:
{
lean_object* v_kinds_152_; lean_object* v_htmls_153_; lean_object* v_strs_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
v_kinds_152_ = lean_ctor_get(v_q_150_, 0);
v_htmls_153_ = lean_ctor_get(v_q_150_, 1);
v_strs_154_ = lean_ctor_get(v_q_150_, 2);
v_isSharedCheck_162_ = !lean_is_exclusive(v_q_150_);
if (v_isSharedCheck_162_ == 0)
{
v___x_156_ = v_q_150_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_strs_154_);
lean_inc(v_htmls_153_);
lean_inc(v_kinds_152_);
lean_dec(v_q_150_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_158_ = lean_array_push(v_htmls_153_, v_value_151_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___x_158_);
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_kinds_152_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_strs_154_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushStr(lean_object* v_q_163_, lean_object* v_str_164_){
_start:
{
lean_object* v_kinds_165_; lean_object* v_htmls_166_; lean_object* v_strs_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
v_kinds_165_ = lean_ctor_get(v_q_163_, 0);
v_htmls_166_ = lean_ctor_get(v_q_163_, 1);
v_strs_167_ = lean_ctor_get(v_q_163_, 2);
v_isSharedCheck_175_ = !lean_is_exclusive(v_q_163_);
if (v_isSharedCheck_175_ == 0)
{
v___x_169_ = v_q_163_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_strs_167_);
lean_inc(v_htmls_166_);
lean_inc(v_kinds_165_);
lean_dec(v_q_163_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = lean_array_push(v_strs_167_, v_str_164_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 2, v___x_171_);
v___x_173_ = v___x_169_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_kinds_165_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_htmls_166_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popKind___redArg(lean_object* v_q_176_){
_start:
{
lean_object* v_kinds_177_; lean_object* v_htmls_178_; lean_object* v_strs_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_192_; 
v_kinds_177_ = lean_ctor_get(v_q_176_, 0);
v_htmls_178_ = lean_ctor_get(v_q_176_, 1);
v_strs_179_ = lean_ctor_get(v_q_176_, 2);
v_isSharedCheck_192_ = !lean_is_exclusive(v_q_176_);
if (v_isSharedCheck_192_ == 0)
{
v___x_181_ = v_q_176_;
v_isShared_182_ = v_isSharedCheck_192_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_strs_179_);
lean_inc(v_htmls_178_);
lean_inc(v_kinds_177_);
lean_dec(v_q_176_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_192_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_kind_186_; lean_object* v___x_187_; lean_object* v_q_189_; 
v___x_183_ = lean_array_get_size(v_kinds_177_);
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_sub(v___x_183_, v___x_184_);
v_kind_186_ = lean_array_fget(v_kinds_177_, v___x_185_);
lean_dec(v___x_185_);
v___x_187_ = lean_array_pop(v_kinds_177_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_187_);
v_q_189_ = v___x_181_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_htmls_178_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_strs_179_);
v_q_189_ = v_reuseFailAlloc_191_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; 
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_kind_186_);
lean_ctor_set(v___x_190_, 1, v_q_189_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popKind(lean_object* v_q_193_, lean_object* v_h_194_){
_start:
{
lean_object* v_kinds_195_; lean_object* v_htmls_196_; lean_object* v_strs_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_210_; 
v_kinds_195_ = lean_ctor_get(v_q_193_, 0);
v_htmls_196_ = lean_ctor_get(v_q_193_, 1);
v_strs_197_ = lean_ctor_get(v_q_193_, 2);
v_isSharedCheck_210_ = !lean_is_exclusive(v_q_193_);
if (v_isSharedCheck_210_ == 0)
{
v___x_199_ = v_q_193_;
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_strs_197_);
lean_inc(v_htmls_196_);
lean_inc(v_kinds_195_);
lean_dec(v_q_193_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_kind_204_; lean_object* v___x_205_; lean_object* v_q_207_; 
v___x_201_ = lean_array_get_size(v_kinds_195_);
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_sub(v___x_201_, v___x_202_);
v_kind_204_ = lean_array_fget(v_kinds_195_, v___x_203_);
lean_dec(v___x_203_);
v___x_205_ = lean_array_pop(v_kinds_195_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_205_);
v_q_207_ = v___x_199_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_htmls_196_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v_strs_197_);
v_q_207_ = v_reuseFailAlloc_209_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; 
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v_kind_204_);
lean_ctor_set(v___x_208_, 1, v_q_207_);
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popHtml_x21(lean_object* v_q_211_){
_start:
{
lean_object* v_kinds_212_; lean_object* v_htmls_213_; lean_object* v_strs_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_228_; 
v_kinds_212_ = lean_ctor_get(v_q_211_, 0);
v_htmls_213_ = lean_ctor_get(v_q_211_, 1);
v_strs_214_ = lean_ctor_get(v_q_211_, 2);
v_isSharedCheck_228_ = !lean_is_exclusive(v_q_211_);
if (v_isSharedCheck_228_ == 0)
{
v___x_216_ = v_q_211_;
v_isShared_217_ = v_isSharedCheck_228_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_strs_214_);
lean_inc(v_htmls_213_);
lean_inc(v_kinds_212_);
lean_dec(v_q_211_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_228_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_value_222_; lean_object* v___x_223_; lean_object* v_q_225_; 
v___x_218_ = l_Lean_instInhabitedHtml_default;
v___x_219_ = lean_array_get_size(v_htmls_213_);
v___x_220_ = lean_unsigned_to_nat(1u);
v___x_221_ = lean_nat_sub(v___x_219_, v___x_220_);
v_value_222_ = lean_array_get(v___x_218_, v_htmls_213_, v___x_221_);
lean_dec(v___x_221_);
v___x_223_ = lean_array_pop(v_htmls_213_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_223_);
v_q_225_ = v___x_216_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_kinds_212_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_strs_214_);
v_q_225_ = v_reuseFailAlloc_227_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; 
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_value_222_);
lean_ctor_set(v___x_226_, 1, v_q_225_);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21(lean_object* v_q_230_){
_start:
{
lean_object* v_kinds_231_; lean_object* v_htmls_232_; lean_object* v_strs_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_247_; 
v_kinds_231_ = lean_ctor_get(v_q_230_, 0);
v_htmls_232_ = lean_ctor_get(v_q_230_, 1);
v_strs_233_ = lean_ctor_get(v_q_230_, 2);
v_isSharedCheck_247_ = !lean_is_exclusive(v_q_230_);
if (v_isSharedCheck_247_ == 0)
{
v___x_235_ = v_q_230_;
v_isShared_236_ = v_isSharedCheck_247_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_strs_233_);
lean_inc(v_htmls_232_);
lean_inc(v_kinds_231_);
lean_dec(v_q_230_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_247_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v_str_241_; lean_object* v___x_242_; lean_object* v_q_244_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_238_ = lean_array_get_size(v_strs_233_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_sub(v___x_238_, v___x_239_);
v_str_241_ = lean_array_get(v___x_237_, v_strs_233_, v___x_240_);
lean_dec(v___x_240_);
v___x_242_ = lean_array_pop(v_strs_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 2, v___x_242_);
v_q_244_ = v___x_235_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_kinds_231_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_htmls_232_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v___x_242_);
v_q_244_ = v_reuseFailAlloc_246_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_str_241_);
lean_ctor_set(v___x_245_, 1, v_q_244_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(lean_object* v_s_248_, lean_object* v_replacement_249_, lean_object* v_a_250_, lean_object* v_b_251_){
_start:
{
lean_object* v_it_253_; lean_object* v_startPos_254_; lean_object* v_endPos_255_; lean_object* v_it_264_; 
switch(lean_obj_tag(v_a_250_))
{
case 0:
{
lean_object* v_pos_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_282_; 
v_pos_270_ = lean_ctor_get(v_a_250_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v_a_250_);
if (v_isSharedCheck_282_ == 0)
{
v___x_272_ = v_a_250_;
v_isShared_273_ = v_isSharedCheck_282_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_pos_270_);
lean_dec(v_a_250_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_282_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v_startInclusive_274_; lean_object* v_endExclusive_275_; lean_object* v___x_276_; uint8_t v_decide_277_; 
v_startInclusive_274_ = lean_ctor_get(v_s_248_, 1);
v_endExclusive_275_ = lean_ctor_get(v_s_248_, 2);
v___x_276_ = lean_nat_sub(v_endExclusive_275_, v_startInclusive_274_);
v_decide_277_ = lean_nat_dec_eq(v_pos_270_, v___x_276_);
lean_dec(v___x_276_);
if (v_decide_277_ == 0)
{
lean_object* v___x_279_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 1);
v___x_279_ = v___x_272_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_pos_270_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
v_it_264_ = v___x_279_;
goto v___jp_263_;
}
}
else
{
lean_object* v___x_281_; 
lean_del_object(v___x_272_);
lean_dec(v_pos_270_);
v___x_281_ = lean_box(3);
v_it_264_ = v___x_281_;
goto v___jp_263_;
}
}
}
case 1:
{
lean_object* v_pos_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_295_; 
v_pos_283_ = lean_ctor_get(v_a_250_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_a_250_);
if (v_isSharedCheck_295_ == 0)
{
v___x_285_ = v_a_250_;
v_isShared_286_ = v_isSharedCheck_295_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_pos_283_);
lean_dec(v_a_250_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_295_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_str_287_; lean_object* v_startInclusive_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v_str_287_ = lean_ctor_get(v_s_248_, 0);
v_startInclusive_288_ = lean_ctor_get(v_s_248_, 1);
v___x_289_ = lean_nat_add(v_startInclusive_288_, v_pos_283_);
v___x_290_ = lean_string_utf8_next_fast(v_str_287_, v___x_289_);
lean_dec(v___x_289_);
v___x_291_ = lean_nat_sub(v___x_290_, v_startInclusive_288_);
lean_inc(v___x_291_);
if (v_isShared_286_ == 0)
{
lean_ctor_set_tag(v___x_285_, 0);
lean_ctor_set(v___x_285_, 0, v___x_291_);
v___x_293_ = v___x_285_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
v_it_253_ = v___x_293_;
v_startPos_254_ = v_pos_283_;
v_endPos_255_ = v___x_291_;
goto v___jp_252_;
}
}
}
case 2:
{
lean_object* v_needle_296_; lean_object* v_table_297_; lean_object* v_stackPos_298_; lean_object* v_needlePos_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_360_; 
v_needle_296_ = lean_ctor_get(v_a_250_, 0);
v_table_297_ = lean_ctor_get(v_a_250_, 1);
v_stackPos_298_ = lean_ctor_get(v_a_250_, 2);
v_needlePos_299_ = lean_ctor_get(v_a_250_, 3);
v_isSharedCheck_360_ = !lean_is_exclusive(v_a_250_);
if (v_isSharedCheck_360_ == 0)
{
v___x_301_ = v_a_250_;
v_isShared_302_ = v_isSharedCheck_360_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_needlePos_299_);
lean_inc(v_stackPos_298_);
lean_inc(v_table_297_);
lean_inc(v_needle_296_);
lean_dec(v_a_250_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_360_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v_str_303_; lean_object* v_startInclusive_304_; lean_object* v_endExclusive_305_; lean_object* v_str_306_; lean_object* v_startInclusive_307_; lean_object* v_endExclusive_308_; lean_object* v_basePos_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_str_303_ = lean_ctor_get(v_needle_296_, 0);
v_startInclusive_304_ = lean_ctor_get(v_needle_296_, 1);
v_endExclusive_305_ = lean_ctor_get(v_needle_296_, 2);
v_str_306_ = lean_ctor_get(v_s_248_, 0);
v_startInclusive_307_ = lean_ctor_get(v_s_248_, 1);
v_endExclusive_308_ = lean_ctor_get(v_s_248_, 2);
v_basePos_309_ = lean_nat_sub(v_stackPos_298_, v_needlePos_299_);
v___x_310_ = lean_nat_sub(v_endExclusive_305_, v_startInclusive_304_);
v___x_311_ = lean_nat_add(v_basePos_309_, v___x_310_);
v___x_312_ = lean_nat_sub(v_endExclusive_308_, v_startInclusive_307_);
v___x_313_ = lean_nat_dec_le(v___x_311_, v___x_312_);
lean_dec(v___x_311_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
lean_dec(v___x_310_);
lean_del_object(v___x_301_);
lean_dec(v_needlePos_299_);
lean_dec(v_stackPos_298_);
lean_dec_ref(v_table_297_);
lean_dec_ref(v_needle_296_);
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_add(v_basePos_309_, v___x_314_);
v___x_316_ = lean_nat_dec_le(v___x_315_, v___x_312_);
lean_dec(v___x_315_);
if (v___x_316_ == 0)
{
lean_dec(v___x_312_);
lean_dec(v_basePos_309_);
lean_dec_ref(v_s_248_);
return v_b_251_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = l_String_Slice_pos_x21(v_s_248_, v_basePos_309_);
lean_dec(v_basePos_309_);
v___x_318_ = lean_box(3);
v_it_253_ = v___x_318_;
v_startPos_254_ = v___x_317_;
v_endPos_255_ = v___x_312_;
goto v___jp_252_;
}
}
else
{
lean_object* v___x_319_; uint8_t v_stackByte_320_; lean_object* v___x_321_; uint8_t v_patByte_322_; uint8_t v___x_323_; 
lean_dec(v___x_312_);
v___x_319_ = lean_nat_add(v_startInclusive_307_, v_stackPos_298_);
v_stackByte_320_ = lean_string_get_byte_fast(v_str_306_, v___x_319_);
v___x_321_ = lean_nat_add(v_startInclusive_304_, v_needlePos_299_);
v_patByte_322_ = lean_string_get_byte_fast(v_str_303_, v___x_321_);
v___x_323_ = lean_uint8_dec_eq(v_stackByte_320_, v_patByte_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; uint8_t v_decide_325_; 
lean_dec(v___x_310_);
v___x_324_ = lean_unsigned_to_nat(0u);
v_decide_325_ = lean_nat_dec_eq(v_needlePos_299_, v___x_324_);
if (v_decide_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_newNeedlePos_328_; uint8_t v___x_329_; 
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = lean_nat_sub(v_needlePos_299_, v___x_326_);
lean_dec(v_needlePos_299_);
v_newNeedlePos_328_ = lean_array_fget_borrowed(v_table_297_, v___x_327_);
lean_dec(v___x_327_);
v___x_329_ = lean_nat_dec_eq(v_newNeedlePos_328_, v___x_324_);
if (v___x_329_ == 0)
{
lean_object* v_oldBasePos_330_; lean_object* v___x_331_; lean_object* v_newBasePos_332_; lean_object* v___x_334_; 
lean_inc(v_newNeedlePos_328_);
v_oldBasePos_330_ = l_String_Slice_pos_x21(v_s_248_, v_basePos_309_);
lean_dec(v_basePos_309_);
v___x_331_ = lean_nat_sub(v_stackPos_298_, v_newNeedlePos_328_);
v_newBasePos_332_ = l_String_Slice_pos_x21(v_s_248_, v___x_331_);
lean_dec(v___x_331_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 3, v_newNeedlePos_328_);
v___x_334_ = v___x_301_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_needle_296_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_table_297_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_stackPos_298_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v_newNeedlePos_328_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
v_it_253_ = v___x_334_;
v_startPos_254_ = v_oldBasePos_330_;
v_endPos_255_ = v_newBasePos_332_;
goto v___jp_252_;
}
}
else
{
lean_object* v_basePos_336_; lean_object* v_nextStackPos_337_; lean_object* v___x_339_; 
v_basePos_336_ = l_String_Slice_pos_x21(v_s_248_, v_basePos_309_);
lean_dec(v_basePos_309_);
v_nextStackPos_337_ = l_String_Slice_posGE___redArg(v_s_248_, v_stackPos_298_);
lean_inc(v_nextStackPos_337_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 3, v___x_324_);
lean_ctor_set(v___x_301_, 2, v_nextStackPos_337_);
v___x_339_ = v___x_301_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_needle_296_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_table_297_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_nextStackPos_337_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v___x_324_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
v_it_253_ = v___x_339_;
v_startPos_254_ = v_basePos_336_;
v_endPos_255_ = v_nextStackPos_337_;
goto v___jp_252_;
}
}
}
else
{
lean_object* v_basePos_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_nextStackPos_344_; lean_object* v___x_346_; 
lean_dec(v_basePos_309_);
lean_dec(v_needlePos_299_);
v_basePos_341_ = l_String_Slice_pos_x21(v_s_248_, v_stackPos_298_);
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_add(v_stackPos_298_, v___x_342_);
lean_dec(v_stackPos_298_);
v_nextStackPos_344_ = l_String_Slice_posGE___redArg(v_s_248_, v___x_343_);
lean_inc(v_nextStackPos_344_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 3, v___x_324_);
lean_ctor_set(v___x_301_, 2, v_nextStackPos_344_);
v___x_346_ = v___x_301_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_needle_296_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_table_297_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_nextStackPos_344_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v___x_324_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
v_it_253_ = v___x_346_;
v_startPos_254_ = v_basePos_341_;
v_endPos_255_ = v_nextStackPos_344_;
goto v___jp_252_;
}
}
}
else
{
lean_object* v___x_348_; lean_object* v_nextStackPos_349_; lean_object* v_nextNeedlePos_350_; uint8_t v_decide_351_; 
lean_dec(v_basePos_309_);
v___x_348_ = lean_unsigned_to_nat(1u);
v_nextStackPos_349_ = lean_nat_add(v_stackPos_298_, v___x_348_);
lean_dec(v_stackPos_298_);
v_nextNeedlePos_350_ = lean_nat_add(v_needlePos_299_, v___x_348_);
lean_dec(v_needlePos_299_);
v_decide_351_ = lean_nat_dec_eq(v_nextNeedlePos_350_, v___x_310_);
lean_dec(v___x_310_);
if (v_decide_351_ == 0)
{
lean_object* v___x_353_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 3, v_nextNeedlePos_350_);
lean_ctor_set(v___x_301_, 2, v_nextStackPos_349_);
v___x_353_ = v___x_301_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_needle_296_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_table_297_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_nextStackPos_349_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_nextNeedlePos_350_);
v___x_353_ = v_reuseFailAlloc_355_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
v_a_250_ = v___x_353_;
goto _start;
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_358_; 
lean_dec(v_nextNeedlePos_350_);
v___x_356_ = lean_unsigned_to_nat(0u);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 3, v___x_356_);
lean_ctor_set(v___x_301_, 2, v_nextStackPos_349_);
v___x_358_ = v___x_301_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_needle_296_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_table_297_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_nextStackPos_349_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
v_it_264_ = v___x_358_;
goto v___jp_263_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_248_);
return v_b_251_;
}
}
v___jp_252_:
{
lean_object* v___x_256_; lean_object* v_str_257_; lean_object* v_startInclusive_258_; lean_object* v_endExclusive_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_inc_ref(v_s_248_);
v___x_256_ = l_String_Slice_slice_x21(v_s_248_, v_startPos_254_, v_endPos_255_);
lean_dec(v_endPos_255_);
lean_dec(v_startPos_254_);
v_str_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc_ref(v_str_257_);
v_startInclusive_258_ = lean_ctor_get(v___x_256_, 1);
lean_inc(v_startInclusive_258_);
v_endExclusive_259_ = lean_ctor_get(v___x_256_, 2);
lean_inc(v_endExclusive_259_);
lean_dec_ref(v___x_256_);
v___x_260_ = lean_string_utf8_extract_fast(v_str_257_, v_startInclusive_258_, v_endExclusive_259_);
lean_dec(v_endExclusive_259_);
lean_dec(v_startInclusive_258_);
lean_dec_ref(v_str_257_);
v___x_261_ = lean_string_append(v_b_251_, v___x_260_);
lean_dec_ref(v___x_260_);
v_a_250_ = v_it_253_;
v_b_251_ = v___x_261_;
goto _start;
}
v___jp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_string_utf8_byte_size(v_replacement_249_);
v___x_267_ = lean_string_utf8_extract_fast(v_replacement_249_, v___x_265_, v___x_266_);
v___x_268_ = lean_string_append(v_b_251_, v___x_267_);
lean_dec_ref(v___x_267_);
v_a_250_ = v_it_264_;
v_b_251_ = v___x_268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg___boxed(lean_object* v_s_361_, lean_object* v_replacement_362_, lean_object* v_a_363_, lean_object* v_b_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_361_, v_replacement_362_, v_a_363_, v_b_364_);
lean_dec_ref(v_replacement_362_);
return v_res_365_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__1));
v___x_372_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2);
v___x_375_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__1));
v___x_376_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
lean_ctor_set(v___x_376_, 2, v___x_373_);
lean_ctor_set(v___x_376_, 3, v___x_373_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(lean_object* v_s_377_, lean_object* v_replacement_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_380_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3);
v___x_381_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_377_, v_replacement_378_, v___x_380_, v___x_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___boxed(lean_object* v_s_382_, lean_object* v_replacement_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(v_s_382_, v_replacement_383_);
lean_dec_ref(v_replacement_383_);
return v_res_384_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__1));
v___x_391_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2);
v___x_394_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__1));
v___x_395_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_393_);
lean_ctor_set(v___x_395_, 2, v___x_392_);
lean_ctor_set(v___x_395_, 3, v___x_392_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(lean_object* v_s_396_, lean_object* v_replacement_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_399_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3);
v___x_400_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_396_, v_replacement_397_, v___x_399_, v___x_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___boxed(lean_object* v_s_401_, lean_object* v_replacement_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v_s_401_, v_replacement_402_);
lean_dec_ref(v_replacement_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal(lean_object* v_v_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_407_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__0));
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_string_utf8_byte_size(v_v_406_);
v___x_410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_410_, 0, v_v_406_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_409_);
v___x_411_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v___x_410_, v___x_407_);
v___x_412_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__1));
v___x_413_ = lean_string_utf8_byte_size(v___x_411_);
v___x_414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_414_, 0, v___x_411_);
lean_ctor_set(v___x_414_, 1, v___x_408_);
lean_ctor_set(v___x_414_, 2, v___x_413_);
v___x_415_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(v___x_414_, v___x_412_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0(lean_object* v_s_416_, lean_object* v_pattern_417_, lean_object* v_replacement_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v_s_416_, v_replacement_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___boxed(lean_object* v_s_420_, lean_object* v_pattern_421_, lean_object* v_replacement_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0(v_s_420_, v_pattern_421_, v_replacement_422_);
lean_dec_ref(v_replacement_422_);
lean_dec_ref(v_pattern_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1(lean_object* v_s_424_, lean_object* v_pattern_425_, lean_object* v_replacement_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(v_s_424_, v_replacement_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___boxed(lean_object* v_s_428_, lean_object* v_pattern_429_, lean_object* v_replacement_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1(v_s_428_, v_pattern_429_, v_replacement_430_);
lean_dec_ref(v_replacement_430_);
lean_dec_ref(v_pattern_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0(lean_object* v_s_432_, lean_object* v_replacement_433_, lean_object* v_inst_434_, lean_object* v_R_435_, lean_object* v_a_436_, lean_object* v_b_437_, lean_object* v_c_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_432_, v_replacement_433_, v_a_436_, v_b_437_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___boxed(lean_object* v_s_440_, lean_object* v_replacement_441_, lean_object* v_inst_442_, lean_object* v_R_443_, lean_object* v_a_444_, lean_object* v_b_445_, lean_object* v_c_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0(v_s_440_, v_replacement_441_, v_inst_442_, v_R_443_, v_a_444_, v_b_445_, v_c_446_);
lean_dec_ref(v_replacement_441_);
return v_res_447_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__1));
v___x_454_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2);
v___x_457_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__1));
v___x_458_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_455_);
lean_ctor_set(v___x_458_, 3, v___x_455_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(lean_object* v_s_459_, lean_object* v_replacement_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_462_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3);
v___x_463_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_459_, v_replacement_460_, v___x_462_, v___x_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___boxed(lean_object* v_s_464_, lean_object* v_replacement_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(v_s_464_, v_replacement_465_);
lean_dec_ref(v_replacement_465_);
return v_res_466_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__1));
v___x_473_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2);
v___x_476_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__1));
v___x_477_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
lean_ctor_set(v___x_477_, 2, v___x_474_);
lean_ctor_set(v___x_477_, 3, v___x_474_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(lean_object* v_s_478_, lean_object* v_replacement_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_481_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3);
v___x_482_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_478_, v_replacement_479_, v___x_481_, v___x_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___boxed(lean_object* v_s_483_, lean_object* v_replacement_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(v_s_483_, v_replacement_484_);
lean_dec_ref(v_replacement_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText(lean_object* v_s_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__0));
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = lean_string_utf8_byte_size(v_s_488_);
v___x_492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_492_, 0, v_s_488_);
lean_ctor_set(v___x_492_, 1, v___x_490_);
lean_ctor_set(v___x_492_, 2, v___x_491_);
v___x_493_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v___x_492_, v___x_489_);
v___x_494_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__0));
v___x_495_ = lean_string_utf8_byte_size(v___x_493_);
v___x_496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_496_, 0, v___x_493_);
lean_ctor_set(v___x_496_, 1, v___x_490_);
lean_ctor_set(v___x_496_, 2, v___x_495_);
v___x_497_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(v___x_496_, v___x_494_);
v___x_498_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__1));
v___x_499_ = lean_string_utf8_byte_size(v___x_497_);
v___x_500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_500_, 0, v___x_497_);
lean_ctor_set(v___x_500_, 1, v___x_490_);
lean_ctor_set(v___x_500_, 2, v___x_499_);
v___x_501_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(v___x_500_, v___x_498_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0(lean_object* v_s_502_, lean_object* v_pattern_503_, lean_object* v_replacement_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(v_s_502_, v_replacement_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___boxed(lean_object* v_s_506_, lean_object* v_pattern_507_, lean_object* v_replacement_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0(v_s_506_, v_pattern_507_, v_replacement_508_);
lean_dec_ref(v_replacement_508_);
lean_dec_ref(v_pattern_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1(lean_object* v_s_510_, lean_object* v_pattern_511_, lean_object* v_replacement_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(v_s_510_, v_replacement_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___boxed(lean_object* v_s_514_, lean_object* v_pattern_515_, lean_object* v_replacement_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1(v_s_514_, v_pattern_515_, v_replacement_516_);
lean_dec_ref(v_replacement_516_);
lean_dec_ref(v_pattern_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__3(uint8_t v_kind_518_, lean_object* v_as_519_, size_t v_i_520_, size_t v_stop_521_, lean_object* v_b_522_){
_start:
{
uint8_t v___x_523_; 
v___x_523_ = lean_usize_dec_eq(v_i_520_, v_stop_521_);
if (v___x_523_ == 0)
{
lean_object* v_kinds_524_; lean_object* v_htmls_525_; lean_object* v_strs_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_540_; 
v_kinds_524_ = lean_ctor_get(v_b_522_, 0);
v_htmls_525_ = lean_ctor_get(v_b_522_, 1);
v_strs_526_ = lean_ctor_get(v_b_522_, 2);
v_isSharedCheck_540_ = !lean_is_exclusive(v_b_522_);
if (v_isSharedCheck_540_ == 0)
{
v___x_528_ = v_b_522_;
v_isShared_529_ = v_isSharedCheck_540_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_strs_526_);
lean_inc(v_htmls_525_);
lean_inc(v_kinds_524_);
lean_dec(v_b_522_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_540_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_sub(v_i_520_, v___x_530_);
v___x_532_ = lean_array_uget_borrowed(v_as_519_, v___x_531_);
v___x_533_ = lean_box(v_kind_518_);
v___x_534_ = lean_array_push(v_kinds_524_, v___x_533_);
lean_inc(v___x_532_);
v___x_535_ = lean_array_push(v_htmls_525_, v___x_532_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 1, v___x_535_);
lean_ctor_set(v___x_528_, 0, v___x_534_);
v___x_537_ = v___x_528_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_strs_526_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
v_i_520_ = v___x_531_;
v_b_522_ = v___x_537_;
goto _start;
}
}
}
else
{
return v_b_522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__3___boxed(lean_object* v_kind_541_, lean_object* v_as_542_, lean_object* v_i_543_, lean_object* v_stop_544_, lean_object* v_b_545_){
_start:
{
uint8_t v_kind_boxed_546_; size_t v_i_boxed_547_; size_t v_stop_boxed_548_; lean_object* v_res_549_; 
v_kind_boxed_546_ = lean_unbox(v_kind_541_);
v_i_boxed_547_ = lean_unbox_usize(v_i_543_);
lean_dec(v_i_543_);
v_stop_boxed_548_ = lean_unbox_usize(v_stop_544_);
lean_dec(v_stop_544_);
v_res_549_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__3(v_kind_boxed_546_, v_as_542_, v_i_boxed_547_, v_stop_boxed_548_, v_b_545_);
lean_dec_ref(v_as_542_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(lean_object* v_as_550_, size_t v_i_551_, size_t v_stop_552_, lean_object* v_b_553_){
_start:
{
uint8_t v___x_554_; 
v___x_554_ = lean_usize_dec_eq(v_i_551_, v_stop_552_);
if (v___x_554_ == 0)
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v_kinds_560_; lean_object* v_htmls_561_; lean_object* v_strs_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_575_; 
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_sub(v_i_551_, v___x_555_);
v___x_557_ = lean_array_uget_borrowed(v_as_550_, v___x_556_);
v_fst_558_ = lean_ctor_get(v___x_557_, 0);
v_snd_559_ = lean_ctor_get(v___x_557_, 1);
v_kinds_560_ = lean_ctor_get(v_b_553_, 0);
v_htmls_561_ = lean_ctor_get(v_b_553_, 1);
v_strs_562_ = lean_ctor_get(v_b_553_, 2);
v_isSharedCheck_575_ = !lean_is_exclusive(v_b_553_);
if (v_isSharedCheck_575_ == 0)
{
v___x_564_ = v_b_553_;
v_isShared_565_ = v_isSharedCheck_575_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_strs_562_);
lean_inc(v_htmls_561_);
lean_inc(v_kinds_560_);
lean_dec(v_b_553_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_575_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_566_ = 1;
v___x_567_ = lean_box(v___x_566_);
v___x_568_ = lean_array_push(v_kinds_560_, v___x_567_);
lean_inc(v_snd_559_);
v___x_569_ = lean_array_push(v_strs_562_, v_snd_559_);
lean_inc(v_fst_558_);
v___x_570_ = lean_array_push(v___x_569_, v_fst_558_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 2, v___x_570_);
lean_ctor_set(v___x_564_, 0, v___x_568_);
v___x_572_ = v___x_564_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_htmls_561_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v___x_570_);
v___x_572_ = v_reuseFailAlloc_574_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v_i_551_ = v___x_556_;
v_b_553_ = v___x_572_;
goto _start;
}
}
}
else
{
return v_b_553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0___boxed(lean_object* v_as_576_, lean_object* v_i_577_, lean_object* v_stop_578_, lean_object* v_b_579_){
_start:
{
size_t v_i_boxed_580_; size_t v_stop_boxed_581_; lean_object* v_res_582_; 
v_i_boxed_580_ = lean_unbox_usize(v_i_577_);
lean_dec(v_i_577_);
v_stop_boxed_581_ = lean_unbox_usize(v_stop_578_);
lean_dec(v_stop_578_);
v_res_582_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(v_as_576_, v_i_boxed_580_, v_stop_boxed_581_, v_b_579_);
lean_dec_ref(v_as_576_);
return v_res_582_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2___redArg(lean_object* v___x_583_, lean_object* v___y_584_, lean_object* v_as_585_, lean_object* v_k_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
lean_object* v___x_589_; uint8_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_m_593_; lean_object* v_a_594_; uint8_t v___x_595_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_nat_dec_eq(v___x_583_, v___x_589_);
v___x_591_ = lean_nat_add(v_x_587_, v_x_588_);
v___x_592_ = lean_unsigned_to_nat(1u);
v_m_593_ = lean_nat_shiftr(v___x_591_, v___x_592_);
lean_dec(v___x_591_);
v_a_594_ = lean_array_fget_borrowed(v_as_585_, v_m_593_);
v___x_595_ = lean_string_dec_lt(v_a_594_, v_k_586_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; 
lean_dec(v_x_588_);
v___x_596_ = lean_string_dec_lt(v_k_586_, v_a_594_);
if (v___x_596_ == 0)
{
uint8_t v___x_597_; 
lean_dec(v_m_593_);
lean_dec(v_x_587_);
v___x_597_ = lean_nat_dec_le(v___x_589_, v___y_584_);
return v___x_597_;
}
else
{
uint8_t v___x_598_; 
v___x_598_ = lean_nat_dec_eq(v_m_593_, v___x_589_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_nat_sub(v_m_593_, v___x_592_);
lean_dec(v_m_593_);
v___x_600_ = lean_nat_dec_lt(v___x_599_, v_x_587_);
if (v___x_600_ == 0)
{
v_x_588_ = v___x_599_;
goto _start;
}
else
{
lean_dec(v___x_599_);
lean_dec(v_x_587_);
return v___x_590_;
}
}
else
{
lean_dec(v_m_593_);
lean_dec(v_x_587_);
return v___x_590_;
}
}
}
else
{
lean_object* v___x_602_; uint8_t v___x_603_; 
lean_dec(v_x_587_);
v___x_602_ = lean_nat_add(v_m_593_, v___x_592_);
lean_dec(v_m_593_);
v___x_603_ = lean_nat_dec_le(v___x_602_, v_x_588_);
if (v___x_603_ == 0)
{
lean_dec(v___x_602_);
lean_dec(v_x_588_);
return v___x_590_;
}
else
{
v_x_587_ = v___x_602_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2___redArg___boxed(lean_object* v___x_605_, lean_object* v___y_606_, lean_object* v_as_607_, lean_object* v_k_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
uint8_t v_res_611_; lean_object* v_r_612_; 
v_res_611_ = l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2___redArg(v___x_605_, v___y_606_, v_as_607_, v_k_608_, v_x_609_, v_x_610_);
lean_dec_ref(v_k_608_);
lean_dec_ref(v_as_607_);
lean_dec(v___y_606_);
lean_dec(v___x_605_);
v_r_612_ = lean_box(v_res_611_);
return v_r_612_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1(lean_object* v_s_613_, lean_object* v_p_614_){
_start:
{
uint32_t v___y_616_; lean_object* v___x_621_; uint8_t v_decide_622_; 
v___x_621_ = lean_string_utf8_byte_size(v_s_613_);
v_decide_622_ = lean_nat_dec_eq(v_p_614_, v___x_621_);
if (v_decide_622_ == 0)
{
uint32_t v___x_623_; uint32_t v___x_624_; uint8_t v___x_625_; 
v___x_623_ = lean_string_utf8_get_fast(v_s_613_, v_p_614_);
v___x_624_ = 65;
v___x_625_ = lean_uint32_dec_le(v___x_624_, v___x_623_);
if (v___x_625_ == 0)
{
v___y_616_ = v___x_623_;
goto v___jp_615_;
}
else
{
uint32_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = 90;
v___x_627_ = lean_uint32_dec_le(v___x_623_, v___x_626_);
if (v___x_627_ == 0)
{
v___y_616_ = v___x_623_;
goto v___jp_615_;
}
else
{
uint32_t v___x_628_; uint32_t v___x_629_; 
v___x_628_ = 32;
v___x_629_ = lean_uint32_add(v___x_623_, v___x_628_);
v___y_616_ = v___x_629_;
goto v___jp_615_;
}
}
}
else
{
lean_dec(v_p_614_);
return v_s_613_;
}
v___jp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_inc(v_p_614_);
v___x_617_ = lean_string_utf8_set(v_s_613_, v_p_614_, v___y_616_);
v___x_618_ = l_Char_utf8Size(v___y_616_);
v___x_619_ = lean_nat_add(v_p_614_, v___x_618_);
lean_dec(v___x_618_);
lean_dec(v_p_614_);
v_s_613_ = v___x_617_;
v_p_614_ = v___x_619_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_Html_voidElements));
v___x_631_ = lean_array_get_size(v___x_630_);
return v___x_631_;
}
}
static uint8_t _init_l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__1(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_obj_once(&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0, &l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0_once, _init_l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_nat_dec_lt(v___x_633_, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_obj_once(&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0, &l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0_once, _init_l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0);
v___x_637_ = lean_nat_sub(v___x_636_, v___x_635_);
return v___x_637_;
}
}
static uint8_t _init_l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__3(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_obj_once(&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2, &l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2_once, _init_l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_nat_dec_le(v___x_639_, v___x_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go(lean_object* v_acc_645_, lean_object* v_q_646_){
_start:
{
lean_object* v_kinds_647_; lean_object* v_htmls_648_; lean_object* v_strs_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_782_; 
v_kinds_647_ = lean_ctor_get(v_q_646_, 0);
v_htmls_648_ = lean_ctor_get(v_q_646_, 1);
v_strs_649_ = lean_ctor_get(v_q_646_, 2);
v_isSharedCheck_782_ = !lean_is_exclusive(v_q_646_);
if (v_isSharedCheck_782_ == 0)
{
v___x_651_ = v_q_646_;
v_isShared_652_ = v_isSharedCheck_782_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_strs_649_);
lean_inc(v_htmls_648_);
lean_inc(v_kinds_647_);
lean_dec(v_q_646_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_782_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_array_get_size(v_kinds_647_);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_nat_dec_eq(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v_kind_658_; lean_object* v___x_659_; lean_object* v_q_661_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_sub(v___x_653_, v___x_656_);
v_kind_658_ = lean_array_fget(v_kinds_647_, v___x_657_);
lean_dec(v___x_657_);
v___x_659_ = lean_array_pop(v_kinds_647_);
lean_inc_ref(v_strs_649_);
lean_inc_ref(v_htmls_648_);
lean_inc_ref(v___x_659_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_659_);
v_q_661_ = v___x_651_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_htmls_648_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_strs_649_);
v_q_661_ = v_reuseFailAlloc_781_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
uint8_t v___x_662_; 
v___x_662_ = lean_unbox(v_kind_658_);
switch(v___x_662_)
{
case 0:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_value_666_; lean_object* v___x_667_; lean_object* v_q_668_; 
lean_dec_ref(v_q_661_);
v___x_663_ = l_Lean_instInhabitedHtml_default;
v___x_664_ = lean_array_get_size(v_htmls_648_);
v___x_665_ = lean_nat_sub(v___x_664_, v___x_656_);
v_value_666_ = lean_array_get(v___x_663_, v_htmls_648_, v___x_665_);
lean_dec(v___x_665_);
v___x_667_ = lean_array_pop(v_htmls_648_);
lean_inc_ref(v_strs_649_);
lean_inc_ref(v___x_667_);
lean_inc_ref(v___x_659_);
v_q_668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_668_, 0, v___x_659_);
lean_ctor_set(v_q_668_, 1, v___x_667_);
lean_ctor_set(v_q_668_, 2, v_strs_649_);
switch(lean_obj_tag(v_value_666_))
{
case 0:
{
lean_object* v_tag_669_; lean_object* v_attrs_670_; lean_object* v_children_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref_known(v_q_668_, 3);
v_tag_669_ = lean_ctor_get(v_value_666_, 0);
v_attrs_670_ = lean_ctor_get(v_value_666_, 1);
v_children_671_ = lean_ctor_get(v_value_666_, 2);
v_isSharedCheck_720_ = !lean_is_exclusive(v_value_666_);
if (v_isSharedCheck_720_ == 0)
{
v___x_673_ = v_value_666_;
v_isShared_674_ = v_isSharedCheck_720_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_children_671_);
lean_inc(v_attrs_670_);
lean_inc(v_tag_669_);
lean_dec(v_value_666_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_720_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___y_676_; lean_object* v___y_682_; uint8_t v___x_699_; 
v___x_699_ = l_Lean_Html_isEmpty(v_children_671_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_del_object(v___x_673_);
v___x_700_ = 3;
v___x_701_ = lean_box(v___x_700_);
v___x_702_ = lean_array_push(v___x_659_, v___x_701_);
lean_inc_ref(v_tag_669_);
v___x_703_ = lean_array_push(v_strs_649_, v_tag_669_);
v___x_704_ = lean_array_push(v___x_702_, v_kind_658_);
v___x_705_ = lean_array_push(v___x_667_, v_children_671_);
v___x_706_ = 2;
v___x_707_ = lean_box(v___x_706_);
v___x_708_ = lean_array_push(v___x_704_, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_705_);
lean_ctor_set(v___x_709_, 2, v___x_703_);
v___y_682_ = v___x_709_;
goto v___jp_681_;
}
else
{
lean_object* v___x_710_; uint8_t v___x_711_; 
lean_dec_ref(v_children_671_);
lean_dec(v_kind_658_);
v___x_710_ = ((lean_object*)(l_Lean_Html_voidElements));
v___x_711_ = lean_uint8_once(&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__1, &l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__1_once, _init_l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__1);
if (v___x_711_ == 0)
{
goto v___jp_688_;
}
else
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_obj_once(&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2, &l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2_once, _init_l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2);
v___x_713_ = lean_uint8_once(&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__3, &l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__3_once, _init_l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__3);
if (v___x_713_ == 0)
{
goto v___jp_688_;
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
lean_inc_ref(v_tag_669_);
v___x_714_ = l_String_mapAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1(v_tag_669_, v___x_654_);
v___x_715_ = l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2___redArg(v___x_653_, v___x_712_, v___x_710_, v___x_714_, v___x_654_, v___x_712_);
lean_dec_ref(v___x_714_);
if (v___x_715_ == 0)
{
goto v___jp_688_;
}
else
{
uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_del_object(v___x_673_);
v___x_716_ = 4;
v___x_717_ = lean_box(v___x_716_);
v___x_718_ = lean_array_push(v___x_659_, v___x_717_);
v___x_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___x_667_);
lean_ctor_set(v___x_719_, 2, v_strs_649_);
v___y_682_ = v___x_719_;
goto v___jp_681_;
}
}
}
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__0));
v___x_678_ = lean_string_append(v___x_677_, v_tag_669_);
lean_dec_ref(v_tag_669_);
v___x_679_ = lean_string_append(v_acc_645_, v___x_678_);
lean_dec_ref(v___x_678_);
v_acc_645_ = v___x_679_;
v_q_646_ = v___y_676_;
goto _start;
}
v___jp_681_:
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_array_get_size(v_attrs_670_);
v___x_684_ = lean_nat_dec_lt(v___x_654_, v___x_683_);
if (v___x_684_ == 0)
{
lean_dec_ref(v_attrs_670_);
v___y_676_ = v___y_682_;
goto v___jp_675_;
}
else
{
size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_685_ = lean_usize_of_nat(v___x_683_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(v_attrs_670_, v___x_685_, v___x_686_, v___y_682_);
lean_dec_ref(v_attrs_670_);
v___y_676_ = v___x_687_;
goto v___jp_675_;
}
}
v___jp_688_:
{
uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_689_ = 3;
v___x_690_ = lean_box(v___x_689_);
v___x_691_ = lean_array_push(v___x_659_, v___x_690_);
lean_inc_ref(v_tag_669_);
v___x_692_ = lean_array_push(v_strs_649_, v_tag_669_);
v___x_693_ = 2;
v___x_694_ = lean_box(v___x_693_);
v___x_695_ = lean_array_push(v___x_691_, v___x_694_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 2, v___x_692_);
lean_ctor_set(v___x_673_, 1, v___x_667_);
lean_ctor_set(v___x_673_, 0, v___x_695_);
v___x_697_ = v___x_673_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v___x_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v___y_682_ = v___x_697_;
goto v___jp_681_;
}
}
}
}
case 1:
{
lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_659_);
lean_dec(v_kind_658_);
lean_dec_ref(v_strs_649_);
v_a_721_ = lean_ctor_get(v_value_666_, 0);
lean_inc_ref(v_a_721_);
lean_dec_ref_known(v_value_666_, 1);
v___x_722_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText(v_a_721_);
v___x_723_ = lean_string_append(v_acc_645_, v___x_722_);
lean_dec_ref(v___x_722_);
v_acc_645_ = v___x_723_;
v_q_646_ = v_q_668_;
goto _start;
}
case 2:
{
lean_object* v_a_725_; lean_object* v___x_726_; 
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_659_);
lean_dec(v_kind_658_);
lean_dec_ref(v_strs_649_);
v_a_725_ = lean_ctor_get(v_value_666_, 0);
lean_inc_ref(v_a_725_);
lean_dec_ref_known(v_value_666_, 1);
v___x_726_ = lean_string_append(v_acc_645_, v_a_725_);
lean_dec_ref(v_a_725_);
v_acc_645_ = v___x_726_;
v_q_646_ = v_q_668_;
goto _start;
}
default: 
{
lean_object* v_a_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
lean_dec_ref(v___x_667_);
lean_dec_ref(v___x_659_);
lean_dec_ref(v_strs_649_);
v_a_728_ = lean_ctor_get(v_value_666_, 0);
lean_inc_ref(v_a_728_);
lean_dec_ref_known(v_value_666_, 1);
v___x_729_ = lean_array_get_size(v_a_728_);
v___x_730_ = lean_nat_dec_lt(v___x_654_, v___x_729_);
if (v___x_730_ == 0)
{
lean_dec_ref(v_a_728_);
lean_dec(v_kind_658_);
v_q_646_ = v_q_668_;
goto _start;
}
else
{
size_t v___x_732_; size_t v___x_733_; uint8_t v___x_734_; lean_object* v___x_735_; 
v___x_732_ = lean_usize_of_nat(v___x_729_);
v___x_733_ = ((size_t)0ULL);
v___x_734_ = lean_unbox(v_kind_658_);
lean_dec(v_kind_658_);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__3(v___x_734_, v_a_728_, v___x_732_, v___x_733_, v_q_668_);
lean_dec_ref(v_a_728_);
v_q_646_ = v___x_735_;
goto _start;
}
}
}
}
case 1:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_str_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v_str_744_; lean_object* v___x_745_; lean_object* v_q_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
lean_dec_ref(v_q_661_);
lean_dec(v_kind_658_);
v___x_737_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_738_ = lean_array_get_size(v_strs_649_);
v___x_739_ = lean_nat_sub(v___x_738_, v___x_656_);
v_str_740_ = lean_array_get(v___x_737_, v_strs_649_, v___x_739_);
lean_dec(v___x_739_);
v___x_741_ = lean_array_pop(v_strs_649_);
v___x_742_ = lean_array_get_size(v___x_741_);
v___x_743_ = lean_nat_sub(v___x_742_, v___x_656_);
v_str_744_ = lean_array_get(v___x_737_, v___x_741_, v___x_743_);
lean_dec(v___x_743_);
v___x_745_ = lean_array_pop(v___x_741_);
v_q_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_746_, 0, v___x_659_);
lean_ctor_set(v_q_746_, 1, v_htmls_648_);
lean_ctor_set(v_q_746_, 2, v___x_745_);
v___x_747_ = lean_string_utf8_byte_size(v_str_744_);
v___x_748_ = lean_nat_dec_eq(v___x_747_, v___x_654_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_749_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__4));
v___x_750_ = lean_string_append(v___x_749_, v_str_740_);
lean_dec(v_str_740_);
v___x_751_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__5));
v___x_752_ = lean_string_append(v___x_750_, v___x_751_);
v___x_753_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal(v_str_744_);
v___x_754_ = lean_string_append(v___x_752_, v___x_753_);
lean_dec_ref(v___x_753_);
v___x_755_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__0));
v___x_756_ = lean_string_append(v___x_754_, v___x_755_);
v___x_757_ = lean_string_append(v_acc_645_, v___x_756_);
lean_dec_ref(v___x_756_);
v_acc_645_ = v___x_757_;
v_q_646_ = v_q_746_;
goto _start;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec(v_str_744_);
v___x_759_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__4));
v___x_760_ = lean_string_append(v___x_759_, v_str_740_);
lean_dec(v_str_740_);
v___x_761_ = lean_string_append(v_acc_645_, v___x_760_);
lean_dec_ref(v___x_760_);
v_acc_645_ = v___x_761_;
v_q_646_ = v_q_746_;
goto _start;
}
}
case 2:
{
uint32_t v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v___x_659_);
lean_dec(v_kind_658_);
lean_dec_ref(v_strs_649_);
lean_dec_ref(v_htmls_648_);
v___x_763_ = 62;
v___x_764_ = lean_string_push(v_acc_645_, v___x_763_);
v_acc_645_ = v___x_764_;
v_q_646_ = v_q_661_;
goto _start;
}
case 3:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_str_769_; lean_object* v___x_770_; lean_object* v_q_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec_ref(v_q_661_);
lean_dec(v_kind_658_);
v___x_766_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_767_ = lean_array_get_size(v_strs_649_);
v___x_768_ = lean_nat_sub(v___x_767_, v___x_656_);
v_str_769_ = lean_array_get(v___x_766_, v_strs_649_, v___x_768_);
lean_dec(v___x_768_);
v___x_770_ = lean_array_pop(v_strs_649_);
v_q_771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_771_, 0, v___x_659_);
lean_ctor_set(v_q_771_, 1, v_htmls_648_);
lean_ctor_set(v_q_771_, 2, v___x_770_);
v___x_772_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__6));
v___x_773_ = lean_string_append(v___x_772_, v_str_769_);
lean_dec(v_str_769_);
v___x_774_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__0));
v___x_775_ = lean_string_append(v___x_773_, v___x_774_);
v___x_776_ = lean_string_append(v_acc_645_, v___x_775_);
lean_dec_ref(v___x_775_);
v_acc_645_ = v___x_776_;
v_q_646_ = v_q_771_;
goto _start;
}
default: 
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec_ref(v___x_659_);
lean_dec(v_kind_658_);
lean_dec_ref(v_strs_649_);
lean_dec_ref(v_htmls_648_);
v___x_778_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__7));
v___x_779_ = lean_string_append(v_acc_645_, v___x_778_);
v_acc_645_ = v___x_779_;
v_q_646_ = v_q_661_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_651_);
lean_dec_ref(v_strs_649_);
lean_dec_ref(v_htmls_648_);
lean_dec_ref(v_kinds_647_);
return v_acc_645_;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2(lean_object* v___x_783_, lean_object* v___y_784_, lean_object* v_as_785_, lean_object* v_k_786_, lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2___redArg(v___x_783_, v___y_784_, v_as_785_, v_k_786_, v_x_787_, v_x_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2___boxed(lean_object* v___x_791_, lean_object* v___y_792_, lean_object* v_as_793_, lean_object* v_k_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Array_binSearchAux___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__2(v___x_791_, v___y_792_, v_as_793_, v_k_794_, v_x_795_, v_x_796_, v_x_797_);
lean_dec_ref(v_k_794_);
lean_dec_ref(v_as_793_);
lean_dec(v___y_792_);
lean_dec(v___x_791_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_render(lean_object* v_h_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_808_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_mk_empty_array_with_capacity(v___x_809_);
v___x_811_ = ((lean_object*)(l_Lean_Html_render___closed__0));
v___x_812_ = lean_array_push(v___x_810_, v_h_807_);
v___x_813_ = ((lean_object*)(l_Lean_Html_render___closed__1));
v___x_814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_814_, 0, v___x_811_);
lean_ctor_set(v___x_814_, 1, v___x_812_);
lean_ctor_set(v___x_814_, 2, v___x_813_);
v___x_815_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go(v___x_808_, v___x_814_);
return v___x_815_;
}
}
lean_object* runtime_initialize_Lean_Data_Html_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_BinSearch(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Html_Printer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Html_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_BinSearch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Html_Printer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Html_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Array_BinSearch(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Html_Printer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Html_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_BinSearch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Html_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Html_Printer(builtin);
}
#ifdef __cplusplus
}
#endif
