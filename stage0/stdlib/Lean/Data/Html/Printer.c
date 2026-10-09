// Lean compiler output
// Module: Lean.Data.Html.Printer
// Imports: public import Lean.Data.Html.Basic import Lean.Data.Html.Spec import Init.Data.String.Search
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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedHtml_default;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Html_isEmpty(lean_object*);
uint8_t l_Lean_Html_isVoidElement(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0_value;
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=\""};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__1_value;
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "</"};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2_value;
static const lean_string_object l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "/>"};
static const lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__3 = (const lean_object*)&l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go(lean_object*, lean_object*);
static const lean_array_object l_Lean_Html_render___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_render___closed__0 = (const lean_object*)&l_Lean_Html_render___closed__0_value;
static const lean_array_object l_Lean_Html_render___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Html_render___closed__1 = (const lean_object*)&l_Lean_Html_render___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_render(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___redArg(lean_object* v_html_22_){
_start:
{
lean_inc(v_html_22_);
return v_html_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___redArg___boxed(lean_object* v_html_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___redArg(v_html_23_);
lean_dec(v_html_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_html_28_){
_start:
{
lean_inc(v_html_28_);
return v_html_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_html_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_html_32_);
lean_dec(v_html_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___redArg(lean_object* v_attr_35_){
_start:
{
lean_inc(v_attr_35_);
return v_attr_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___redArg___boxed(lean_object* v_attr_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___redArg(v_attr_36_);
lean_dec(v_attr_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_attr_41_){
_start:
{
lean_inc(v_attr_41_);
return v_attr_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_attr_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_attr_45_);
lean_dec(v_attr_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___redArg(lean_object* v_endAttrs_48_){
_start:
{
lean_inc(v_endAttrs_48_);
return v_endAttrs_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___redArg___boxed(lean_object* v_endAttrs_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___redArg(v_endAttrs_49_);
lean_dec(v_endAttrs_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_endAttrs_54_){
_start:
{
lean_inc(v_endAttrs_54_);
return v_endAttrs_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_endAttrs_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_endAttrs_58_);
lean_dec(v_endAttrs_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___redArg(lean_object* v_endElement_61_){
_start:
{
lean_inc(v_endElement_61_);
return v_endElement_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___redArg___boxed(lean_object* v_endElement_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___redArg(v_endElement_62_);
lean_dec(v_endElement_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_endElement_67_){
_start:
{
lean_inc(v_endElement_67_);
return v_endElement_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_endElement_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_endElement_71_);
lean_dec(v_endElement_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___redArg(lean_object* v_endVoidElement_74_){
_start:
{
lean_inc(v_endVoidElement_74_);
return v_endVoidElement_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___redArg___boxed(lean_object* v_endVoidElement_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___redArg(v_endVoidElement_75_);
lean_dec(v_endVoidElement_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_endVoidElement_80_){
_start:
{
lean_inc(v_endVoidElement_80_);
return v_endVoidElement_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___boxed(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_endVoidElement_84_){
_start:
{
uint8_t v_t_boxed_85_; lean_object* v_res_86_; 
v_t_boxed_85_ = lean_unbox(v_t_82_);
v_res_86_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim(v_motive_81_, v_t_boxed_85_, v_h_83_, v_endVoidElement_84_);
lean_dec(v_endVoidElement_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind(lean_object* v_q_87_, uint8_t v_kind_88_){
_start:
{
lean_object* v_kinds_89_; lean_object* v_htmls_90_; lean_object* v_strs_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_100_; 
v_kinds_89_ = lean_ctor_get(v_q_87_, 0);
v_htmls_90_ = lean_ctor_get(v_q_87_, 1);
v_strs_91_ = lean_ctor_get(v_q_87_, 2);
v_isSharedCheck_100_ = !lean_is_exclusive(v_q_87_);
if (v_isSharedCheck_100_ == 0)
{
v___x_93_ = v_q_87_;
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_strs_91_);
lean_inc(v_htmls_90_);
lean_inc(v_kinds_89_);
lean_dec(v_q_87_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_95_ = lean_box(v_kind_88_);
v___x_96_ = lean_array_push(v_kinds_89_, v___x_95_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_96_);
v___x_98_ = v___x_93_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_htmls_90_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_strs_91_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind___boxed(lean_object* v_q_101_, lean_object* v_kind_102_){
_start:
{
uint8_t v_kind_boxed_103_; lean_object* v_res_104_; 
v_kind_boxed_103_ = lean_unbox(v_kind_102_);
v_res_104_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind(v_q_101_, v_kind_boxed_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushHtml(lean_object* v_q_105_, lean_object* v_value_106_){
_start:
{
lean_object* v_kinds_107_; lean_object* v_htmls_108_; lean_object* v_strs_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_117_; 
v_kinds_107_ = lean_ctor_get(v_q_105_, 0);
v_htmls_108_ = lean_ctor_get(v_q_105_, 1);
v_strs_109_ = lean_ctor_get(v_q_105_, 2);
v_isSharedCheck_117_ = !lean_is_exclusive(v_q_105_);
if (v_isSharedCheck_117_ == 0)
{
v___x_111_ = v_q_105_;
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_strs_109_);
lean_inc(v_htmls_108_);
lean_inc(v_kinds_107_);
lean_dec(v_q_105_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_array_push(v_htmls_108_, v_value_106_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v___x_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_kinds_107_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_strs_109_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushStr(lean_object* v_q_118_, lean_object* v_str_119_){
_start:
{
lean_object* v_kinds_120_; lean_object* v_htmls_121_; lean_object* v_strs_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_130_; 
v_kinds_120_ = lean_ctor_get(v_q_118_, 0);
v_htmls_121_ = lean_ctor_get(v_q_118_, 1);
v_strs_122_ = lean_ctor_get(v_q_118_, 2);
v_isSharedCheck_130_ = !lean_is_exclusive(v_q_118_);
if (v_isSharedCheck_130_ == 0)
{
v___x_124_ = v_q_118_;
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_strs_122_);
lean_inc(v_htmls_121_);
lean_inc(v_kinds_120_);
lean_dec(v_q_118_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_array_push(v_strs_122_, v_str_119_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 2, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_kinds_120_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_htmls_121_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popKind___redArg(lean_object* v_q_131_){
_start:
{
lean_object* v_kinds_132_; lean_object* v_htmls_133_; lean_object* v_strs_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_147_; 
v_kinds_132_ = lean_ctor_get(v_q_131_, 0);
v_htmls_133_ = lean_ctor_get(v_q_131_, 1);
v_strs_134_ = lean_ctor_get(v_q_131_, 2);
v_isSharedCheck_147_ = !lean_is_exclusive(v_q_131_);
if (v_isSharedCheck_147_ == 0)
{
v___x_136_ = v_q_131_;
v_isShared_137_ = v_isSharedCheck_147_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_strs_134_);
lean_inc(v_htmls_133_);
lean_inc(v_kinds_132_);
lean_dec(v_q_131_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_147_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v_kind_141_; lean_object* v___x_142_; lean_object* v_q_144_; 
v___x_138_ = lean_array_get_size(v_kinds_132_);
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_nat_sub(v___x_138_, v___x_139_);
v_kind_141_ = lean_array_fget(v_kinds_132_, v___x_140_);
lean_dec(v___x_140_);
v___x_142_ = lean_array_pop(v_kinds_132_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_142_);
v_q_144_ = v___x_136_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_htmls_133_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_strs_134_);
v_q_144_ = v_reuseFailAlloc_146_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; 
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v_kind_141_);
lean_ctor_set(v___x_145_, 1, v_q_144_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popKind(lean_object* v_q_148_, lean_object* v_h_149_){
_start:
{
lean_object* v_kinds_150_; lean_object* v_htmls_151_; lean_object* v_strs_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_165_; 
v_kinds_150_ = lean_ctor_get(v_q_148_, 0);
v_htmls_151_ = lean_ctor_get(v_q_148_, 1);
v_strs_152_ = lean_ctor_get(v_q_148_, 2);
v_isSharedCheck_165_ = !lean_is_exclusive(v_q_148_);
if (v_isSharedCheck_165_ == 0)
{
v___x_154_ = v_q_148_;
v_isShared_155_ = v_isSharedCheck_165_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_strs_152_);
lean_inc(v_htmls_151_);
lean_inc(v_kinds_150_);
lean_dec(v_q_148_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_165_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_kind_159_; lean_object* v___x_160_; lean_object* v_q_162_; 
v___x_156_ = lean_array_get_size(v_kinds_150_);
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_sub(v___x_156_, v___x_157_);
v_kind_159_ = lean_array_fget(v_kinds_150_, v___x_158_);
lean_dec(v___x_158_);
v___x_160_ = lean_array_pop(v_kinds_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_160_);
v_q_162_ = v___x_154_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_htmls_151_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_strs_152_);
v_q_162_ = v_reuseFailAlloc_164_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; 
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v_kind_159_);
lean_ctor_set(v___x_163_, 1, v_q_162_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popHtml_x21(lean_object* v_q_166_){
_start:
{
lean_object* v_kinds_167_; lean_object* v_htmls_168_; lean_object* v_strs_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_183_; 
v_kinds_167_ = lean_ctor_get(v_q_166_, 0);
v_htmls_168_ = lean_ctor_get(v_q_166_, 1);
v_strs_169_ = lean_ctor_get(v_q_166_, 2);
v_isSharedCheck_183_ = !lean_is_exclusive(v_q_166_);
if (v_isSharedCheck_183_ == 0)
{
v___x_171_ = v_q_166_;
v_isShared_172_ = v_isSharedCheck_183_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_strs_169_);
lean_inc(v_htmls_168_);
lean_inc(v_kinds_167_);
lean_dec(v_q_166_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_183_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_value_177_; lean_object* v___x_178_; lean_object* v_q_180_; 
v___x_173_ = l_Lean_instInhabitedHtml_default;
v___x_174_ = lean_array_get_size(v_htmls_168_);
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_sub(v___x_174_, v___x_175_);
v_value_177_ = lean_array_get(v___x_173_, v_htmls_168_, v___x_176_);
lean_dec(v___x_176_);
v___x_178_ = lean_array_pop(v_htmls_168_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_178_);
v_q_180_ = v___x_171_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_kinds_167_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_strs_169_);
v_q_180_ = v_reuseFailAlloc_182_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; 
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v_value_177_);
lean_ctor_set(v___x_181_, 1, v_q_180_);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21(lean_object* v_q_185_){
_start:
{
lean_object* v_kinds_186_; lean_object* v_htmls_187_; lean_object* v_strs_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_202_; 
v_kinds_186_ = lean_ctor_get(v_q_185_, 0);
v_htmls_187_ = lean_ctor_get(v_q_185_, 1);
v_strs_188_ = lean_ctor_get(v_q_185_, 2);
v_isSharedCheck_202_ = !lean_is_exclusive(v_q_185_);
if (v_isSharedCheck_202_ == 0)
{
v___x_190_ = v_q_185_;
v_isShared_191_ = v_isSharedCheck_202_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_strs_188_);
lean_inc(v_htmls_187_);
lean_inc(v_kinds_186_);
lean_dec(v_q_185_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_202_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_str_196_; lean_object* v___x_197_; lean_object* v_q_199_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_193_ = lean_array_get_size(v_strs_188_);
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_sub(v___x_193_, v___x_194_);
v_str_196_ = lean_array_get(v___x_192_, v_strs_188_, v___x_195_);
lean_dec(v___x_195_);
v___x_197_ = lean_array_pop(v_strs_188_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 2, v___x_197_);
v_q_199_ = v___x_190_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_kinds_186_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_htmls_187_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v___x_197_);
v_q_199_ = v_reuseFailAlloc_201_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_str_196_);
lean_ctor_set(v___x_200_, 1, v_q_199_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(lean_object* v_s_203_, lean_object* v_replacement_204_, lean_object* v_a_205_, lean_object* v_b_206_){
_start:
{
lean_object* v_it_208_; lean_object* v_startPos_209_; lean_object* v_endPos_210_; lean_object* v_it_219_; 
switch(lean_obj_tag(v_a_205_))
{
case 0:
{
lean_object* v_pos_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_237_; 
v_pos_225_ = lean_ctor_get(v_a_205_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_a_205_);
if (v_isSharedCheck_237_ == 0)
{
v___x_227_ = v_a_205_;
v_isShared_228_ = v_isSharedCheck_237_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_pos_225_);
lean_dec(v_a_205_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_237_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v_startInclusive_229_; lean_object* v_endExclusive_230_; lean_object* v___x_231_; uint8_t v_decide_232_; 
v_startInclusive_229_ = lean_ctor_get(v_s_203_, 1);
v_endExclusive_230_ = lean_ctor_get(v_s_203_, 2);
v___x_231_ = lean_nat_sub(v_endExclusive_230_, v_startInclusive_229_);
v_decide_232_ = lean_nat_dec_eq(v_pos_225_, v___x_231_);
lean_dec(v___x_231_);
if (v_decide_232_ == 0)
{
lean_object* v___x_234_; 
if (v_isShared_228_ == 0)
{
lean_ctor_set_tag(v___x_227_, 1);
v___x_234_ = v___x_227_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_pos_225_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
v_it_219_ = v___x_234_;
goto v___jp_218_;
}
}
else
{
lean_object* v___x_236_; 
lean_del_object(v___x_227_);
lean_dec(v_pos_225_);
v___x_236_ = lean_box(3);
v_it_219_ = v___x_236_;
goto v___jp_218_;
}
}
}
case 1:
{
lean_object* v_pos_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_250_; 
v_pos_238_ = lean_ctor_get(v_a_205_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_a_205_);
if (v_isSharedCheck_250_ == 0)
{
v___x_240_ = v_a_205_;
v_isShared_241_ = v_isSharedCheck_250_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_pos_238_);
lean_dec(v_a_205_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_250_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_str_242_; lean_object* v_startInclusive_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v_str_242_ = lean_ctor_get(v_s_203_, 0);
v_startInclusive_243_ = lean_ctor_get(v_s_203_, 1);
v___x_244_ = lean_nat_add(v_startInclusive_243_, v_pos_238_);
v___x_245_ = lean_string_utf8_next_fast(v_str_242_, v___x_244_);
lean_dec(v___x_244_);
v___x_246_ = lean_nat_sub(v___x_245_, v_startInclusive_243_);
lean_inc(v___x_246_);
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 0);
lean_ctor_set(v___x_240_, 0, v___x_246_);
v___x_248_ = v___x_240_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
v_it_208_ = v___x_248_;
v_startPos_209_ = v_pos_238_;
v_endPos_210_ = v___x_246_;
goto v___jp_207_;
}
}
}
case 2:
{
lean_object* v_needle_251_; lean_object* v_table_252_; lean_object* v_stackPos_253_; lean_object* v_needlePos_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_315_; 
v_needle_251_ = lean_ctor_get(v_a_205_, 0);
v_table_252_ = lean_ctor_get(v_a_205_, 1);
v_stackPos_253_ = lean_ctor_get(v_a_205_, 2);
v_needlePos_254_ = lean_ctor_get(v_a_205_, 3);
v_isSharedCheck_315_ = !lean_is_exclusive(v_a_205_);
if (v_isSharedCheck_315_ == 0)
{
v___x_256_ = v_a_205_;
v_isShared_257_ = v_isSharedCheck_315_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_needlePos_254_);
lean_inc(v_stackPos_253_);
lean_inc(v_table_252_);
lean_inc(v_needle_251_);
lean_dec(v_a_205_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_315_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v_str_258_; lean_object* v_startInclusive_259_; lean_object* v_endExclusive_260_; lean_object* v_str_261_; lean_object* v_startInclusive_262_; lean_object* v_endExclusive_263_; lean_object* v_basePos_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_str_258_ = lean_ctor_get(v_needle_251_, 0);
v_startInclusive_259_ = lean_ctor_get(v_needle_251_, 1);
v_endExclusive_260_ = lean_ctor_get(v_needle_251_, 2);
v_str_261_ = lean_ctor_get(v_s_203_, 0);
v_startInclusive_262_ = lean_ctor_get(v_s_203_, 1);
v_endExclusive_263_ = lean_ctor_get(v_s_203_, 2);
v_basePos_264_ = lean_nat_sub(v_stackPos_253_, v_needlePos_254_);
v___x_265_ = lean_nat_sub(v_endExclusive_260_, v_startInclusive_259_);
v___x_266_ = lean_nat_add(v_basePos_264_, v___x_265_);
v___x_267_ = lean_nat_sub(v_endExclusive_263_, v_startInclusive_262_);
v___x_268_ = lean_nat_dec_le(v___x_266_, v___x_267_);
lean_dec(v___x_266_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
lean_dec(v___x_265_);
lean_del_object(v___x_256_);
lean_dec(v_needlePos_254_);
lean_dec(v_stackPos_253_);
lean_dec_ref(v_table_252_);
lean_dec_ref(v_needle_251_);
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_add(v_basePos_264_, v___x_269_);
v___x_271_ = lean_nat_dec_le(v___x_270_, v___x_267_);
lean_dec(v___x_270_);
if (v___x_271_ == 0)
{
lean_dec(v___x_267_);
lean_dec(v_basePos_264_);
lean_dec_ref(v_s_203_);
return v_b_206_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = l_String_Slice_pos_x21(v_s_203_, v_basePos_264_);
lean_dec(v_basePos_264_);
v___x_273_ = lean_box(3);
v_it_208_ = v___x_273_;
v_startPos_209_ = v___x_272_;
v_endPos_210_ = v___x_267_;
goto v___jp_207_;
}
}
else
{
lean_object* v___x_274_; uint8_t v_stackByte_275_; lean_object* v___x_276_; uint8_t v_patByte_277_; uint8_t v___x_278_; 
lean_dec(v___x_267_);
v___x_274_ = lean_nat_add(v_startInclusive_262_, v_stackPos_253_);
v_stackByte_275_ = lean_string_get_byte_fast(v_str_261_, v___x_274_);
v___x_276_ = lean_nat_add(v_startInclusive_259_, v_needlePos_254_);
v_patByte_277_ = lean_string_get_byte_fast(v_str_258_, v___x_276_);
v___x_278_ = lean_uint8_dec_eq(v_stackByte_275_, v_patByte_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; uint8_t v_decide_280_; 
lean_dec(v___x_265_);
v___x_279_ = lean_unsigned_to_nat(0u);
v_decide_280_ = lean_nat_dec_eq(v_needlePos_254_, v___x_279_);
if (v_decide_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_newNeedlePos_283_; uint8_t v___x_284_; 
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_nat_sub(v_needlePos_254_, v___x_281_);
lean_dec(v_needlePos_254_);
v_newNeedlePos_283_ = lean_array_fget_borrowed(v_table_252_, v___x_282_);
lean_dec(v___x_282_);
v___x_284_ = lean_nat_dec_eq(v_newNeedlePos_283_, v___x_279_);
if (v___x_284_ == 0)
{
lean_object* v_oldBasePos_285_; lean_object* v___x_286_; lean_object* v_newBasePos_287_; lean_object* v___x_289_; 
lean_inc(v_newNeedlePos_283_);
v_oldBasePos_285_ = l_String_Slice_pos_x21(v_s_203_, v_basePos_264_);
lean_dec(v_basePos_264_);
v___x_286_ = lean_nat_sub(v_stackPos_253_, v_newNeedlePos_283_);
v_newBasePos_287_ = l_String_Slice_pos_x21(v_s_203_, v___x_286_);
lean_dec(v___x_286_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 3, v_newNeedlePos_283_);
v___x_289_ = v___x_256_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_needle_251_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_table_252_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_stackPos_253_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_newNeedlePos_283_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
v_it_208_ = v___x_289_;
v_startPos_209_ = v_oldBasePos_285_;
v_endPos_210_ = v_newBasePos_287_;
goto v___jp_207_;
}
}
else
{
lean_object* v_basePos_291_; lean_object* v_nextStackPos_292_; lean_object* v___x_294_; 
v_basePos_291_ = l_String_Slice_pos_x21(v_s_203_, v_basePos_264_);
lean_dec(v_basePos_264_);
v_nextStackPos_292_ = l_String_Slice_posGE___redArg(v_s_203_, v_stackPos_253_);
lean_inc(v_nextStackPos_292_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 3, v___x_279_);
lean_ctor_set(v___x_256_, 2, v_nextStackPos_292_);
v___x_294_ = v___x_256_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_needle_251_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_table_252_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_nextStackPos_292_);
lean_ctor_set(v_reuseFailAlloc_295_, 3, v___x_279_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
v_it_208_ = v___x_294_;
v_startPos_209_ = v_basePos_291_;
v_endPos_210_ = v_nextStackPos_292_;
goto v___jp_207_;
}
}
}
else
{
lean_object* v_basePos_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_nextStackPos_299_; lean_object* v___x_301_; 
lean_dec(v_basePos_264_);
lean_dec(v_needlePos_254_);
v_basePos_296_ = l_String_Slice_pos_x21(v_s_203_, v_stackPos_253_);
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_add(v_stackPos_253_, v___x_297_);
lean_dec(v_stackPos_253_);
v_nextStackPos_299_ = l_String_Slice_posGE___redArg(v_s_203_, v___x_298_);
lean_inc(v_nextStackPos_299_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 3, v___x_279_);
lean_ctor_set(v___x_256_, 2, v_nextStackPos_299_);
v___x_301_ = v___x_256_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_needle_251_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_table_252_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_nextStackPos_299_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v___x_279_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
v_it_208_ = v___x_301_;
v_startPos_209_ = v_basePos_296_;
v_endPos_210_ = v_nextStackPos_299_;
goto v___jp_207_;
}
}
}
else
{
lean_object* v___x_303_; lean_object* v_nextStackPos_304_; lean_object* v_nextNeedlePos_305_; uint8_t v_decide_306_; 
lean_dec(v_basePos_264_);
v___x_303_ = lean_unsigned_to_nat(1u);
v_nextStackPos_304_ = lean_nat_add(v_stackPos_253_, v___x_303_);
lean_dec(v_stackPos_253_);
v_nextNeedlePos_305_ = lean_nat_add(v_needlePos_254_, v___x_303_);
lean_dec(v_needlePos_254_);
v_decide_306_ = lean_nat_dec_eq(v_nextNeedlePos_305_, v___x_265_);
lean_dec(v___x_265_);
if (v_decide_306_ == 0)
{
lean_object* v___x_308_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 3, v_nextNeedlePos_305_);
lean_ctor_set(v___x_256_, 2, v_nextStackPos_304_);
v___x_308_ = v___x_256_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_needle_251_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_table_252_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_nextStackPos_304_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v_nextNeedlePos_305_);
v___x_308_ = v_reuseFailAlloc_310_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
v_a_205_ = v___x_308_;
goto _start;
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec(v_nextNeedlePos_305_);
v___x_311_ = lean_unsigned_to_nat(0u);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 3, v___x_311_);
lean_ctor_set(v___x_256_, 2, v_nextStackPos_304_);
v___x_313_ = v___x_256_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_needle_251_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_table_252_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_nextStackPos_304_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
v_it_219_ = v___x_313_;
goto v___jp_218_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_203_);
return v_b_206_;
}
}
v___jp_207_:
{
lean_object* v___x_211_; lean_object* v_str_212_; lean_object* v_startInclusive_213_; lean_object* v_endExclusive_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
lean_inc_ref(v_s_203_);
v___x_211_ = l_String_Slice_slice_x21(v_s_203_, v_startPos_209_, v_endPos_210_);
lean_dec(v_endPos_210_);
lean_dec(v_startPos_209_);
v_str_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_str_212_);
v_startInclusive_213_ = lean_ctor_get(v___x_211_, 1);
lean_inc(v_startInclusive_213_);
v_endExclusive_214_ = lean_ctor_get(v___x_211_, 2);
lean_inc(v_endExclusive_214_);
lean_dec_ref(v___x_211_);
v___x_215_ = lean_string_utf8_extract_fast(v_str_212_, v_startInclusive_213_, v_endExclusive_214_);
lean_dec(v_endExclusive_214_);
lean_dec(v_startInclusive_213_);
lean_dec_ref(v_str_212_);
v___x_216_ = lean_string_append(v_b_206_, v___x_215_);
lean_dec_ref(v___x_215_);
v_a_205_ = v_it_208_;
v_b_206_ = v___x_216_;
goto _start;
}
v___jp_218_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_string_utf8_byte_size(v_replacement_204_);
v___x_222_ = lean_string_utf8_extract_fast(v_replacement_204_, v___x_220_, v___x_221_);
v___x_223_ = lean_string_append(v_b_206_, v___x_222_);
lean_dec_ref(v___x_222_);
v_a_205_ = v_it_219_;
v_b_206_ = v___x_223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg___boxed(lean_object* v_s_316_, lean_object* v_replacement_317_, lean_object* v_a_318_, lean_object* v_b_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_316_, v_replacement_317_, v_a_318_, v_b_319_);
lean_dec_ref(v_replacement_317_);
return v_res_320_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__1));
v___x_327_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2);
v___x_330_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__1));
v___x_331_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_329_);
lean_ctor_set(v___x_331_, 2, v___x_328_);
lean_ctor_set(v___x_331_, 3, v___x_328_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(lean_object* v_s_332_, lean_object* v_replacement_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_335_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3);
v___x_336_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_332_, v_replacement_333_, v___x_335_, v___x_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___boxed(lean_object* v_s_337_, lean_object* v_replacement_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(v_s_337_, v_replacement_338_);
lean_dec_ref(v_replacement_338_);
return v_res_339_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__1));
v___x_346_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2);
v___x_349_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__1));
v___x_350_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
lean_ctor_set(v___x_350_, 2, v___x_347_);
lean_ctor_set(v___x_350_, 3, v___x_347_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(lean_object* v_s_351_, lean_object* v_replacement_352_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_354_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3);
v___x_355_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_351_, v_replacement_352_, v___x_354_, v___x_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___boxed(lean_object* v_s_356_, lean_object* v_replacement_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v_s_356_, v_replacement_357_);
lean_dec_ref(v_replacement_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal(lean_object* v_v_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__0));
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_string_utf8_byte_size(v_v_361_);
v___x_365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_365_, 0, v_v_361_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_364_);
v___x_366_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v___x_365_, v___x_362_);
v___x_367_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__1));
v___x_368_ = lean_string_utf8_byte_size(v___x_366_);
v___x_369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_369_, 0, v___x_366_);
lean_ctor_set(v___x_369_, 1, v___x_363_);
lean_ctor_set(v___x_369_, 2, v___x_368_);
v___x_370_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(v___x_369_, v___x_367_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0(lean_object* v_s_371_, lean_object* v_pattern_372_, lean_object* v_replacement_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v_s_371_, v_replacement_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___boxed(lean_object* v_s_375_, lean_object* v_pattern_376_, lean_object* v_replacement_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0(v_s_375_, v_pattern_376_, v_replacement_377_);
lean_dec_ref(v_replacement_377_);
lean_dec_ref(v_pattern_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1(lean_object* v_s_379_, lean_object* v_pattern_380_, lean_object* v_replacement_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(v_s_379_, v_replacement_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___boxed(lean_object* v_s_383_, lean_object* v_pattern_384_, lean_object* v_replacement_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1(v_s_383_, v_pattern_384_, v_replacement_385_);
lean_dec_ref(v_replacement_385_);
lean_dec_ref(v_pattern_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0(lean_object* v_s_387_, lean_object* v_replacement_388_, lean_object* v_inst_389_, lean_object* v_R_390_, lean_object* v_a_391_, lean_object* v_b_392_, lean_object* v_c_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_387_, v_replacement_388_, v_a_391_, v_b_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___boxed(lean_object* v_s_395_, lean_object* v_replacement_396_, lean_object* v_inst_397_, lean_object* v_R_398_, lean_object* v_a_399_, lean_object* v_b_400_, lean_object* v_c_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0(v_s_395_, v_replacement_396_, v_inst_397_, v_R_398_, v_a_399_, v_b_400_, v_c_401_);
lean_dec_ref(v_replacement_396_);
return v_res_402_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__1));
v___x_409_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2);
v___x_412_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__1));
v___x_413_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_411_);
lean_ctor_set(v___x_413_, 2, v___x_410_);
lean_ctor_set(v___x_413_, 3, v___x_410_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(lean_object* v_s_414_, lean_object* v_replacement_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_417_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3);
v___x_418_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_414_, v_replacement_415_, v___x_417_, v___x_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___boxed(lean_object* v_s_419_, lean_object* v_replacement_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(v_s_419_, v_replacement_420_);
lean_dec_ref(v_replacement_420_);
return v_res_421_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__1));
v___x_428_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2);
v___x_431_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__1));
v___x_432_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_429_);
lean_ctor_set(v___x_432_, 3, v___x_429_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(lean_object* v_s_433_, lean_object* v_replacement_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_436_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3);
v___x_437_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_433_, v_replacement_434_, v___x_436_, v___x_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___boxed(lean_object* v_s_438_, lean_object* v_replacement_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(v_s_438_, v_replacement_439_);
lean_dec_ref(v_replacement_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText(lean_object* v_s_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_444_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__0));
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_string_utf8_byte_size(v_s_443_);
v___x_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_447_, 0, v_s_443_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
lean_ctor_set(v___x_447_, 2, v___x_446_);
v___x_448_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v___x_447_, v___x_444_);
v___x_449_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__0));
v___x_450_ = lean_string_utf8_byte_size(v___x_448_);
v___x_451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_451_, 0, v___x_448_);
lean_ctor_set(v___x_451_, 1, v___x_445_);
lean_ctor_set(v___x_451_, 2, v___x_450_);
v___x_452_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(v___x_451_, v___x_449_);
v___x_453_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__1));
v___x_454_ = lean_string_utf8_byte_size(v___x_452_);
v___x_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_455_, 0, v___x_452_);
lean_ctor_set(v___x_455_, 1, v___x_445_);
lean_ctor_set(v___x_455_, 2, v___x_454_);
v___x_456_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(v___x_455_, v___x_453_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0(lean_object* v_s_457_, lean_object* v_pattern_458_, lean_object* v_replacement_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(v_s_457_, v_replacement_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___boxed(lean_object* v_s_461_, lean_object* v_pattern_462_, lean_object* v_replacement_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0(v_s_461_, v_pattern_462_, v_replacement_463_);
lean_dec_ref(v_replacement_463_);
lean_dec_ref(v_pattern_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1(lean_object* v_s_465_, lean_object* v_pattern_466_, lean_object* v_replacement_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(v_s_465_, v_replacement_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___boxed(lean_object* v_s_469_, lean_object* v_pattern_470_, lean_object* v_replacement_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1(v_s_469_, v_pattern_470_, v_replacement_471_);
lean_dec_ref(v_replacement_471_);
lean_dec_ref(v_pattern_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1(uint8_t v_kind_473_, lean_object* v_as_474_, size_t v_i_475_, size_t v_stop_476_, lean_object* v_b_477_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = lean_usize_dec_eq(v_i_475_, v_stop_476_);
if (v___x_478_ == 0)
{
lean_object* v_kinds_479_; lean_object* v_htmls_480_; lean_object* v_strs_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_495_; 
v_kinds_479_ = lean_ctor_get(v_b_477_, 0);
v_htmls_480_ = lean_ctor_get(v_b_477_, 1);
v_strs_481_ = lean_ctor_get(v_b_477_, 2);
v_isSharedCheck_495_ = !lean_is_exclusive(v_b_477_);
if (v_isSharedCheck_495_ == 0)
{
v___x_483_ = v_b_477_;
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_strs_481_);
lean_inc(v_htmls_480_);
lean_inc(v_kinds_479_);
lean_dec(v_b_477_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_sub(v_i_475_, v___x_485_);
v___x_487_ = lean_array_uget_borrowed(v_as_474_, v___x_486_);
v___x_488_ = lean_box(v_kind_473_);
v___x_489_ = lean_array_push(v_kinds_479_, v___x_488_);
lean_inc(v___x_487_);
v___x_490_ = lean_array_push(v_htmls_480_, v___x_487_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_490_);
lean_ctor_set(v___x_483_, 0, v___x_489_);
v___x_492_ = v___x_483_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_strs_481_);
v___x_492_ = v_reuseFailAlloc_494_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
v_i_475_ = v___x_486_;
v_b_477_ = v___x_492_;
goto _start;
}
}
}
else
{
return v_b_477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1___boxed(lean_object* v_kind_496_, lean_object* v_as_497_, lean_object* v_i_498_, lean_object* v_stop_499_, lean_object* v_b_500_){
_start:
{
uint8_t v_kind_boxed_501_; size_t v_i_boxed_502_; size_t v_stop_boxed_503_; lean_object* v_res_504_; 
v_kind_boxed_501_ = lean_unbox(v_kind_496_);
v_i_boxed_502_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_stop_boxed_503_ = lean_unbox_usize(v_stop_499_);
lean_dec(v_stop_499_);
v_res_504_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1(v_kind_boxed_501_, v_as_497_, v_i_boxed_502_, v_stop_boxed_503_, v_b_500_);
lean_dec_ref(v_as_497_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(lean_object* v_as_505_, size_t v_i_506_, size_t v_stop_507_, lean_object* v_b_508_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = lean_usize_dec_eq(v_i_506_, v_stop_507_);
if (v___x_509_ == 0)
{
size_t v___x_510_; size_t v___x_511_; lean_object* v___x_512_; lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v_kinds_515_; lean_object* v_htmls_516_; lean_object* v_strs_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_530_; 
v___x_510_ = ((size_t)1ULL);
v___x_511_ = lean_usize_sub(v_i_506_, v___x_510_);
v___x_512_ = lean_array_uget_borrowed(v_as_505_, v___x_511_);
v_fst_513_ = lean_ctor_get(v___x_512_, 0);
v_snd_514_ = lean_ctor_get(v___x_512_, 1);
v_kinds_515_ = lean_ctor_get(v_b_508_, 0);
v_htmls_516_ = lean_ctor_get(v_b_508_, 1);
v_strs_517_ = lean_ctor_get(v_b_508_, 2);
v_isSharedCheck_530_ = !lean_is_exclusive(v_b_508_);
if (v_isSharedCheck_530_ == 0)
{
v___x_519_ = v_b_508_;
v_isShared_520_ = v_isSharedCheck_530_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_strs_517_);
lean_inc(v_htmls_516_);
lean_inc(v_kinds_515_);
lean_dec(v_b_508_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_530_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_521_ = 1;
v___x_522_ = lean_box(v___x_521_);
v___x_523_ = lean_array_push(v_kinds_515_, v___x_522_);
lean_inc(v_snd_514_);
v___x_524_ = lean_array_push(v_strs_517_, v_snd_514_);
lean_inc(v_fst_513_);
v___x_525_ = lean_array_push(v___x_524_, v_fst_513_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 2, v___x_525_);
lean_ctor_set(v___x_519_, 0, v___x_523_);
v___x_527_ = v___x_519_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_htmls_516_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v___x_525_);
v___x_527_ = v_reuseFailAlloc_529_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
v_i_506_ = v___x_511_;
v_b_508_ = v___x_527_;
goto _start;
}
}
}
else
{
return v_b_508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0___boxed(lean_object* v_as_531_, lean_object* v_i_532_, lean_object* v_stop_533_, lean_object* v_b_534_){
_start:
{
size_t v_i_boxed_535_; size_t v_stop_boxed_536_; lean_object* v_res_537_; 
v_i_boxed_535_ = lean_unbox_usize(v_i_532_);
lean_dec(v_i_532_);
v_stop_boxed_536_ = lean_unbox_usize(v_stop_533_);
lean_dec(v_stop_533_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(v_as_531_, v_i_boxed_535_, v_stop_boxed_536_, v_b_534_);
lean_dec_ref(v_as_531_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go(lean_object* v_acc_542_, lean_object* v_q_543_){
_start:
{
lean_object* v_kinds_544_; lean_object* v_htmls_545_; lean_object* v_strs_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_677_; 
v_kinds_544_ = lean_ctor_get(v_q_543_, 0);
v_htmls_545_ = lean_ctor_get(v_q_543_, 1);
v_strs_546_ = lean_ctor_get(v_q_543_, 2);
v_isSharedCheck_677_ = !lean_is_exclusive(v_q_543_);
if (v_isSharedCheck_677_ == 0)
{
v___x_548_ = v_q_543_;
v_isShared_549_ = v_isSharedCheck_677_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_strs_546_);
lean_inc(v_htmls_545_);
lean_inc(v_kinds_544_);
lean_dec(v_q_543_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_677_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_550_ = lean_array_get_size(v_kinds_544_);
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = lean_nat_dec_eq(v___x_550_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_kind_555_; lean_object* v___x_556_; lean_object* v_q_558_; 
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_nat_sub(v___x_550_, v___x_553_);
v_kind_555_ = lean_array_fget(v_kinds_544_, v___x_554_);
lean_dec(v___x_554_);
v___x_556_ = lean_array_pop(v_kinds_544_);
lean_inc_ref(v_strs_546_);
lean_inc_ref(v_htmls_545_);
lean_inc_ref(v___x_556_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_556_);
v_q_558_ = v___x_548_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_htmls_545_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_strs_546_);
v_q_558_ = v_reuseFailAlloc_676_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
uint8_t v___x_559_; 
v___x_559_ = lean_unbox(v_kind_555_);
switch(v___x_559_)
{
case 0:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_value_563_; lean_object* v___x_564_; lean_object* v_q_565_; 
lean_dec_ref(v_q_558_);
v___x_560_ = l_Lean_instInhabitedHtml_default;
v___x_561_ = lean_array_get_size(v_htmls_545_);
v___x_562_ = lean_nat_sub(v___x_561_, v___x_553_);
v_value_563_ = lean_array_get(v___x_560_, v_htmls_545_, v___x_562_);
lean_dec(v___x_562_);
v___x_564_ = lean_array_pop(v_htmls_545_);
lean_inc_ref(v_strs_546_);
lean_inc_ref(v___x_564_);
lean_inc_ref(v___x_556_);
v_q_565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_565_, 0, v___x_556_);
lean_ctor_set(v_q_565_, 1, v___x_564_);
lean_ctor_set(v_q_565_, 2, v_strs_546_);
switch(lean_obj_tag(v_value_563_))
{
case 0:
{
lean_object* v_tag_566_; lean_object* v_attrs_567_; lean_object* v_children_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref_known(v_q_565_, 3);
v_tag_566_ = lean_ctor_get(v_value_563_, 0);
v_attrs_567_ = lean_ctor_get(v_value_563_, 1);
v_children_568_ = lean_ctor_get(v_value_563_, 2);
v_isSharedCheck_615_ = !lean_is_exclusive(v_value_563_);
if (v_isSharedCheck_615_ == 0)
{
v___x_570_ = v_value_563_;
v_isShared_571_ = v_isSharedCheck_615_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_children_568_);
lean_inc(v_attrs_567_);
lean_inc(v_tag_566_);
lean_dec(v_value_563_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_615_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___y_573_; lean_object* v___y_579_; uint8_t v___x_585_; 
v___x_585_ = l_Lean_Html_isEmpty(v_children_568_);
if (v___x_585_ == 0)
{
uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_586_ = 3;
v___x_587_ = lean_box(v___x_586_);
v___x_588_ = lean_array_push(v___x_556_, v___x_587_);
lean_inc_ref(v_tag_566_);
v___x_589_ = lean_array_push(v_strs_546_, v_tag_566_);
v___x_590_ = lean_array_push(v___x_588_, v_kind_555_);
v___x_591_ = lean_array_push(v___x_564_, v_children_568_);
v___x_592_ = 2;
v___x_593_ = lean_box(v___x_592_);
v___x_594_ = lean_array_push(v___x_590_, v___x_593_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 2, v___x_589_);
lean_ctor_set(v___x_570_, 1, v___x_591_);
lean_ctor_set(v___x_570_, 0, v___x_594_);
v___x_596_ = v___x_570_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v___x_589_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
v___y_579_ = v___x_596_;
goto v___jp_578_;
}
}
else
{
uint8_t v___x_598_; 
lean_dec_ref(v_children_568_);
lean_dec(v_kind_555_);
lean_inc_ref(v_tag_566_);
v___x_598_ = l_Lean_Html_isVoidElement(v_tag_566_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_599_ = 3;
v___x_600_ = lean_box(v___x_599_);
v___x_601_ = lean_array_push(v___x_556_, v___x_600_);
lean_inc_ref(v_tag_566_);
v___x_602_ = lean_array_push(v_strs_546_, v_tag_566_);
v___x_603_ = 2;
v___x_604_ = lean_box(v___x_603_);
v___x_605_ = lean_array_push(v___x_601_, v___x_604_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 2, v___x_602_);
lean_ctor_set(v___x_570_, 1, v___x_564_);
lean_ctor_set(v___x_570_, 0, v___x_605_);
v___x_607_ = v___x_570_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v___x_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
v___y_579_ = v___x_607_;
goto v___jp_578_;
}
}
else
{
uint8_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_609_ = 4;
v___x_610_ = lean_box(v___x_609_);
v___x_611_ = lean_array_push(v___x_556_, v___x_610_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 2, v_strs_546_);
lean_ctor_set(v___x_570_, 1, v___x_564_);
lean_ctor_set(v___x_570_, 0, v___x_611_);
v___x_613_ = v___x_570_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_strs_546_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
v___y_579_ = v___x_613_;
goto v___jp_578_;
}
}
}
v___jp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__0));
v___x_575_ = lean_string_append(v___x_574_, v_tag_566_);
lean_dec_ref(v_tag_566_);
v___x_576_ = lean_string_append(v_acc_542_, v___x_575_);
lean_dec_ref(v___x_575_);
v_acc_542_ = v___x_576_;
v_q_543_ = v___y_573_;
goto _start;
}
v___jp_578_:
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_array_get_size(v_attrs_567_);
v___x_581_ = lean_nat_dec_lt(v___x_551_, v___x_580_);
if (v___x_581_ == 0)
{
lean_dec_ref(v_attrs_567_);
v___y_573_ = v___y_579_;
goto v___jp_572_;
}
else
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_usize_of_nat(v___x_580_);
v___x_583_ = ((size_t)0ULL);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(v_attrs_567_, v___x_582_, v___x_583_, v___y_579_);
lean_dec_ref(v_attrs_567_);
v___y_573_ = v___x_584_;
goto v___jp_572_;
}
}
}
}
case 1:
{
lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec_ref(v___x_564_);
lean_dec_ref(v___x_556_);
lean_dec(v_kind_555_);
lean_dec_ref(v_strs_546_);
v_a_616_ = lean_ctor_get(v_value_563_, 0);
lean_inc_ref(v_a_616_);
lean_dec_ref_known(v_value_563_, 1);
v___x_617_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText(v_a_616_);
v___x_618_ = lean_string_append(v_acc_542_, v___x_617_);
lean_dec_ref(v___x_617_);
v_acc_542_ = v___x_618_;
v_q_543_ = v_q_565_;
goto _start;
}
case 2:
{
lean_object* v_a_620_; lean_object* v___x_621_; 
lean_dec_ref(v___x_564_);
lean_dec_ref(v___x_556_);
lean_dec(v_kind_555_);
lean_dec_ref(v_strs_546_);
v_a_620_ = lean_ctor_get(v_value_563_, 0);
lean_inc_ref(v_a_620_);
lean_dec_ref_known(v_value_563_, 1);
v___x_621_ = lean_string_append(v_acc_542_, v_a_620_);
lean_dec_ref(v_a_620_);
v_acc_542_ = v___x_621_;
v_q_543_ = v_q_565_;
goto _start;
}
default: 
{
lean_object* v_a_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
lean_dec_ref(v___x_564_);
lean_dec_ref(v___x_556_);
lean_dec_ref(v_strs_546_);
v_a_623_ = lean_ctor_get(v_value_563_, 0);
lean_inc_ref(v_a_623_);
lean_dec_ref_known(v_value_563_, 1);
v___x_624_ = lean_array_get_size(v_a_623_);
v___x_625_ = lean_nat_dec_lt(v___x_551_, v___x_624_);
if (v___x_625_ == 0)
{
lean_dec_ref(v_a_623_);
lean_dec(v_kind_555_);
v_q_543_ = v_q_565_;
goto _start;
}
else
{
size_t v___x_627_; size_t v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; 
v___x_627_ = lean_usize_of_nat(v___x_624_);
v___x_628_ = ((size_t)0ULL);
v___x_629_ = lean_unbox(v_kind_555_);
lean_dec(v_kind_555_);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1(v___x_629_, v_a_623_, v___x_627_, v___x_628_, v_q_565_);
lean_dec_ref(v_a_623_);
v_q_543_ = v___x_630_;
goto _start;
}
}
}
}
case 1:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_str_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_str_639_; lean_object* v___x_640_; lean_object* v_q_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
lean_dec_ref(v_q_558_);
lean_dec(v_kind_555_);
v___x_632_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_633_ = lean_array_get_size(v_strs_546_);
v___x_634_ = lean_nat_sub(v___x_633_, v___x_553_);
v_str_635_ = lean_array_get(v___x_632_, v_strs_546_, v___x_634_);
lean_dec(v___x_634_);
v___x_636_ = lean_array_pop(v_strs_546_);
v___x_637_ = lean_array_get_size(v___x_636_);
v___x_638_ = lean_nat_sub(v___x_637_, v___x_553_);
v_str_639_ = lean_array_get(v___x_632_, v___x_636_, v___x_638_);
lean_dec(v___x_638_);
v___x_640_ = lean_array_pop(v___x_636_);
v_q_641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_641_, 0, v___x_556_);
lean_ctor_set(v_q_641_, 1, v_htmls_545_);
lean_ctor_set(v_q_641_, 2, v___x_640_);
v___x_642_ = lean_string_utf8_byte_size(v_str_639_);
v___x_643_ = lean_nat_dec_eq(v___x_642_, v___x_551_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_644_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0));
v___x_645_ = lean_string_append(v___x_644_, v_str_635_);
lean_dec(v_str_635_);
v___x_646_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__1));
v___x_647_ = lean_string_append(v___x_645_, v___x_646_);
v___x_648_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal(v_str_639_);
v___x_649_ = lean_string_append(v___x_647_, v___x_648_);
lean_dec_ref(v___x_648_);
v___x_650_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__0));
v___x_651_ = lean_string_append(v___x_649_, v___x_650_);
v___x_652_ = lean_string_append(v_acc_542_, v___x_651_);
lean_dec_ref(v___x_651_);
v_acc_542_ = v___x_652_;
v_q_543_ = v_q_641_;
goto _start;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec(v_str_639_);
v___x_654_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0));
v___x_655_ = lean_string_append(v___x_654_, v_str_635_);
lean_dec(v_str_635_);
v___x_656_ = lean_string_append(v_acc_542_, v___x_655_);
lean_dec_ref(v___x_655_);
v_acc_542_ = v___x_656_;
v_q_543_ = v_q_641_;
goto _start;
}
}
case 2:
{
uint32_t v___x_658_; lean_object* v___x_659_; 
lean_dec_ref(v___x_556_);
lean_dec(v_kind_555_);
lean_dec_ref(v_strs_546_);
lean_dec_ref(v_htmls_545_);
v___x_658_ = 62;
v___x_659_ = lean_string_push(v_acc_542_, v___x_658_);
v_acc_542_ = v___x_659_;
v_q_543_ = v_q_558_;
goto _start;
}
case 3:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_str_664_; lean_object* v___x_665_; lean_object* v_q_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec_ref(v_q_558_);
lean_dec(v_kind_555_);
v___x_661_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_662_ = lean_array_get_size(v_strs_546_);
v___x_663_ = lean_nat_sub(v___x_662_, v___x_553_);
v_str_664_ = lean_array_get(v___x_661_, v_strs_546_, v___x_663_);
lean_dec(v___x_663_);
v___x_665_ = lean_array_pop(v_strs_546_);
v_q_666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_666_, 0, v___x_556_);
lean_ctor_set(v_q_666_, 1, v_htmls_545_);
lean_ctor_set(v_q_666_, 2, v___x_665_);
v___x_667_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2));
v___x_668_ = lean_string_append(v___x_667_, v_str_664_);
lean_dec(v_str_664_);
v___x_669_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__0));
v___x_670_ = lean_string_append(v___x_668_, v___x_669_);
v___x_671_ = lean_string_append(v_acc_542_, v___x_670_);
lean_dec_ref(v___x_670_);
v_acc_542_ = v___x_671_;
v_q_543_ = v_q_666_;
goto _start;
}
default: 
{
lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec_ref(v___x_556_);
lean_dec(v_kind_555_);
lean_dec_ref(v_strs_546_);
lean_dec_ref(v_htmls_545_);
v___x_673_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__3));
v___x_674_ = lean_string_append(v_acc_542_, v___x_673_);
v_acc_542_ = v___x_674_;
v_q_543_ = v_q_558_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_548_);
lean_dec_ref(v_strs_546_);
lean_dec_ref(v_htmls_545_);
lean_dec_ref(v_kinds_544_);
return v_acc_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_render(lean_object* v_h_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_686_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_mk_empty_array_with_capacity(v___x_687_);
v___x_689_ = ((lean_object*)(l_Lean_Html_render___closed__0));
v___x_690_ = lean_array_push(v___x_688_, v_h_685_);
v___x_691_ = ((lean_object*)(l_Lean_Html_render___closed__1));
v___x_692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_692_, 0, v___x_689_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
lean_ctor_set(v___x_692_, 2, v___x_691_);
v___x_693_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go(v___x_686_, v___x_692_);
return v___x_693_;
}
}
lean_object* runtime_initialize_Lean_Data_Html_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Html_Spec(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
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
res = runtime_initialize_Lean_Data_Html_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
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
lean_object* initialize_Lean_Data_Html_Spec(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Html_Printer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Html_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Html_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
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
