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
lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___redArg(lean_object* v_html_24_){
_start:
{
lean_inc(v_html_24_);
return v_html_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___redArg___boxed(lean_object* v_html_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___redArg(v_html_25_);
lean_dec(v_html_25_);
return v_res_26_;
}
}
lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_html_30_){
_start:
{
lean_inc(v_html_30_);
return v_html_30_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_html_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim(lean_box(0), v_t_28_, lean_box(0), v_html_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_html_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_html_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_html_35_);
lean_dec(v_html_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___redArg(lean_object* v_attr_38_){
_start:
{
lean_inc(v_attr_38_);
return v_attr_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___redArg___boxed(lean_object* v_attr_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___redArg(v_attr_39_);
lean_dec(v_attr_39_);
return v_res_40_;
}
}
lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_attr_44_){
_start:
{
lean_inc(v_attr_44_);
return v_attr_44_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_attr_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim(lean_box(0), v_t_42_, lean_box(0), v_attr_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_attr_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_attr_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_attr_49_);
lean_dec(v_attr_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___redArg(lean_object* v_endAttrs_52_){
_start:
{
lean_inc(v_endAttrs_52_);
return v_endAttrs_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___redArg___boxed(lean_object* v_endAttrs_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___redArg(v_endAttrs_53_);
lean_dec(v_endAttrs_53_);
return v_res_54_;
}
}
lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_endAttrs_58_){
_start:
{
lean_inc(v_endAttrs_58_);
return v_endAttrs_58_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_endAttrs_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim(lean_box(0), v_t_56_, lean_box(0), v_endAttrs_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_endAttrs_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endAttrs_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_endAttrs_63_);
lean_dec(v_endAttrs_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___redArg(lean_object* v_endElement_66_){
_start:
{
lean_inc(v_endElement_66_);
return v_endElement_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___redArg___boxed(lean_object* v_endElement_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___redArg(v_endElement_67_);
lean_dec(v_endElement_67_);
return v_res_68_;
}
}
lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_endElement_72_){
_start:
{
lean_inc(v_endElement_72_);
return v_endElement_72_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_70_ = stack[1].m_num;
lean_object* v_endElement_72_ = stack[3].m_obj;
lean_object* v_res_73_;
v_res_73_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim(lean_box(0), v_t_70_, lean_box(0), v_endElement_72_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_endElement_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endElement_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_endElement_77_);
lean_dec(v_endElement_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___redArg(lean_object* v_endVoidElement_80_){
_start:
{
lean_inc(v_endVoidElement_80_);
return v_endVoidElement_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___redArg___boxed(lean_object* v_endVoidElement_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___redArg(v_endVoidElement_81_);
lean_dec(v_endVoidElement_81_);
return v_res_82_;
}
}
lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim(lean_object* v_motive_83_, uint8_t v_t_84_, lean_object* v_h_85_, lean_object* v_endVoidElement_86_){
_start:
{
lean_inc(v_endVoidElement_86_);
return v_endVoidElement_86_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_84_ = stack[1].m_num;
lean_object* v_endVoidElement_86_ = stack[3].m_obj;
lean_object* v_res_87_;
v_res_87_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim(lean_box(0), v_t_84_, lean_box(0), v_endVoidElement_86_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim___boxed(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_endVoidElement_91_){
_start:
{
uint8_t v_t_boxed_92_; lean_object* v_res_93_; 
v_t_boxed_92_ = lean_unbox(v_t_89_);
v_res_93_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemKind_endVoidElement_elim(v_motive_88_, v_t_boxed_92_, v_h_90_, v_endVoidElement_91_);
lean_dec(v_endVoidElement_91_);
return v_res_93_;
}
}
lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind(lean_object* v_q_94_, uint8_t v_kind_95_){
_start:
{
lean_object* v_kinds_96_; lean_object* v_htmls_97_; lean_object* v_strs_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_107_; 
v_kinds_96_ = lean_ctor_get(v_q_94_, 0);
v_htmls_97_ = lean_ctor_get(v_q_94_, 1);
v_strs_98_ = lean_ctor_get(v_q_94_, 2);
v_isSharedCheck_107_ = !lean_is_exclusive(v_q_94_);
if (v_isSharedCheck_107_ == 0)
{
v___x_100_ = v_q_94_;
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_strs_98_);
lean_inc(v_htmls_97_);
lean_inc(v_kinds_96_);
lean_dec(v_q_94_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_102_ = lean_box(v_kind_95_);
v___x_103_ = lean_array_push(v_kinds_96_, v___x_102_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_103_);
v___x_105_ = v___x_100_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_htmls_97_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_strs_98_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_94_ = stack[0].m_obj;
uint8_t v_kind_95_ = stack[1].m_num;
lean_object* v_res_108_;
v_res_108_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind(v_q_94_, v_kind_95_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind___boxed(lean_object* v_q_109_, lean_object* v_kind_110_){
_start:
{
uint8_t v_kind_boxed_111_; lean_object* v_res_112_; 
v_kind_boxed_111_ = lean_unbox(v_kind_110_);
v_res_112_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushKind(v_q_109_, v_kind_boxed_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushHtml(lean_object* v_q_113_, lean_object* v_value_114_){
_start:
{
lean_object* v_kinds_115_; lean_object* v_htmls_116_; lean_object* v_strs_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_125_; 
v_kinds_115_ = lean_ctor_get(v_q_113_, 0);
v_htmls_116_ = lean_ctor_get(v_q_113_, 1);
v_strs_117_ = lean_ctor_get(v_q_113_, 2);
v_isSharedCheck_125_ = !lean_is_exclusive(v_q_113_);
if (v_isSharedCheck_125_ == 0)
{
v___x_119_ = v_q_113_;
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_strs_117_);
lean_inc(v_htmls_116_);
lean_inc(v_kinds_115_);
lean_dec(v_q_113_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = lean_array_push(v_htmls_116_, v_value_114_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v___x_121_);
v___x_123_ = v___x_119_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_kinds_115_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v_strs_117_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_pushStr(lean_object* v_q_126_, lean_object* v_str_127_){
_start:
{
lean_object* v_kinds_128_; lean_object* v_htmls_129_; lean_object* v_strs_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_138_; 
v_kinds_128_ = lean_ctor_get(v_q_126_, 0);
v_htmls_129_ = lean_ctor_get(v_q_126_, 1);
v_strs_130_ = lean_ctor_get(v_q_126_, 2);
v_isSharedCheck_138_ = !lean_is_exclusive(v_q_126_);
if (v_isSharedCheck_138_ == 0)
{
v___x_132_ = v_q_126_;
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_strs_130_);
lean_inc(v_htmls_129_);
lean_inc(v_kinds_128_);
lean_dec(v_q_126_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = lean_array_push(v_strs_130_, v_str_127_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 2, v___x_134_);
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_kinds_128_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_htmls_129_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popKind___redArg(lean_object* v_q_139_){
_start:
{
lean_object* v_kinds_140_; lean_object* v_htmls_141_; lean_object* v_strs_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_155_; 
v_kinds_140_ = lean_ctor_get(v_q_139_, 0);
v_htmls_141_ = lean_ctor_get(v_q_139_, 1);
v_strs_142_ = lean_ctor_get(v_q_139_, 2);
v_isSharedCheck_155_ = !lean_is_exclusive(v_q_139_);
if (v_isSharedCheck_155_ == 0)
{
v___x_144_ = v_q_139_;
v_isShared_145_ = v_isSharedCheck_155_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_strs_142_);
lean_inc(v_htmls_141_);
lean_inc(v_kinds_140_);
lean_dec(v_q_139_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_155_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v_kind_149_; lean_object* v___x_150_; lean_object* v_q_152_; 
v___x_146_ = lean_array_get_size(v_kinds_140_);
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_nat_sub(v___x_146_, v___x_147_);
v_kind_149_ = lean_array_fget(v_kinds_140_, v___x_148_);
lean_dec(v___x_148_);
v___x_150_ = lean_array_pop(v_kinds_140_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_150_);
v_q_152_ = v___x_144_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_htmls_141_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_strs_142_);
v_q_152_ = v_reuseFailAlloc_154_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v_kind_149_);
lean_ctor_set(v___x_153_, 1, v_q_152_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popKind(lean_object* v_q_156_, lean_object* v_h_157_){
_start:
{
lean_object* v_kinds_158_; lean_object* v_htmls_159_; lean_object* v_strs_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_173_; 
v_kinds_158_ = lean_ctor_get(v_q_156_, 0);
v_htmls_159_ = lean_ctor_get(v_q_156_, 1);
v_strs_160_ = lean_ctor_get(v_q_156_, 2);
v_isSharedCheck_173_ = !lean_is_exclusive(v_q_156_);
if (v_isSharedCheck_173_ == 0)
{
v___x_162_ = v_q_156_;
v_isShared_163_ = v_isSharedCheck_173_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_strs_160_);
lean_inc(v_htmls_159_);
lean_inc(v_kinds_158_);
lean_dec(v_q_156_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_173_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_kind_167_; lean_object* v___x_168_; lean_object* v_q_170_; 
v___x_164_ = lean_array_get_size(v_kinds_158_);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_sub(v___x_164_, v___x_165_);
v_kind_167_ = lean_array_fget(v_kinds_158_, v___x_166_);
lean_dec(v___x_166_);
v___x_168_ = lean_array_pop(v_kinds_158_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_168_);
v_q_170_ = v___x_162_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_htmls_159_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_strs_160_);
v_q_170_ = v_reuseFailAlloc_172_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; 
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_kind_167_);
lean_ctor_set(v___x_171_, 1, v_q_170_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popHtml_x21(lean_object* v_q_174_){
_start:
{
lean_object* v_kinds_175_; lean_object* v_htmls_176_; lean_object* v_strs_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_191_; 
v_kinds_175_ = lean_ctor_get(v_q_174_, 0);
v_htmls_176_ = lean_ctor_get(v_q_174_, 1);
v_strs_177_ = lean_ctor_get(v_q_174_, 2);
v_isSharedCheck_191_ = !lean_is_exclusive(v_q_174_);
if (v_isSharedCheck_191_ == 0)
{
v___x_179_ = v_q_174_;
v_isShared_180_ = v_isSharedCheck_191_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_strs_177_);
lean_inc(v_htmls_176_);
lean_inc(v_kinds_175_);
lean_dec(v_q_174_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_191_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_value_185_; lean_object* v___x_186_; lean_object* v_q_188_; 
v___x_181_ = l_Lean_instInhabitedHtml_default;
v___x_182_ = lean_array_get_size(v_htmls_176_);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_sub(v___x_182_, v___x_183_);
v_value_185_ = lean_array_get(v___x_181_, v_htmls_176_, v___x_184_);
lean_dec(v___x_184_);
v___x_186_ = lean_array_pop(v_htmls_176_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_186_);
v_q_188_ = v___x_179_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_kinds_175_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_strs_177_);
v_q_188_ = v_reuseFailAlloc_190_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_value_185_);
lean_ctor_set(v___x_189_, 1, v_q_188_);
return v___x_189_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21(lean_object* v_q_193_){
_start:
{
lean_object* v_kinds_194_; lean_object* v_htmls_195_; lean_object* v_strs_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_210_; 
v_kinds_194_ = lean_ctor_get(v_q_193_, 0);
v_htmls_195_ = lean_ctor_get(v_q_193_, 1);
v_strs_196_ = lean_ctor_get(v_q_193_, 2);
v_isSharedCheck_210_ = !lean_is_exclusive(v_q_193_);
if (v_isSharedCheck_210_ == 0)
{
v___x_198_ = v_q_193_;
v_isShared_199_ = v_isSharedCheck_210_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_strs_196_);
lean_inc(v_htmls_195_);
lean_inc(v_kinds_194_);
lean_dec(v_q_193_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_210_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_str_204_; lean_object* v___x_205_; lean_object* v_q_207_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_201_ = lean_array_get_size(v_strs_196_);
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_sub(v___x_201_, v___x_202_);
v_str_204_ = lean_array_get(v___x_200_, v_strs_196_, v___x_203_);
lean_dec(v___x_203_);
v___x_205_ = lean_array_pop(v_strs_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 2, v___x_205_);
v_q_207_ = v___x_198_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_kinds_194_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_htmls_195_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v___x_205_);
v_q_207_ = v_reuseFailAlloc_209_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; 
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v_str_204_);
lean_ctor_set(v___x_208_, 1, v_q_207_);
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(lean_object* v_s_211_, lean_object* v_replacement_212_, lean_object* v_a_213_, lean_object* v_b_214_){
_start:
{
lean_object* v_it_216_; lean_object* v_startPos_217_; lean_object* v_endPos_218_; lean_object* v_it_227_; 
switch(lean_obj_tag(v_a_213_))
{
case 0:
{
lean_object* v_pos_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_245_; 
v_pos_233_ = lean_ctor_get(v_a_213_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_a_213_);
if (v_isSharedCheck_245_ == 0)
{
v___x_235_ = v_a_213_;
v_isShared_236_ = v_isSharedCheck_245_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_pos_233_);
lean_dec(v_a_213_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_245_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v_startInclusive_237_; lean_object* v_endExclusive_238_; lean_object* v___x_239_; uint8_t v_decide_240_; 
v_startInclusive_237_ = lean_ctor_get(v_s_211_, 1);
v_endExclusive_238_ = lean_ctor_get(v_s_211_, 2);
v___x_239_ = lean_nat_sub(v_endExclusive_238_, v_startInclusive_237_);
v_decide_240_ = lean_nat_dec_eq(v_pos_233_, v___x_239_);
lean_dec(v___x_239_);
if (v_decide_240_ == 0)
{
lean_object* v___x_242_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 1);
v___x_242_ = v___x_235_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_pos_233_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
v_it_227_ = v___x_242_;
goto v___jp_226_;
}
}
else
{
lean_object* v___x_244_; 
lean_del_object(v___x_235_);
lean_dec(v_pos_233_);
v___x_244_ = lean_box(3);
v_it_227_ = v___x_244_;
goto v___jp_226_;
}
}
}
case 1:
{
lean_object* v_pos_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_258_; 
v_pos_246_ = lean_ctor_get(v_a_213_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v_a_213_);
if (v_isSharedCheck_258_ == 0)
{
v___x_248_ = v_a_213_;
v_isShared_249_ = v_isSharedCheck_258_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_pos_246_);
lean_dec(v_a_213_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_258_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v_str_250_; lean_object* v_startInclusive_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v_str_250_ = lean_ctor_get(v_s_211_, 0);
v_startInclusive_251_ = lean_ctor_get(v_s_211_, 1);
v___x_252_ = lean_nat_add(v_startInclusive_251_, v_pos_246_);
v___x_253_ = lean_string_utf8_next_fast(v_str_250_, v___x_252_);
lean_dec(v___x_252_);
v___x_254_ = lean_nat_sub(v___x_253_, v_startInclusive_251_);
lean_inc(v___x_254_);
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 0);
lean_ctor_set(v___x_248_, 0, v___x_254_);
v___x_256_ = v___x_248_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
v_it_216_ = v___x_256_;
v_startPos_217_ = v_pos_246_;
v_endPos_218_ = v___x_254_;
goto v___jp_215_;
}
}
}
case 2:
{
lean_object* v_needle_259_; lean_object* v_table_260_; lean_object* v_stackPos_261_; lean_object* v_needlePos_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_323_; 
v_needle_259_ = lean_ctor_get(v_a_213_, 0);
v_table_260_ = lean_ctor_get(v_a_213_, 1);
v_stackPos_261_ = lean_ctor_get(v_a_213_, 2);
v_needlePos_262_ = lean_ctor_get(v_a_213_, 3);
v_isSharedCheck_323_ = !lean_is_exclusive(v_a_213_);
if (v_isSharedCheck_323_ == 0)
{
v___x_264_ = v_a_213_;
v_isShared_265_ = v_isSharedCheck_323_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_needlePos_262_);
lean_inc(v_stackPos_261_);
lean_inc(v_table_260_);
lean_inc(v_needle_259_);
lean_dec(v_a_213_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_323_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v_str_266_; lean_object* v_startInclusive_267_; lean_object* v_endExclusive_268_; lean_object* v_str_269_; lean_object* v_startInclusive_270_; lean_object* v_endExclusive_271_; lean_object* v_basePos_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_str_266_ = lean_ctor_get(v_needle_259_, 0);
v_startInclusive_267_ = lean_ctor_get(v_needle_259_, 1);
v_endExclusive_268_ = lean_ctor_get(v_needle_259_, 2);
v_str_269_ = lean_ctor_get(v_s_211_, 0);
v_startInclusive_270_ = lean_ctor_get(v_s_211_, 1);
v_endExclusive_271_ = lean_ctor_get(v_s_211_, 2);
v_basePos_272_ = lean_nat_sub(v_stackPos_261_, v_needlePos_262_);
v___x_273_ = lean_nat_sub(v_endExclusive_268_, v_startInclusive_267_);
v___x_274_ = lean_nat_add(v_basePos_272_, v___x_273_);
v___x_275_ = lean_nat_sub(v_endExclusive_271_, v_startInclusive_270_);
v___x_276_ = lean_nat_dec_le(v___x_274_, v___x_275_);
lean_dec(v___x_274_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
lean_dec(v___x_273_);
lean_del_object(v___x_264_);
lean_dec(v_needlePos_262_);
lean_dec(v_stackPos_261_);
lean_dec_ref(v_table_260_);
lean_dec_ref(v_needle_259_);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_add(v_basePos_272_, v___x_277_);
v___x_279_ = lean_nat_dec_le(v___x_278_, v___x_275_);
lean_dec(v___x_278_);
if (v___x_279_ == 0)
{
lean_dec(v___x_275_);
lean_dec(v_basePos_272_);
lean_dec_ref(v_s_211_);
return v_b_214_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = l_String_Slice_pos_x21(v_s_211_, v_basePos_272_);
lean_dec(v_basePos_272_);
v___x_281_ = lean_box(3);
v_it_216_ = v___x_281_;
v_startPos_217_ = v___x_280_;
v_endPos_218_ = v___x_275_;
goto v___jp_215_;
}
}
else
{
lean_object* v___x_282_; uint8_t v_stackByte_283_; lean_object* v___x_284_; uint8_t v_patByte_285_; uint8_t v___x_286_; 
lean_dec(v___x_275_);
v___x_282_ = lean_nat_add(v_startInclusive_270_, v_stackPos_261_);
v_stackByte_283_ = lean_string_get_byte_fast(v_str_269_, v___x_282_);
v___x_284_ = lean_nat_add(v_startInclusive_267_, v_needlePos_262_);
v_patByte_285_ = lean_string_get_byte_fast(v_str_266_, v___x_284_);
v___x_286_ = lean_uint8_dec_eq(v_stackByte_283_, v_patByte_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; uint8_t v_decide_288_; 
lean_dec(v___x_273_);
v___x_287_ = lean_unsigned_to_nat(0u);
v_decide_288_ = lean_nat_dec_eq(v_needlePos_262_, v___x_287_);
if (v_decide_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_newNeedlePos_291_; uint8_t v___x_292_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_sub(v_needlePos_262_, v___x_289_);
lean_dec(v_needlePos_262_);
v_newNeedlePos_291_ = lean_array_fget_borrowed(v_table_260_, v___x_290_);
lean_dec(v___x_290_);
v___x_292_ = lean_nat_dec_eq(v_newNeedlePos_291_, v___x_287_);
if (v___x_292_ == 0)
{
lean_object* v_oldBasePos_293_; lean_object* v___x_294_; lean_object* v_newBasePos_295_; lean_object* v___x_297_; 
lean_inc(v_newNeedlePos_291_);
v_oldBasePos_293_ = l_String_Slice_pos_x21(v_s_211_, v_basePos_272_);
lean_dec(v_basePos_272_);
v___x_294_ = lean_nat_sub(v_stackPos_261_, v_newNeedlePos_291_);
v_newBasePos_295_ = l_String_Slice_pos_x21(v_s_211_, v___x_294_);
lean_dec(v___x_294_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 3, v_newNeedlePos_291_);
v___x_297_ = v___x_264_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_needle_259_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_table_260_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_stackPos_261_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_newNeedlePos_291_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
v_it_216_ = v___x_297_;
v_startPos_217_ = v_oldBasePos_293_;
v_endPos_218_ = v_newBasePos_295_;
goto v___jp_215_;
}
}
else
{
lean_object* v_basePos_299_; lean_object* v_nextStackPos_300_; lean_object* v___x_302_; 
v_basePos_299_ = l_String_Slice_pos_x21(v_s_211_, v_basePos_272_);
lean_dec(v_basePos_272_);
v_nextStackPos_300_ = l_String_Slice_posGE___redArg(v_s_211_, v_stackPos_261_);
lean_inc(v_nextStackPos_300_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 3, v___x_287_);
lean_ctor_set(v___x_264_, 2, v_nextStackPos_300_);
v___x_302_ = v___x_264_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_needle_259_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_table_260_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_nextStackPos_300_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v___x_287_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
v_it_216_ = v___x_302_;
v_startPos_217_ = v_basePos_299_;
v_endPos_218_ = v_nextStackPos_300_;
goto v___jp_215_;
}
}
}
else
{
lean_object* v_basePos_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_nextStackPos_307_; lean_object* v___x_309_; 
lean_dec(v_basePos_272_);
lean_dec(v_needlePos_262_);
v_basePos_304_ = l_String_Slice_pos_x21(v_s_211_, v_stackPos_261_);
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_add(v_stackPos_261_, v___x_305_);
lean_dec(v_stackPos_261_);
v_nextStackPos_307_ = l_String_Slice_posGE___redArg(v_s_211_, v___x_306_);
lean_inc(v_nextStackPos_307_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 3, v___x_287_);
lean_ctor_set(v___x_264_, 2, v_nextStackPos_307_);
v___x_309_ = v___x_264_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_needle_259_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_table_260_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_nextStackPos_307_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v___x_287_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
v_it_216_ = v___x_309_;
v_startPos_217_ = v_basePos_304_;
v_endPos_218_ = v_nextStackPos_307_;
goto v___jp_215_;
}
}
}
else
{
lean_object* v___x_311_; lean_object* v_nextStackPos_312_; lean_object* v_nextNeedlePos_313_; uint8_t v_decide_314_; 
lean_dec(v_basePos_272_);
v___x_311_ = lean_unsigned_to_nat(1u);
v_nextStackPos_312_ = lean_nat_add(v_stackPos_261_, v___x_311_);
lean_dec(v_stackPos_261_);
v_nextNeedlePos_313_ = lean_nat_add(v_needlePos_262_, v___x_311_);
lean_dec(v_needlePos_262_);
v_decide_314_ = lean_nat_dec_eq(v_nextNeedlePos_313_, v___x_273_);
lean_dec(v___x_273_);
if (v_decide_314_ == 0)
{
lean_object* v___x_316_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 3, v_nextNeedlePos_313_);
lean_ctor_set(v___x_264_, 2, v_nextStackPos_312_);
v___x_316_ = v___x_264_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_needle_259_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_table_260_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_nextStackPos_312_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_nextNeedlePos_313_);
v___x_316_ = v_reuseFailAlloc_318_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
v_a_213_ = v___x_316_;
goto _start;
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_dec(v_nextNeedlePos_313_);
v___x_319_ = lean_unsigned_to_nat(0u);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 3, v___x_319_);
lean_ctor_set(v___x_264_, 2, v_nextStackPos_312_);
v___x_321_ = v___x_264_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_needle_259_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_table_260_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v_nextStackPos_312_);
lean_ctor_set(v_reuseFailAlloc_322_, 3, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
v_it_227_ = v___x_321_;
goto v___jp_226_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_211_);
return v_b_214_;
}
}
v___jp_215_:
{
lean_object* v___x_219_; lean_object* v_str_220_; lean_object* v_startInclusive_221_; lean_object* v_endExclusive_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
lean_inc_ref(v_s_211_);
v___x_219_ = l_String_Slice_slice_x21(v_s_211_, v_startPos_217_, v_endPos_218_);
lean_dec(v_endPos_218_);
lean_dec(v_startPos_217_);
v_str_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc_ref(v_str_220_);
v_startInclusive_221_ = lean_ctor_get(v___x_219_, 1);
lean_inc(v_startInclusive_221_);
v_endExclusive_222_ = lean_ctor_get(v___x_219_, 2);
lean_inc(v_endExclusive_222_);
lean_dec_ref(v___x_219_);
v___x_223_ = lean_string_utf8_extract_fast(v_str_220_, v_startInclusive_221_, v_endExclusive_222_);
lean_dec(v_endExclusive_222_);
lean_dec(v_startInclusive_221_);
lean_dec_ref(v_str_220_);
v___x_224_ = lean_string_append(v_b_214_, v___x_223_);
lean_dec_ref(v___x_223_);
v_a_213_ = v_it_216_;
v_b_214_ = v___x_224_;
goto _start;
}
v___jp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_string_utf8_byte_size(v_replacement_212_);
v___x_230_ = lean_string_utf8_extract_fast(v_replacement_212_, v___x_228_, v___x_229_);
v___x_231_ = lean_string_append(v_b_214_, v___x_230_);
lean_dec_ref(v___x_230_);
v_a_213_ = v_it_227_;
v_b_214_ = v___x_231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg___boxed(lean_object* v_s_324_, lean_object* v_replacement_325_, lean_object* v_a_326_, lean_object* v_b_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_324_, v_replacement_325_, v_a_326_, v_b_327_);
lean_dec_ref(v_replacement_325_);
return v_res_328_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__1));
v___x_335_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__2);
v___x_338_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__1));
v___x_339_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
lean_ctor_set(v___x_339_, 2, v___x_336_);
lean_ctor_set(v___x_339_, 3, v___x_336_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(lean_object* v_s_340_, lean_object* v_replacement_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_343_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__3);
v___x_344_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_340_, v_replacement_341_, v___x_343_, v___x_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___boxed(lean_object* v_s_345_, lean_object* v_replacement_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(v_s_345_, v_replacement_346_);
lean_dec_ref(v_replacement_346_);
return v_res_347_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__1));
v___x_354_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__2);
v___x_357_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__1));
v___x_358_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
lean_ctor_set(v___x_358_, 2, v___x_355_);
lean_ctor_set(v___x_358_, 3, v___x_355_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(lean_object* v_s_359_, lean_object* v_replacement_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_362_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___closed__3);
v___x_363_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_359_, v_replacement_360_, v___x_362_, v___x_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg___boxed(lean_object* v_s_364_, lean_object* v_replacement_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v_s_364_, v_replacement_365_);
lean_dec_ref(v_replacement_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal(lean_object* v_v_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__0));
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_string_utf8_byte_size(v_v_369_);
v___x_373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_373_, 0, v_v_369_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_ctor_set(v___x_373_, 2, v___x_372_);
v___x_374_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v___x_373_, v___x_370_);
v___x_375_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__1));
v___x_376_ = lean_string_utf8_byte_size(v___x_374_);
v___x_377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_377_, 0, v___x_374_);
lean_ctor_set(v___x_377_, 1, v___x_371_);
lean_ctor_set(v___x_377_, 2, v___x_376_);
v___x_378_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(v___x_377_, v___x_375_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0(lean_object* v_s_379_, lean_object* v_pattern_380_, lean_object* v_replacement_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v_s_379_, v_replacement_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___boxed(lean_object* v_s_383_, lean_object* v_pattern_384_, lean_object* v_replacement_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0(v_s_383_, v_pattern_384_, v_replacement_385_);
lean_dec_ref(v_replacement_385_);
lean_dec_ref(v_pattern_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1(lean_object* v_s_387_, lean_object* v_pattern_388_, lean_object* v_replacement_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg(v_s_387_, v_replacement_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___boxed(lean_object* v_s_391_, lean_object* v_pattern_392_, lean_object* v_replacement_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1(v_s_391_, v_pattern_392_, v_replacement_393_);
lean_dec_ref(v_replacement_393_);
lean_dec_ref(v_pattern_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0(lean_object* v_s_395_, lean_object* v_replacement_396_, lean_object* v_inst_397_, lean_object* v_R_398_, lean_object* v_a_399_, lean_object* v_b_400_, lean_object* v_c_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_395_, v_replacement_396_, v_a_399_, v_b_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___boxed(lean_object* v_s_403_, lean_object* v_replacement_404_, lean_object* v_inst_405_, lean_object* v_R_406_, lean_object* v_a_407_, lean_object* v_b_408_, lean_object* v_c_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0(v_s_403_, v_replacement_404_, v_inst_405_, v_R_406_, v_a_407_, v_b_408_, v_c_409_);
lean_dec_ref(v_replacement_404_);
return v_res_410_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__1));
v___x_417_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__2);
v___x_420_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__1));
v___x_421_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
lean_ctor_set(v___x_421_, 2, v___x_418_);
lean_ctor_set(v___x_421_, 3, v___x_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(lean_object* v_s_422_, lean_object* v_replacement_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_425_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__3);
v___x_426_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_422_, v_replacement_423_, v___x_425_, v___x_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___boxed(lean_object* v_s_427_, lean_object* v_replacement_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(v_s_427_, v_replacement_428_);
lean_dec_ref(v_replacement_428_);
return v_res_429_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__1));
v___x_436_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__2);
v___x_439_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__1));
v___x_440_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
lean_ctor_set(v___x_440_, 2, v___x_437_);
lean_ctor_set(v___x_440_, 3, v___x_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(lean_object* v_s_441_, lean_object* v_replacement_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_444_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__3);
v___x_445_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0_spec__0___redArg(v_s_441_, v_replacement_442_, v___x_444_, v___x_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___boxed(lean_object* v_s_446_, lean_object* v_replacement_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(v_s_446_, v_replacement_447_);
lean_dec_ref(v_replacement_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText(lean_object* v_s_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal___closed__0));
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_string_utf8_byte_size(v_s_451_);
v___x_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_455_, 0, v_s_451_);
lean_ctor_set(v___x_455_, 1, v___x_453_);
lean_ctor_set(v___x_455_, 2, v___x_454_);
v___x_456_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__0___redArg(v___x_455_, v___x_452_);
v___x_457_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__0));
v___x_458_ = lean_string_utf8_byte_size(v___x_456_);
v___x_459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_459_, 0, v___x_456_);
lean_ctor_set(v___x_459_, 1, v___x_453_);
lean_ctor_set(v___x_459_, 2, v___x_458_);
v___x_460_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(v___x_459_, v___x_457_);
v___x_461_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText___closed__1));
v___x_462_ = lean_string_utf8_byte_size(v___x_460_);
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v___x_460_);
lean_ctor_set(v___x_463_, 1, v___x_453_);
lean_ctor_set(v___x_463_, 2, v___x_462_);
v___x_464_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(v___x_463_, v___x_461_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0(lean_object* v_s_465_, lean_object* v_pattern_466_, lean_object* v_replacement_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg(v_s_465_, v_replacement_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___boxed(lean_object* v_s_469_, lean_object* v_pattern_470_, lean_object* v_replacement_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0(v_s_469_, v_pattern_470_, v_replacement_471_);
lean_dec_ref(v_replacement_471_);
lean_dec_ref(v_pattern_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1(lean_object* v_s_473_, lean_object* v_pattern_474_, lean_object* v_replacement_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg(v_s_473_, v_replacement_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___boxed(lean_object* v_s_477_, lean_object* v_pattern_478_, lean_object* v_replacement_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1(v_s_477_, v_pattern_478_, v_replacement_479_);
lean_dec_ref(v_replacement_479_);
lean_dec_ref(v_pattern_478_);
return v_res_480_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1(uint8_t v_kind_481_, lean_object* v_as_482_, size_t v_i_483_, size_t v_stop_484_, lean_object* v_b_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = lean_usize_dec_eq(v_i_483_, v_stop_484_);
if (v___x_486_ == 0)
{
lean_object* v_kinds_487_; lean_object* v_htmls_488_; lean_object* v_strs_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_503_; 
v_kinds_487_ = lean_ctor_get(v_b_485_, 0);
v_htmls_488_ = lean_ctor_get(v_b_485_, 1);
v_strs_489_ = lean_ctor_get(v_b_485_, 2);
v_isSharedCheck_503_ = !lean_is_exclusive(v_b_485_);
if (v_isSharedCheck_503_ == 0)
{
v___x_491_ = v_b_485_;
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_strs_489_);
lean_inc(v_htmls_488_);
lean_inc(v_kinds_487_);
lean_dec(v_b_485_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_sub(v_i_483_, v___x_493_);
v___x_495_ = lean_array_uget_borrowed(v_as_482_, v___x_494_);
v___x_496_ = lean_box(v_kind_481_);
v___x_497_ = lean_array_push(v_kinds_487_, v___x_496_);
lean_inc(v___x_495_);
v___x_498_ = lean_array_push(v_htmls_488_, v___x_495_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_498_);
lean_ctor_set(v___x_491_, 0, v___x_497_);
v___x_500_ = v___x_491_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_strs_489_);
v___x_500_ = v_reuseFailAlloc_502_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
v_i_483_ = v___x_494_;
v_b_485_ = v___x_500_;
goto _start;
}
}
}
else
{
return v_b_485_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_kind_481_ = stack[0].m_num;
lean_object* v_as_482_ = stack[1].m_obj;
size_t v_i_483_ = stack[2].m_num;
size_t v_stop_484_ = stack[3].m_num;
lean_object* v_b_485_ = stack[4].m_obj;
lean_object* v_res_504_;
v_res_504_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1(v_kind_481_, v_as_482_, v_i_483_, v_stop_484_, v_b_485_);
stack->m_obj
 = v_res_504_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1___boxed(lean_object* v_kind_505_, lean_object* v_as_506_, lean_object* v_i_507_, lean_object* v_stop_508_, lean_object* v_b_509_){
_start:
{
uint8_t v_kind_boxed_510_; size_t v_i_boxed_511_; size_t v_stop_boxed_512_; lean_object* v_res_513_; 
v_kind_boxed_510_ = lean_unbox(v_kind_505_);
v_i_boxed_511_ = lean_unbox_usize(v_i_507_);
lean_dec(v_i_507_);
v_stop_boxed_512_ = lean_unbox_usize(v_stop_508_);
lean_dec(v_stop_508_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1(v_kind_boxed_510_, v_as_506_, v_i_boxed_511_, v_stop_boxed_512_, v_b_509_);
lean_dec_ref(v_as_506_);
return v_res_513_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(lean_object* v_as_514_, size_t v_i_515_, size_t v_stop_516_, lean_object* v_b_517_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = lean_usize_dec_eq(v_i_515_, v_stop_516_);
if (v___x_518_ == 0)
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; lean_object* v_fst_522_; lean_object* v_snd_523_; lean_object* v_kinds_524_; lean_object* v_htmls_525_; lean_object* v_strs_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_539_; 
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_sub(v_i_515_, v___x_519_);
v___x_521_ = lean_array_uget_borrowed(v_as_514_, v___x_520_);
v_fst_522_ = lean_ctor_get(v___x_521_, 0);
v_snd_523_ = lean_ctor_get(v___x_521_, 1);
v_kinds_524_ = lean_ctor_get(v_b_517_, 0);
v_htmls_525_ = lean_ctor_get(v_b_517_, 1);
v_strs_526_ = lean_ctor_get(v_b_517_, 2);
v_isSharedCheck_539_ = !lean_is_exclusive(v_b_517_);
if (v_isSharedCheck_539_ == 0)
{
v___x_528_ = v_b_517_;
v_isShared_529_ = v_isSharedCheck_539_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_strs_526_);
lean_inc(v_htmls_525_);
lean_inc(v_kinds_524_);
lean_dec(v_b_517_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_539_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_530_ = 1;
v___x_531_ = lean_box(v___x_530_);
v___x_532_ = lean_array_push(v_kinds_524_, v___x_531_);
lean_inc(v_snd_523_);
v___x_533_ = lean_array_push(v_strs_526_, v_snd_523_);
lean_inc(v_fst_522_);
v___x_534_ = lean_array_push(v___x_533_, v_fst_522_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 2, v___x_534_);
lean_ctor_set(v___x_528_, 0, v___x_532_);
v___x_536_ = v___x_528_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_htmls_525_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v___x_534_);
v___x_536_ = v_reuseFailAlloc_538_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
v_i_515_ = v___x_520_;
v_b_517_ = v___x_536_;
goto _start;
}
}
}
else
{
return v_b_517_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_514_ = stack[0].m_obj;
size_t v_i_515_ = stack[1].m_num;
size_t v_stop_516_ = stack[2].m_num;
lean_object* v_b_517_ = stack[3].m_obj;
lean_object* v_res_540_;
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(v_as_514_, v_i_515_, v_stop_516_, v_b_517_);
stack->m_obj
 = v_res_540_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0___boxed(lean_object* v_as_541_, lean_object* v_i_542_, lean_object* v_stop_543_, lean_object* v_b_544_){
_start:
{
size_t v_i_boxed_545_; size_t v_stop_boxed_546_; lean_object* v_res_547_; 
v_i_boxed_545_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_stop_boxed_546_ = lean_unbox_usize(v_stop_543_);
lean_dec(v_stop_543_);
v_res_547_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(v_as_541_, v_i_boxed_545_, v_stop_boxed_546_, v_b_544_);
lean_dec_ref(v_as_541_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go(lean_object* v_acc_552_, lean_object* v_q_553_){
_start:
{
lean_object* v_kinds_554_; lean_object* v_htmls_555_; lean_object* v_strs_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_687_; 
v_kinds_554_ = lean_ctor_get(v_q_553_, 0);
v_htmls_555_ = lean_ctor_get(v_q_553_, 1);
v_strs_556_ = lean_ctor_get(v_q_553_, 2);
v_isSharedCheck_687_ = !lean_is_exclusive(v_q_553_);
if (v_isSharedCheck_687_ == 0)
{
v___x_558_ = v_q_553_;
v_isShared_559_ = v_isSharedCheck_687_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_strs_556_);
lean_inc(v_htmls_555_);
lean_inc(v_kinds_554_);
lean_dec(v_q_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_687_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_560_ = lean_array_get_size(v_kinds_554_);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_nat_dec_eq(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_kind_565_; lean_object* v___x_566_; lean_object* v_q_568_; 
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_sub(v___x_560_, v___x_563_);
v_kind_565_ = lean_array_fget(v_kinds_554_, v___x_564_);
lean_dec(v___x_564_);
v___x_566_ = lean_array_pop(v_kinds_554_);
lean_inc_ref(v_strs_556_);
lean_inc_ref(v_htmls_555_);
lean_inc_ref(v___x_566_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_566_);
v_q_568_ = v___x_558_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_htmls_555_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_strs_556_);
v_q_568_ = v_reuseFailAlloc_686_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
uint8_t v___x_569_; 
v___x_569_ = lean_unbox(v_kind_565_);
switch(v___x_569_)
{
case 0:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_value_573_; lean_object* v___x_574_; lean_object* v_q_575_; 
lean_dec_ref(v_q_568_);
v___x_570_ = l_Lean_instInhabitedHtml_default;
v___x_571_ = lean_array_get_size(v_htmls_555_);
v___x_572_ = lean_nat_sub(v___x_571_, v___x_563_);
v_value_573_ = lean_array_get(v___x_570_, v_htmls_555_, v___x_572_);
lean_dec(v___x_572_);
v___x_574_ = lean_array_pop(v_htmls_555_);
lean_inc_ref(v_strs_556_);
lean_inc_ref(v___x_574_);
lean_inc_ref(v___x_566_);
v_q_575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_575_, 0, v___x_566_);
lean_ctor_set(v_q_575_, 1, v___x_574_);
lean_ctor_set(v_q_575_, 2, v_strs_556_);
switch(lean_obj_tag(v_value_573_))
{
case 0:
{
lean_object* v_tag_576_; lean_object* v_attrs_577_; lean_object* v_children_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref_known(v_q_575_, 3);
v_tag_576_ = lean_ctor_get(v_value_573_, 0);
v_attrs_577_ = lean_ctor_get(v_value_573_, 1);
v_children_578_ = lean_ctor_get(v_value_573_, 2);
v_isSharedCheck_625_ = !lean_is_exclusive(v_value_573_);
if (v_isSharedCheck_625_ == 0)
{
v___x_580_ = v_value_573_;
v_isShared_581_ = v_isSharedCheck_625_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_children_578_);
lean_inc(v_attrs_577_);
lean_inc(v_tag_576_);
lean_dec(v_value_573_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_625_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___y_583_; lean_object* v___y_589_; uint8_t v___x_595_; 
v___x_595_ = l_Lean_Html_isEmpty(v_children_578_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_596_ = 3;
v___x_597_ = lean_box(v___x_596_);
v___x_598_ = lean_array_push(v___x_566_, v___x_597_);
lean_inc_ref(v_tag_576_);
v___x_599_ = lean_array_push(v_strs_556_, v_tag_576_);
v___x_600_ = lean_array_push(v___x_598_, v_kind_565_);
v___x_601_ = lean_array_push(v___x_574_, v_children_578_);
v___x_602_ = 2;
v___x_603_ = lean_box(v___x_602_);
v___x_604_ = lean_array_push(v___x_600_, v___x_603_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 2, v___x_599_);
lean_ctor_set(v___x_580_, 1, v___x_601_);
lean_ctor_set(v___x_580_, 0, v___x_604_);
v___x_606_ = v___x_580_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v___x_599_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
v___y_589_ = v___x_606_;
goto v___jp_588_;
}
}
else
{
uint8_t v___x_608_; 
lean_dec_ref(v_children_578_);
lean_dec(v_kind_565_);
lean_inc_ref(v_tag_576_);
v___x_608_ = l_Lean_Html_isVoidElement(v_tag_576_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_609_ = 3;
v___x_610_ = lean_box(v___x_609_);
v___x_611_ = lean_array_push(v___x_566_, v___x_610_);
lean_inc_ref(v_tag_576_);
v___x_612_ = lean_array_push(v_strs_556_, v_tag_576_);
v___x_613_ = 2;
v___x_614_ = lean_box(v___x_613_);
v___x_615_ = lean_array_push(v___x_611_, v___x_614_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 2, v___x_612_);
lean_ctor_set(v___x_580_, 1, v___x_574_);
lean_ctor_set(v___x_580_, 0, v___x_615_);
v___x_617_ = v___x_580_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v___x_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
v___y_589_ = v___x_617_;
goto v___jp_588_;
}
}
else
{
uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_619_ = 4;
v___x_620_ = lean_box(v___x_619_);
v___x_621_ = lean_array_push(v___x_566_, v___x_620_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 2, v_strs_556_);
lean_ctor_set(v___x_580_, 1, v___x_574_);
lean_ctor_set(v___x_580_, 0, v___x_621_);
v___x_623_ = v___x_580_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_strs_556_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
v___y_589_ = v___x_623_;
goto v___jp_588_;
}
}
}
v___jp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__0___redArg___closed__0));
v___x_585_ = lean_string_append(v___x_584_, v_tag_576_);
lean_dec_ref(v_tag_576_);
v___x_586_ = lean_string_append(v_acc_552_, v___x_585_);
lean_dec_ref(v___x_585_);
v_acc_552_ = v___x_586_;
v_q_553_ = v___y_583_;
goto _start;
}
v___jp_588_:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_array_get_size(v_attrs_577_);
v___x_591_ = lean_nat_dec_lt(v___x_561_, v___x_590_);
if (v___x_591_ == 0)
{
lean_dec_ref(v_attrs_577_);
v___y_583_ = v___y_589_;
goto v___jp_582_;
}
else
{
size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_usize_of_nat(v___x_590_);
v___x_593_ = ((size_t)0ULL);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__0(v_attrs_577_, v___x_592_, v___x_593_, v___y_589_);
lean_dec_ref(v_attrs_577_);
v___y_583_ = v___x_594_;
goto v___jp_582_;
}
}
}
}
case 1:
{
lean_object* v_a_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec_ref(v___x_574_);
lean_dec_ref(v___x_566_);
lean_dec(v_kind_565_);
lean_dec_ref(v_strs_556_);
v_a_626_ = lean_ctor_get(v_value_573_, 0);
lean_inc_ref(v_a_626_);
lean_dec_ref_known(v_value_573_, 1);
v___x_627_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText(v_a_626_);
v___x_628_ = lean_string_append(v_acc_552_, v___x_627_);
lean_dec_ref(v___x_627_);
v_acc_552_ = v___x_628_;
v_q_553_ = v_q_575_;
goto _start;
}
case 2:
{
lean_object* v_a_630_; lean_object* v___x_631_; 
lean_dec_ref(v___x_574_);
lean_dec_ref(v___x_566_);
lean_dec(v_kind_565_);
lean_dec_ref(v_strs_556_);
v_a_630_ = lean_ctor_get(v_value_573_, 0);
lean_inc_ref(v_a_630_);
lean_dec_ref_known(v_value_573_, 1);
v___x_631_ = lean_string_append(v_acc_552_, v_a_630_);
lean_dec_ref(v_a_630_);
v_acc_552_ = v___x_631_;
v_q_553_ = v_q_575_;
goto _start;
}
default: 
{
lean_object* v_a_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
lean_dec_ref(v___x_574_);
lean_dec_ref(v___x_566_);
lean_dec_ref(v_strs_556_);
v_a_633_ = lean_ctor_get(v_value_573_, 0);
lean_inc_ref(v_a_633_);
lean_dec_ref_known(v_value_573_, 1);
v___x_634_ = lean_array_get_size(v_a_633_);
v___x_635_ = lean_nat_dec_lt(v___x_561_, v___x_634_);
if (v___x_635_ == 0)
{
lean_dec_ref(v_a_633_);
lean_dec(v_kind_565_);
v_q_553_ = v_q_575_;
goto _start;
}
else
{
size_t v___x_637_; size_t v___x_638_; uint8_t v___x_639_; lean_object* v___x_640_; 
v___x_637_ = lean_usize_of_nat(v___x_634_);
v___x_638_ = ((size_t)0ULL);
v___x_639_ = lean_unbox(v_kind_565_);
lean_dec(v_kind_565_);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_go_spec__1(v___x_639_, v_a_633_, v___x_637_, v___x_638_, v_q_575_);
lean_dec_ref(v_a_633_);
v_q_553_ = v___x_640_;
goto _start;
}
}
}
}
case 1:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_str_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_str_649_; lean_object* v___x_650_; lean_object* v_q_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
lean_dec_ref(v_q_568_);
lean_dec(v_kind_565_);
v___x_642_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_643_ = lean_array_get_size(v_strs_556_);
v___x_644_ = lean_nat_sub(v___x_643_, v___x_563_);
v_str_645_ = lean_array_get(v___x_642_, v_strs_556_, v___x_644_);
lean_dec(v___x_644_);
v___x_646_ = lean_array_pop(v_strs_556_);
v___x_647_ = lean_array_get_size(v___x_646_);
v___x_648_ = lean_nat_sub(v___x_647_, v___x_563_);
v_str_649_ = lean_array_get(v___x_642_, v___x_646_, v___x_648_);
lean_dec(v___x_648_);
v___x_650_ = lean_array_pop(v___x_646_);
v_q_651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_651_, 0, v___x_566_);
lean_ctor_set(v_q_651_, 1, v_htmls_555_);
lean_ctor_set(v_q_651_, 2, v___x_650_);
v___x_652_ = lean_string_utf8_byte_size(v_str_649_);
v___x_653_ = lean_nat_dec_eq(v___x_652_, v___x_561_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_654_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0));
v___x_655_ = lean_string_append(v___x_654_, v_str_645_);
lean_dec(v_str_645_);
v___x_656_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__1));
v___x_657_ = lean_string_append(v___x_655_, v___x_656_);
v___x_658_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal(v_str_649_);
v___x_659_ = lean_string_append(v___x_657_, v___x_658_);
lean_dec_ref(v___x_658_);
v___x_660_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeAttrVal_spec__1___redArg___closed__0));
v___x_661_ = lean_string_append(v___x_659_, v___x_660_);
v___x_662_ = lean_string_append(v_acc_552_, v___x_661_);
lean_dec_ref(v___x_661_);
v_acc_552_ = v___x_662_;
v_q_553_ = v_q_651_;
goto _start;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v_str_649_);
v___x_664_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__0));
v___x_665_ = lean_string_append(v___x_664_, v_str_645_);
lean_dec(v_str_645_);
v___x_666_ = lean_string_append(v_acc_552_, v___x_665_);
lean_dec_ref(v___x_665_);
v_acc_552_ = v___x_666_;
v_q_553_ = v_q_651_;
goto _start;
}
}
case 2:
{
uint32_t v___x_668_; lean_object* v___x_669_; 
lean_dec_ref(v___x_566_);
lean_dec(v_kind_565_);
lean_dec_ref(v_strs_556_);
lean_dec_ref(v_htmls_555_);
v___x_668_ = 62;
v___x_669_ = lean_string_push(v_acc_552_, v___x_668_);
v_acc_552_ = v___x_669_;
v_q_553_ = v_q_568_;
goto _start;
}
case 3:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_str_674_; lean_object* v___x_675_; lean_object* v_q_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec_ref(v_q_568_);
lean_dec(v_kind_565_);
v___x_671_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_672_ = lean_array_get_size(v_strs_556_);
v___x_673_ = lean_nat_sub(v___x_672_, v___x_563_);
v_str_674_ = lean_array_get(v___x_671_, v_strs_556_, v___x_673_);
lean_dec(v___x_673_);
v___x_675_ = lean_array_pop(v_strs_556_);
v_q_676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_676_, 0, v___x_566_);
lean_ctor_set(v_q_676_, 1, v_htmls_555_);
lean_ctor_set(v_q_676_, 2, v___x_675_);
v___x_677_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__2));
v___x_678_ = lean_string_append(v___x_677_, v_str_674_);
lean_dec(v_str_674_);
v___x_679_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lean_Data_Html_Printer_0__Lean_Html_render_escapeText_spec__1___redArg___closed__0));
v___x_680_ = lean_string_append(v___x_678_, v___x_679_);
v___x_681_ = lean_string_append(v_acc_552_, v___x_680_);
lean_dec_ref(v___x_680_);
v_acc_552_ = v___x_681_;
v_q_553_ = v_q_676_;
goto _start;
}
default: 
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec_ref(v___x_566_);
lean_dec(v_kind_565_);
lean_dec_ref(v_strs_556_);
lean_dec_ref(v_htmls_555_);
v___x_683_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go___closed__3));
v___x_684_ = lean_string_append(v_acc_552_, v___x_683_);
v_acc_552_ = v___x_684_;
v_q_553_ = v_q_568_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_558_);
lean_dec_ref(v_strs_556_);
lean_dec_ref(v_htmls_555_);
lean_dec_ref(v_kinds_554_);
return v_acc_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_render(lean_object* v_h_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_696_ = ((lean_object*)(l___private_Lean_Data_Html_Printer_0__Lean_Html_RenderWorkItemStack_popStr_x21___closed__0));
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_mk_empty_array_with_capacity(v___x_697_);
v___x_699_ = ((lean_object*)(l_Lean_Html_render___closed__0));
v___x_700_ = lean_array_push(v___x_698_, v_h_695_);
v___x_701_ = ((lean_object*)(l_Lean_Html_render___closed__1));
v___x_702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_702_, 0, v___x_699_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
lean_ctor_set(v___x_702_, 2, v___x_701_);
v___x_703_ = l___private_Lean_Data_Html_Printer_0__Lean_Html_render_go(v___x_696_, v___x_702_);
return v___x_703_;
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
