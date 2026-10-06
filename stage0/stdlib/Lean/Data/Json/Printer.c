// Lean compiler output
// Module: Lean.Data.Json.Printer
// Imports: public import Lean.Data.Format public import Lean.Data.Json.Basic import Init.Data.String.Search import Init.Data.UInt.Lemmas import Init.Omega
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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static const lean_sarray_object l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_sarray_object) + 256, .m_other = 1, .m_tag = 248}, .m_size = 256, .m_capacity = 256, .m_data = {1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1}};
static const lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable___closed__0 = (const lean_object*)&l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable = (const lean_object*)&l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable___closed__0_value;
static const lean_string_object l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\u"};
static const lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__0 = (const lean_object*)&l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__0_value;
static const lean_string_object l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\r"};
static const lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1 = (const lean_object*)&l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1_value;
static const lean_string_object l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\n"};
static const lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2 = (const lean_object*)&l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2_value;
static const lean_string_object l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\\\"};
static const lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3 = (const lean_object*)&l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3_value;
static const lean_string_object l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\\""};
static const lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4 = (const lean_object*)&l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_escape___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_escape___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_renderString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_Lean_Json_renderString___closed__0 = (const lean_object*)&l_Lean_Json_renderString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_render_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Json_render_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_render___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Json_render___closed__0 = (const lean_object*)&l_Lean_Json_render___closed__0_value;
static const lean_ctor_object l_Lean_Json_render___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_render___closed__0_value)}};
static const lean_object* l_Lean_Json_render___closed__1 = (const lean_object*)&l_Lean_Json_render___closed__1_value;
static const lean_string_object l_Lean_Json_render___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Json_render___closed__2 = (const lean_object*)&l_Lean_Json_render___closed__2_value;
static const lean_ctor_object l_Lean_Json_render___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_render___closed__2_value)}};
static const lean_object* l_Lean_Json_render___closed__3 = (const lean_object*)&l_Lean_Json_render___closed__3_value;
static const lean_string_object l_Lean_Json_render___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Json_render___closed__4 = (const lean_object*)&l_Lean_Json_render___closed__4_value;
static const lean_ctor_object l_Lean_Json_render___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_render___closed__4_value)}};
static const lean_object* l_Lean_Json_render___closed__5 = (const lean_object*)&l_Lean_Json_render___closed__5_value;
static const lean_string_object l_Lean_Json_render___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Json_render___closed__6 = (const lean_object*)&l_Lean_Json_render___closed__6_value;
static const lean_ctor_object l_Lean_Json_render___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_render___closed__6_value)}};
static const lean_object* l_Lean_Json_render___closed__7 = (const lean_object*)&l_Lean_Json_render___closed__7_value;
static const lean_ctor_object l_Lean_Json_render___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Json_render___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Json_render___closed__8 = (const lean_object*)&l_Lean_Json_render___closed__8_value;
static const lean_string_object l_Lean_Json_render___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Json_render___closed__9 = (const lean_object*)&l_Lean_Json_render___closed__9_value;
static lean_once_cell_t l_Lean_Json_render___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json_render___closed__11;
static lean_once_cell_t l_Lean_Json_render___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json_render___closed__12;
static const lean_ctor_object l_Lean_Json_render___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_render___closed__9_value)}};
static const lean_object* l_Lean_Json_render___closed__13 = (const lean_object*)&l_Lean_Json_render___closed__13_value;
static const lean_string_object l_Lean_Json_render___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Json_render___closed__10 = (const lean_object*)&l_Lean_Json_render___closed__10_value;
static const lean_ctor_object l_Lean_Json_render___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_render___closed__10_value)}};
static const lean_object* l_Lean_Json_render___closed__14 = (const lean_object*)&l_Lean_Json_render___closed__14_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_render___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Json_render___closed__15 = (const lean_object*)&l_Lean_Json_render___closed__15_value;
static lean_once_cell_t l_Lean_Json_render___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json_render___closed__17;
static lean_once_cell_t l_Lean_Json_render___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json_render___closed__18;
static const lean_ctor_object l_Lean_Json_render___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_render___closed__15_value)}};
static const lean_object* l_Lean_Json_render___closed__19 = (const lean_object*)&l_Lean_Json_render___closed__19_value;
static const lean_string_object l_Lean_Json_render___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Json_render___closed__16 = (const lean_object*)&l_Lean_Json_render___closed__16_value;
static const lean_ctor_object l_Lean_Json_render___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Json_render___closed__16_value)}};
static const lean_object* l_Lean_Json_render___closed__20 = (const lean_object*)&l_Lean_Json_render___closed__20_value;
LEAN_EXPORT lean_object* l_Lean_Json_render(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_pretty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushObjectFieldKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popValue_x21(lean_object*);
static const lean_string_object l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0 = (const lean_object*)&l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0 = (const lean_object*)&l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0_value;
static const lean_array_object l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1 = (const lean_object*)&l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(lean_object*, lean_object*);
static const lean_array_object l_Lean_Json_compress___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Json_compress___closed__0 = (const lean_object*)&l_Lean_Json_compress___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_compress(lean_object*);
static const lean_closure_object l_Lean_Json_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_render, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instToFormat___closed__0 = (const lean_object*)&l_Lean_Json_instToFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instToFormat = (const lean_object*)&l_Lean_Json_instToFormat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_instToString___lam__0(lean_object*);
static const lean_closure_object l_Lean_Json_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instToString___closed__0 = (const lean_object*)&l_Lean_Json_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instToString = (const lean_object*)&l_Lean_Json_instToString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(lean_object* v_acc_524_, uint32_t v_c_525_){
_start:
{
uint32_t v___x_550_; uint8_t v___x_551_; 
v___x_550_ = 34;
v___x_551_ = lean_uint32_dec_eq(v_c_525_, v___x_550_);
if (v___x_551_ == 0)
{
uint32_t v___x_552_; uint8_t v___x_553_; 
v___x_552_ = 92;
v___x_553_ = lean_uint32_dec_eq(v_c_525_, v___x_552_);
if (v___x_553_ == 0)
{
uint32_t v___x_554_; uint8_t v___x_555_; 
v___x_554_ = 10;
v___x_555_ = lean_uint32_dec_eq(v_c_525_, v___x_554_);
if (v___x_555_ == 0)
{
uint32_t v___x_556_; uint8_t v___x_557_; 
v___x_556_ = 13;
v___x_557_ = lean_uint32_dec_eq(v_c_525_, v___x_556_);
if (v___x_557_ == 0)
{
uint32_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 32;
v___x_559_ = lean_uint32_dec_le(v___x_558_, v_c_525_);
if (v___x_559_ == 0)
{
goto v___jp_526_;
}
else
{
uint32_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = 1114111;
v___x_561_ = lean_uint32_dec_le(v_c_525_, v___x_560_);
if (v___x_561_ == 0)
{
goto v___jp_526_;
}
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_string_push(v_acc_524_, v_c_525_);
return v___x_562_;
}
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1));
v___x_564_ = lean_string_append(v_acc_524_, v___x_563_);
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2));
v___x_566_ = lean_string_append(v_acc_524_, v___x_565_);
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3));
v___x_568_ = lean_string_append(v_acc_524_, v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4));
v___x_570_ = lean_string_append(v_acc_524_, v___x_569_);
return v___x_570_;
}
v___jp_526_:
{
lean_object* v_n_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint32_t v_d1_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint32_t v_d2_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint32_t v_d3_541_; lean_object* v___x_542_; uint32_t v_d4_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_n_527_ = lean_uint32_to_nat(v_c_525_);
v___x_528_ = lean_unsigned_to_nat(4096u);
v___x_529_ = lean_unsigned_to_nat(12u);
v___x_530_ = lean_nat_shiftr(v_n_527_, v___x_529_);
v_d1_531_ = l_Nat_digitChar(v___x_530_);
lean_dec(v___x_530_);
v___x_532_ = lean_nat_mod(v_n_527_, v___x_528_);
v___x_533_ = lean_unsigned_to_nat(256u);
v___x_534_ = lean_unsigned_to_nat(8u);
v___x_535_ = lean_nat_shiftr(v___x_532_, v___x_534_);
lean_dec(v___x_532_);
v_d2_536_ = l_Nat_digitChar(v___x_535_);
lean_dec(v___x_535_);
v___x_537_ = lean_nat_mod(v_n_527_, v___x_533_);
v___x_538_ = lean_unsigned_to_nat(16u);
v___x_539_ = lean_unsigned_to_nat(4u);
v___x_540_ = lean_nat_shiftr(v___x_537_, v___x_539_);
lean_dec(v___x_537_);
v_d3_541_ = l_Nat_digitChar(v___x_540_);
lean_dec(v___x_540_);
v___x_542_ = lean_nat_mod(v_n_527_, v___x_538_);
lean_dec(v_n_527_);
v_d4_543_ = l_Nat_digitChar(v___x_542_);
lean_dec(v___x_542_);
v___x_544_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__0));
v___x_545_ = lean_string_append(v_acc_524_, v___x_544_);
v___x_546_ = lean_string_push(v___x_545_, v_d1_531_);
v___x_547_ = lean_string_push(v___x_546_, v_d2_536_);
v___x_548_ = lean_string_push(v___x_547_, v_d3_541_);
v___x_549_ = lean_string_push(v___x_548_, v_d4_543_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___boxed(lean_object* v_acc_571_, lean_object* v_c_572_){
_start:
{
uint32_t v_c_boxed_573_; lean_object* v_res_574_; 
v_c_boxed_573_ = lean_unbox_uint32(v_c_572_);
lean_dec(v_c_572_);
v_res_574_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_571_, v_c_boxed_573_);
return v_res_574_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(lean_object* v_s_575_, lean_object* v_i_576_){
_start:
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_string_utf8_byte_size(v_s_575_);
v___x_578_ = lean_nat_dec_lt(v_i_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_dec(v_i_576_);
return v___x_578_;
}
else
{
uint8_t v_byte_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; uint8_t v___x_583_; uint8_t v___x_584_; 
lean_inc(v_i_576_);
v_byte_579_ = lean_string_get_byte_fast(v_s_575_, v_i_576_);
v___x_580_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable));
v___x_581_ = lean_uint8_to_nat(v_byte_579_);
v___x_582_ = lean_byte_array_fget(v___x_580_, v___x_581_);
v___x_583_ = 0;
v___x_584_ = lean_uint8_dec_eq(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
lean_dec(v_i_576_);
return v___x_578_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_nat_add(v_i_576_, v___x_585_);
lean_dec(v_i_576_);
v_i_576_ = v___x_586_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go___boxed(lean_object* v_s_588_, lean_object* v_i_589_){
_start:
{
uint8_t v_res_590_; lean_object* v_r_591_; 
v_res_590_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(v_s_588_, v_i_589_);
lean_dec_ref(v_s_588_);
v_r_591_ = lean_box(v_res_590_);
return v_r_591_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(lean_object* v_s_592_){
_start:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(v_s_592_, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape___boxed(lean_object* v_s_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_595_);
lean_dec_ref(v_s_595_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape___lam__0(lean_object* v___x_598_, lean_object* v_s_599_, lean_object* v_it_600_, lean_object* v_acc_601_, lean_object* v_hP_602_, lean_object* v_recur_603_){
_start:
{
uint8_t v_decide_604_; 
v_decide_604_ = lean_nat_dec_eq(v_it_600_, v___x_598_);
if (v_decide_604_ == 0)
{
uint32_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_605_ = lean_string_utf8_get_fast(v_s_599_, v_it_600_);
v___x_606_ = lean_string_utf8_next_fast(v_s_599_, v_it_600_);
v___x_607_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_601_, v___x_605_);
v___x_608_ = lean_apply_4(v_recur_603_, v___x_606_, v___x_607_, lean_box(0), lean_box(0));
return v___x_608_;
}
else
{
lean_dec_ref(v_recur_603_);
return v_acc_601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape___lam__0___boxed(lean_object* v___x_609_, lean_object* v_s_610_, lean_object* v_it_611_, lean_object* v_acc_612_, lean_object* v_hP_613_, lean_object* v_recur_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Json_escape___lam__0(v___x_609_, v_s_610_, v_it_611_, v_acc_612_, v_hP_613_, v_recur_614_);
lean_dec(v_it_611_);
lean_dec_ref(v_s_610_);
lean_dec(v___x_609_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object* v_s_616_, lean_object* v_acc_617_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_616_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
v___x_619_ = lean_string_append(v_acc_617_, v_s_616_);
lean_dec_ref(v_s_616_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___f_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_620_ = lean_string_utf8_byte_size(v_s_616_);
v___f_621_ = lean_alloc_closure((void*)(l_Lean_Json_escape___lam__0___boxed), 6, 2);
lean_closure_set(v___f_621_, 0, v___x_620_);
lean_closure_set(v___f_621_, 1, v_s_616_);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_621_, v___x_622_, v_acc_617_, lean_box(0));
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object* v_s_625_, lean_object* v_acc_626_){
_start:
{
lean_object* v___x_627_; lean_object* v_acc_628_; uint8_t v___x_629_; 
v___x_627_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_628_ = lean_string_append(v_acc_626_, v___x_627_);
v___x_629_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_625_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_string_append(v_acc_628_, v_s_625_);
lean_dec_ref(v_s_625_);
v___x_631_ = lean_string_append(v___x_630_, v___x_627_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v___f_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_632_ = lean_string_utf8_byte_size(v_s_625_);
v___f_633_ = lean_alloc_closure((void*)(l_Lean_Json_escape___lam__0___boxed), 6, 2);
lean_closure_set(v___f_633_, 0, v___x_632_);
lean_closure_set(v___f_633_, 1, v_s_625_);
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_633_, v___x_634_, v_acc_628_, lean_box(0));
v___x_636_ = lean_string_append(v___x_635_, v___x_627_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_render_spec__3(lean_object* v_a_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = lean_nat_to_int(v_a_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(lean_object* v___x_639_, lean_object* v_k_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
uint8_t v_decide_643_; 
v_decide_643_ = lean_nat_dec_eq(v_a_641_, v___x_639_);
if (v_decide_643_ == 0)
{
uint32_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_string_utf8_get_fast(v_k_640_, v_a_641_);
v___x_645_ = lean_string_utf8_next_fast(v_k_640_, v_a_641_);
lean_dec(v_a_641_);
v___x_646_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_b_642_, v___x_644_);
v_a_641_ = v___x_645_;
v_b_642_ = v___x_646_;
goto _start;
}
else
{
lean_dec(v_a_641_);
return v_b_642_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg___boxed(lean_object* v___x_648_, lean_object* v_k_649_, lean_object* v_a_650_, lean_object* v_b_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_648_, v_k_649_, v_a_650_, v_b_651_);
lean_dec_ref(v_k_649_);
lean_dec(v___x_648_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Json_render_spec__2_spec__2(lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
if (lean_obj_tag(v_x_655_) == 0)
{
lean_dec(v_x_653_);
return v_x_654_;
}
else
{
lean_object* v_head_656_; lean_object* v_tail_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_666_; 
v_head_656_ = lean_ctor_get(v_x_655_, 0);
v_tail_657_ = lean_ctor_get(v_x_655_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_666_ == 0)
{
v___x_659_ = v_x_655_;
v_isShared_660_ = v_isSharedCheck_666_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_tail_657_);
lean_inc(v_head_656_);
lean_dec(v_x_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_666_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
lean_inc(v_x_653_);
if (v_isShared_660_ == 0)
{
lean_ctor_set_tag(v___x_659_, 5);
lean_ctor_set(v___x_659_, 1, v_x_653_);
lean_ctor_set(v___x_659_, 0, v_x_654_);
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_x_654_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_x_653_);
v___x_662_ = v_reuseFailAlloc_665_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; 
v___x_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v_head_656_);
v_x_654_ = v___x_663_;
v_x_655_ = v_tail_657_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_667_) == 0)
{
lean_object* v___x_669_; 
lean_dec(v_x_668_);
v___x_669_ = lean_box(0);
return v___x_669_;
}
else
{
lean_object* v_tail_670_; 
v_tail_670_ = lean_ctor_get(v_x_667_, 1);
if (lean_obj_tag(v_tail_670_) == 0)
{
lean_object* v_head_671_; 
lean_dec(v_x_668_);
v_head_671_ = lean_ctor_get(v_x_667_, 0);
lean_inc(v_head_671_);
lean_dec_ref_known(v_x_667_, 2);
return v_head_671_;
}
else
{
lean_object* v_head_672_; lean_object* v___x_673_; 
lean_inc(v_tail_670_);
v_head_672_ = lean_ctor_get(v_x_667_, 0);
lean_inc(v_head_672_);
lean_dec_ref_known(v_x_667_, 2);
v___x_673_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Json_render_spec__2_spec__2(v_x_668_, v_head_672_, v_tail_670_);
return v___x_673_;
}
}
}
}
static lean_object* _init_l_Lean_Json_render___closed__11(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_Json_render___closed__9));
v___x_691_ = lean_string_length(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_Json_render___closed__12(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Lean_Json_render___closed__11, &l_Lean_Json_render___closed__11_once, _init_l_Lean_Json_render___closed__11);
v___x_693_ = lean_nat_to_int(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(lean_object* v_init_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_object* v_k_704_; lean_object* v_v_705_; lean_object* v_l_706_; lean_object* v_r_707_; lean_object* v___x_708_; lean_object* v___y_710_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_k_704_ = lean_ctor_get(v_x_703_, 1);
lean_inc(v_k_704_);
v_v_705_ = lean_ctor_get(v_x_703_, 2);
lean_inc(v_v_705_);
v_l_706_ = lean_ctor_get(v_x_703_, 3);
lean_inc(v_l_706_);
v_r_707_ = lean_ctor_get(v_x_703_, 4);
lean_inc(v_r_707_);
lean_dec_ref_known(v_x_703_, 5);
v___x_708_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v_init_702_, v_l_706_);
v___x_722_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v___x_723_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_k_704_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_string_append(v___x_722_, v_k_704_);
lean_dec(v_k_704_);
v___x_725_ = lean_string_append(v___x_724_, v___x_722_);
v___y_710_ = v___x_725_;
goto v___jp_709_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = lean_string_utf8_byte_size(v_k_704_);
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_726_, v_k_704_, v___x_727_, v___x_722_);
lean_dec(v_k_704_);
v___x_729_ = lean_string_append(v___x_728_, v___x_722_);
v___y_710_ = v___x_729_;
goto v___jp_709_;
}
v___jp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_711_, 0, v___y_710_);
v___x_712_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__1));
v___x_713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = lean_box(1);
v___x_715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = l_Lean_Json_render(v_v_705_);
v___x_717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = 0;
v___x_719_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*1, v___x_718_);
v___x_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_708_);
v_init_702_ = v___x_720_;
v_x_703_ = v_r_707_;
goto _start;
}
}
else
{
return v_init_702_;
}
}
}
static lean_object* _init_l_Lean_Json_render___closed__17(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = ((lean_object*)(l_Lean_Json_render___closed__15));
v___x_732_ = lean_string_length(v___x_731_);
return v___x_732_;
}
}
static lean_object* _init_l_Lean_Json_render___closed__18(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_obj_once(&l_Lean_Json_render___closed__17, &l_Lean_Json_render___closed__17_once, _init_l_Lean_Json_render___closed__17);
v___x_734_ = lean_nat_to_int(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_render(lean_object* v_x_740_){
_start:
{
switch(lean_obj_tag(v_x_740_))
{
case 0:
{
lean_object* v___x_741_; 
v___x_741_ = ((lean_object*)(l_Lean_Json_render___closed__1));
return v___x_741_;
}
case 1:
{
uint8_t v_b_742_; 
v_b_742_ = lean_ctor_get_uint8(v_x_740_, 0);
lean_dec_ref_known(v_x_740_, 0);
if (v_b_742_ == 0)
{
lean_object* v___x_743_; 
v___x_743_ = ((lean_object*)(l_Lean_Json_render___closed__3));
return v___x_743_;
}
else
{
lean_object* v___x_744_; 
v___x_744_ = ((lean_object*)(l_Lean_Json_render___closed__5));
return v___x_744_;
}
}
case 2:
{
lean_object* v_n_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_753_; 
v_n_745_ = lean_ctor_get(v_x_740_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_753_ == 0)
{
v___x_747_ = v_x_740_;
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_n_745_);
lean_dec(v_x_740_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_749_ = l_Lean_JsonNumber_toString(v_n_745_);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 3);
lean_ctor_set(v___x_747_, 0, v___x_749_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
case 3:
{
lean_object* v_s_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_772_; 
v_s_754_ = lean_ctor_get(v_x_740_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_772_ == 0)
{
v___x_756_ = v_x_740_;
v_isShared_757_ = v_isSharedCheck_772_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_s_754_);
lean_dec(v_x_740_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_772_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v___x_759_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_754_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_760_ = lean_string_append(v___x_758_, v_s_754_);
lean_dec_ref(v_s_754_);
v___x_761_ = lean_string_append(v___x_760_, v___x_758_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_761_);
v___x_763_ = v___x_756_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_765_ = lean_string_utf8_byte_size(v_s_754_);
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_765_, v_s_754_, v___x_766_, v___x_758_);
lean_dec_ref(v_s_754_);
v___x_768_ = lean_string_append(v___x_767_, v___x_758_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_768_);
v___x_770_ = v___x_756_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
case 4:
{
lean_object* v_elems_773_; size_t v_sz_774_; size_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v_elems_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; 
v_elems_773_ = lean_ctor_get(v_x_740_, 0);
lean_inc_ref(v_elems_773_);
lean_dec_ref_known(v_x_740_, 1);
v_sz_774_ = lean_array_size(v_elems_773_);
v___x_775_ = ((size_t)0ULL);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(v_sz_774_, v___x_775_, v_elems_773_);
v___x_777_ = lean_array_to_list(v___x_776_);
v___x_778_ = ((lean_object*)(l_Lean_Json_render___closed__8));
v_elems_779_ = l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(v___x_777_, v___x_778_);
v___x_780_ = lean_obj_once(&l_Lean_Json_render___closed__12, &l_Lean_Json_render___closed__12_once, _init_l_Lean_Json_render___closed__12);
v___x_781_ = ((lean_object*)(l_Lean_Json_render___closed__13));
v___x_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_elems_779_);
v___x_783_ = ((lean_object*)(l_Lean_Json_render___closed__14));
v___x_784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_780_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = 0;
v___x_787_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*1, v___x_786_);
return v___x_787_;
}
default: 
{
lean_object* v_kvPairs_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_kvs_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; 
v_kvPairs_788_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_kvPairs_788_);
lean_dec_ref_known(v_x_740_, 1);
v___x_789_ = lean_box(0);
v___x_790_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v___x_789_, v_kvPairs_788_);
v___x_791_ = ((lean_object*)(l_Lean_Json_render___closed__8));
v_kvs_792_ = l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(v___x_790_, v___x_791_);
v___x_793_ = lean_obj_once(&l_Lean_Json_render___closed__18, &l_Lean_Json_render___closed__18_once, _init_l_Lean_Json_render___closed__18);
v___x_794_ = ((lean_object*)(l_Lean_Json_render___closed__19));
v___x_795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v_kvs_792_);
v___x_796_ = ((lean_object*)(l_Lean_Json_render___closed__20));
v___x_797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_793_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = 0;
v___x_800_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*1, v___x_799_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(size_t v_sz_801_, size_t v_i_802_, lean_object* v_bs_803_){
_start:
{
uint8_t v___x_804_; 
v___x_804_ = lean_usize_dec_lt(v_i_802_, v_sz_801_);
if (v___x_804_ == 0)
{
return v_bs_803_;
}
else
{
lean_object* v_v_805_; lean_object* v___x_806_; lean_object* v_bs_x27_807_; lean_object* v___x_808_; size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; 
v_v_805_ = lean_array_uget(v_bs_803_, v_i_802_);
v___x_806_ = lean_unsigned_to_nat(0u);
v_bs_x27_807_ = lean_array_uset(v_bs_803_, v_i_802_, v___x_806_);
v___x_808_ = l_Lean_Json_render(v_v_805_);
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_add(v_i_802_, v___x_809_);
v___x_811_ = lean_array_uset(v_bs_x27_807_, v_i_802_, v___x_808_);
v_i_802_ = v___x_810_;
v_bs_803_ = v___x_811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1___boxed(lean_object* v_sz_813_, lean_object* v_i_814_, lean_object* v_bs_815_){
_start:
{
size_t v_sz_boxed_816_; size_t v_i_boxed_817_; lean_object* v_res_818_; 
v_sz_boxed_816_ = lean_unbox_usize(v_sz_813_);
lean_dec(v_sz_813_);
v_i_boxed_817_ = lean_unbox_usize(v_i_814_);
lean_dec(v_i_814_);
v_res_818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(v_sz_boxed_816_, v_i_boxed_817_, v_bs_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(lean_object* v___x_819_, lean_object* v___x_820_, lean_object* v_k_821_, lean_object* v_inst_822_, lean_object* v_R_823_, lean_object* v_a_824_, lean_object* v_b_825_, lean_object* v_c_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_820_, v_k_821_, v_a_824_, v_b_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___boxed(lean_object* v___x_828_, lean_object* v___x_829_, lean_object* v_k_830_, lean_object* v_inst_831_, lean_object* v_R_832_, lean_object* v_a_833_, lean_object* v_b_834_, lean_object* v_c_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(v___x_828_, v___x_829_, v_k_830_, v_inst_831_, v_R_832_, v_a_833_, v_b_834_, v_c_835_);
lean_dec_ref(v_k_830_);
lean_dec(v___x_829_);
lean_dec_ref(v___x_828_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4(lean_object* v_init_837_, lean_object* v_t_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v_init_837_, v_t_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_pretty(lean_object* v_j_840_, lean_object* v_lineWidth_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = l_Lean_Json_render(v_j_840_);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = l_Std_Format_pretty(v___x_842_, v_lineWidth_841_, v___x_843_, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_pretty___boxed(lean_object* v_j_845_, lean_object* v_lineWidth_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Json_pretty(v_j_845_, v_lineWidth_846_);
lean_dec(v_lineWidth_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___impl(uint8_t v_x_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_box(v_x_848_);
v___x_850_ = lean_obj_tag_nat(v___x_849_);
lean_dec(v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___impl___boxed(lean_object* v_x_851_){
_start:
{
uint8_t v_x_4__boxed_852_; lean_object* v_res_853_; 
v_x_4__boxed_852_ = lean_unbox(v_x_851_);
v_res_853_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___impl(v_x_4__boxed_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg(lean_object* v_k_854_){
_start:
{
lean_inc(v_k_854_);
return v_k_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg___boxed(lean_object* v_k_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg(v_k_855_);
lean_dec(v_k_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(lean_object* v_motive_857_, lean_object* v_ctorIdx_858_, uint8_t v_t_859_, lean_object* v_h_860_, lean_object* v_k_861_){
_start:
{
lean_inc(v_k_861_);
return v_k_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___boxed(lean_object* v_motive_862_, lean_object* v_ctorIdx_863_, lean_object* v_t_864_, lean_object* v_h_865_, lean_object* v_k_866_){
_start:
{
uint8_t v_t_boxed_867_; lean_object* v_res_868_; 
v_t_boxed_867_ = lean_unbox(v_t_864_);
v_res_868_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(v_motive_862_, v_ctorIdx_863_, v_t_boxed_867_, v_h_865_, v_k_866_);
lean_dec(v_k_866_);
lean_dec(v_ctorIdx_863_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(lean_object* v_json_869_){
_start:
{
lean_inc(v_json_869_);
return v_json_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg___boxed(lean_object* v_json_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(v_json_870_);
lean_dec(v_json_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(lean_object* v_motive_872_, uint8_t v_t_873_, lean_object* v_h_874_, lean_object* v_json_875_){
_start:
{
lean_inc(v_json_875_);
return v_json_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___boxed(lean_object* v_motive_876_, lean_object* v_t_877_, lean_object* v_h_878_, lean_object* v_json_879_){
_start:
{
uint8_t v_t_boxed_880_; lean_object* v_res_881_; 
v_t_boxed_880_ = lean_unbox(v_t_877_);
v_res_881_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(v_motive_876_, v_t_boxed_880_, v_h_878_, v_json_879_);
lean_dec(v_json_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(lean_object* v_arrayElem_882_){
_start:
{
lean_inc(v_arrayElem_882_);
return v_arrayElem_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg___boxed(lean_object* v_arrayElem_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(v_arrayElem_883_);
lean_dec(v_arrayElem_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(lean_object* v_motive_885_, uint8_t v_t_886_, lean_object* v_h_887_, lean_object* v_arrayElem_888_){
_start:
{
lean_inc(v_arrayElem_888_);
return v_arrayElem_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___boxed(lean_object* v_motive_889_, lean_object* v_t_890_, lean_object* v_h_891_, lean_object* v_arrayElem_892_){
_start:
{
uint8_t v_t_boxed_893_; lean_object* v_res_894_; 
v_t_boxed_893_ = lean_unbox(v_t_890_);
v_res_894_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(v_motive_889_, v_t_boxed_893_, v_h_891_, v_arrayElem_892_);
lean_dec(v_arrayElem_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(lean_object* v_arrayEnd_895_){
_start:
{
lean_inc(v_arrayEnd_895_);
return v_arrayEnd_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg___boxed(lean_object* v_arrayEnd_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(v_arrayEnd_896_);
lean_dec(v_arrayEnd_896_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(lean_object* v_motive_898_, uint8_t v_t_899_, lean_object* v_h_900_, lean_object* v_arrayEnd_901_){
_start:
{
lean_inc(v_arrayEnd_901_);
return v_arrayEnd_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___boxed(lean_object* v_motive_902_, lean_object* v_t_903_, lean_object* v_h_904_, lean_object* v_arrayEnd_905_){
_start:
{
uint8_t v_t_boxed_906_; lean_object* v_res_907_; 
v_t_boxed_906_ = lean_unbox(v_t_903_);
v_res_907_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(v_motive_902_, v_t_boxed_906_, v_h_904_, v_arrayEnd_905_);
lean_dec(v_arrayEnd_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(lean_object* v_objectField_908_){
_start:
{
lean_inc(v_objectField_908_);
return v_objectField_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg___boxed(lean_object* v_objectField_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(v_objectField_909_);
lean_dec(v_objectField_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(lean_object* v_motive_911_, uint8_t v_t_912_, lean_object* v_h_913_, lean_object* v_objectField_914_){
_start:
{
lean_inc(v_objectField_914_);
return v_objectField_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___boxed(lean_object* v_motive_915_, lean_object* v_t_916_, lean_object* v_h_917_, lean_object* v_objectField_918_){
_start:
{
uint8_t v_t_boxed_919_; lean_object* v_res_920_; 
v_t_boxed_919_ = lean_unbox(v_t_916_);
v_res_920_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(v_motive_915_, v_t_boxed_919_, v_h_917_, v_objectField_918_);
lean_dec(v_objectField_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(lean_object* v_objectEnd_921_){
_start:
{
lean_inc(v_objectEnd_921_);
return v_objectEnd_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg___boxed(lean_object* v_objectEnd_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(v_objectEnd_922_);
lean_dec(v_objectEnd_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(lean_object* v_motive_924_, uint8_t v_t_925_, lean_object* v_h_926_, lean_object* v_objectEnd_927_){
_start:
{
lean_inc(v_objectEnd_927_);
return v_objectEnd_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___boxed(lean_object* v_motive_928_, lean_object* v_t_929_, lean_object* v_h_930_, lean_object* v_objectEnd_931_){
_start:
{
uint8_t v_t_boxed_932_; lean_object* v_res_933_; 
v_t_boxed_932_ = lean_unbox(v_t_929_);
v_res_933_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(v_motive_928_, v_t_boxed_932_, v_h_930_, v_objectEnd_931_);
lean_dec(v_objectEnd_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(lean_object* v_comma_934_){
_start:
{
lean_inc(v_comma_934_);
return v_comma_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg___boxed(lean_object* v_comma_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(v_comma_935_);
lean_dec(v_comma_935_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(lean_object* v_motive_937_, uint8_t v_t_938_, lean_object* v_h_939_, lean_object* v_comma_940_){
_start:
{
lean_inc(v_comma_940_);
return v_comma_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___boxed(lean_object* v_motive_941_, lean_object* v_t_942_, lean_object* v_h_943_, lean_object* v_comma_944_){
_start:
{
uint8_t v_t_boxed_945_; lean_object* v_res_946_; 
v_t_boxed_945_ = lean_unbox(v_t_942_);
v_res_946_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(v_motive_941_, v_t_boxed_945_, v_h_943_, v_comma_944_);
lean_dec(v_comma_944_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(lean_object* v_q_947_, uint8_t v_kind_948_){
_start:
{
lean_object* v_kinds_949_; lean_object* v_values_950_; lean_object* v_objectFieldKeys_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_960_; 
v_kinds_949_ = lean_ctor_get(v_q_947_, 0);
v_values_950_ = lean_ctor_get(v_q_947_, 1);
v_objectFieldKeys_951_ = lean_ctor_get(v_q_947_, 2);
v_isSharedCheck_960_ = !lean_is_exclusive(v_q_947_);
if (v_isSharedCheck_960_ == 0)
{
v___x_953_ = v_q_947_;
v_isShared_954_ = v_isSharedCheck_960_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_objectFieldKeys_951_);
lean_inc(v_values_950_);
lean_inc(v_kinds_949_);
lean_dec(v_q_947_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_960_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_955_ = lean_box(v_kind_948_);
v___x_956_ = lean_array_push(v_kinds_949_, v___x_955_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_956_);
v___x_958_ = v___x_953_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_values_950_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_objectFieldKeys_951_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind___boxed(lean_object* v_q_961_, lean_object* v_kind_962_){
_start:
{
uint8_t v_kind_boxed_963_; lean_object* v_res_964_; 
v_kind_boxed_963_ = lean_unbox(v_kind_962_);
v_res_964_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(v_q_961_, v_kind_boxed_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushValue(lean_object* v_q_965_, lean_object* v_value_966_){
_start:
{
lean_object* v_kinds_967_; lean_object* v_values_968_; lean_object* v_objectFieldKeys_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_977_; 
v_kinds_967_ = lean_ctor_get(v_q_965_, 0);
v_values_968_ = lean_ctor_get(v_q_965_, 1);
v_objectFieldKeys_969_ = lean_ctor_get(v_q_965_, 2);
v_isSharedCheck_977_ = !lean_is_exclusive(v_q_965_);
if (v_isSharedCheck_977_ == 0)
{
v___x_971_ = v_q_965_;
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_objectFieldKeys_969_);
lean_inc(v_values_968_);
lean_inc(v_kinds_967_);
lean_dec(v_q_965_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = lean_array_push(v_values_968_, v_value_966_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v___x_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_kinds_967_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_objectFieldKeys_969_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushObjectFieldKey(lean_object* v_q_978_, lean_object* v_objectFieldKey_979_){
_start:
{
lean_object* v_kinds_980_; lean_object* v_values_981_; lean_object* v_objectFieldKeys_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_990_; 
v_kinds_980_ = lean_ctor_get(v_q_978_, 0);
v_values_981_ = lean_ctor_get(v_q_978_, 1);
v_objectFieldKeys_982_ = lean_ctor_get(v_q_978_, 2);
v_isSharedCheck_990_ = !lean_is_exclusive(v_q_978_);
if (v_isSharedCheck_990_ == 0)
{
v___x_984_ = v_q_978_;
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_objectFieldKeys_982_);
lean_inc(v_values_981_);
lean_inc(v_kinds_980_);
lean_dec(v_q_978_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_array_push(v_objectFieldKeys_982_, v_objectFieldKey_979_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 2, v___x_986_);
v___x_988_ = v___x_984_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_kinds_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_values_981_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind___redArg(lean_object* v_q_991_){
_start:
{
lean_object* v_kinds_992_; lean_object* v_values_993_; lean_object* v_objectFieldKeys_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1007_; 
v_kinds_992_ = lean_ctor_get(v_q_991_, 0);
v_values_993_ = lean_ctor_get(v_q_991_, 1);
v_objectFieldKeys_994_ = lean_ctor_get(v_q_991_, 2);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_q_991_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_996_ = v_q_991_;
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_objectFieldKeys_994_);
lean_inc(v_values_993_);
lean_inc(v_kinds_992_);
lean_dec(v_q_991_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_kind_1001_; lean_object* v___x_1002_; lean_object* v_q_1004_; 
v___x_998_ = lean_array_get_size(v_kinds_992_);
v___x_999_ = lean_unsigned_to_nat(1u);
v___x_1000_ = lean_nat_sub(v___x_998_, v___x_999_);
v_kind_1001_ = lean_array_fget(v_kinds_992_, v___x_1000_);
lean_dec(v___x_1000_);
v___x_1002_ = lean_array_pop(v_kinds_992_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1002_);
v_q_1004_ = v___x_996_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_values_993_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_objectFieldKeys_994_);
v_q_1004_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v_kind_1001_);
lean_ctor_set(v___x_1005_, 1, v_q_1004_);
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind(lean_object* v_q_1008_, lean_object* v_h_1009_){
_start:
{
lean_object* v_kinds_1010_; lean_object* v_values_1011_; lean_object* v_objectFieldKeys_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1025_; 
v_kinds_1010_ = lean_ctor_get(v_q_1008_, 0);
v_values_1011_ = lean_ctor_get(v_q_1008_, 1);
v_objectFieldKeys_1012_ = lean_ctor_get(v_q_1008_, 2);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_q_1008_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1014_ = v_q_1008_;
v_isShared_1015_ = v_isSharedCheck_1025_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_objectFieldKeys_1012_);
lean_inc(v_values_1011_);
lean_inc(v_kinds_1010_);
lean_dec(v_q_1008_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1025_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_kind_1019_; lean_object* v___x_1020_; lean_object* v_q_1022_; 
v___x_1016_ = lean_array_get_size(v_kinds_1010_);
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = lean_nat_sub(v___x_1016_, v___x_1017_);
v_kind_1019_ = lean_array_fget(v_kinds_1010_, v___x_1018_);
lean_dec(v___x_1018_);
v___x_1020_ = lean_array_pop(v_kinds_1010_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1020_);
v_q_1022_ = v___x_1014_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_values_1011_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_objectFieldKeys_1012_);
v_q_1022_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v_kind_1019_);
lean_ctor_set(v___x_1023_, 1, v_q_1022_);
return v___x_1023_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popValue_x21(lean_object* v_q_1026_){
_start:
{
lean_object* v_kinds_1027_; lean_object* v_values_1028_; lean_object* v_objectFieldKeys_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1043_; 
v_kinds_1027_ = lean_ctor_get(v_q_1026_, 0);
v_values_1028_ = lean_ctor_get(v_q_1026_, 1);
v_objectFieldKeys_1029_ = lean_ctor_get(v_q_1026_, 2);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_q_1026_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1031_ = v_q_1026_;
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_objectFieldKeys_1029_);
lean_inc(v_values_1028_);
lean_inc(v_kinds_1027_);
lean_dec(v_q_1026_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_value_1037_; lean_object* v___x_1038_; lean_object* v_q_1040_; 
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_array_get_size(v_values_1028_);
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_nat_sub(v___x_1034_, v___x_1035_);
v_value_1037_ = lean_array_get(v___x_1033_, v_values_1028_, v___x_1036_);
lean_dec(v___x_1036_);
v___x_1038_ = lean_array_pop(v_values_1028_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v___x_1038_);
v_q_1040_ = v___x_1031_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_kinds_1027_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_objectFieldKeys_1029_);
v_q_1040_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_value_1037_);
lean_ctor_set(v___x_1041_, 1, v_q_1040_);
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21(lean_object* v_q_1045_){
_start:
{
lean_object* v_kinds_1046_; lean_object* v_values_1047_; lean_object* v_objectFieldKeys_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1062_; 
v_kinds_1046_ = lean_ctor_get(v_q_1045_, 0);
v_values_1047_ = lean_ctor_get(v_q_1045_, 1);
v_objectFieldKeys_1048_ = lean_ctor_get(v_q_1045_, 2);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_q_1045_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1050_ = v_q_1045_;
v_isShared_1051_ = v_isSharedCheck_1062_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_objectFieldKeys_1048_);
lean_inc(v_values_1047_);
lean_inc(v_kinds_1046_);
lean_dec(v_q_1045_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1062_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_objectFieldKey_1056_; lean_object* v___x_1057_; lean_object* v_q_1059_; 
v___x_1052_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1053_ = lean_array_get_size(v_objectFieldKeys_1048_);
v___x_1054_ = lean_unsigned_to_nat(1u);
v___x_1055_ = lean_nat_sub(v___x_1053_, v___x_1054_);
v_objectFieldKey_1056_ = lean_array_get(v___x_1052_, v_objectFieldKeys_1048_, v___x_1055_);
lean_dec(v___x_1055_);
v___x_1057_ = lean_array_pop(v_objectFieldKeys_1048_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 2, v___x_1057_);
v_q_1059_ = v___x_1050_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_kinds_1046_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_values_1047_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v___x_1057_);
v_q_1059_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_objectFieldKey_1056_);
lean_ctor_set(v___x_1060_, 1, v_q_1059_);
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(lean_object* v_as_1063_, size_t v_i_1064_, size_t v_stop_1065_, lean_object* v_b_1066_){
_start:
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_usize_dec_eq(v_i_1064_, v_stop_1065_);
if (v___x_1067_ == 0)
{
lean_object* v_kinds_1068_; lean_object* v_values_1069_; lean_object* v_objectFieldKeys_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1085_; 
v_kinds_1068_ = lean_ctor_get(v_b_1066_, 0);
v_values_1069_ = lean_ctor_get(v_b_1066_, 1);
v_objectFieldKeys_1070_ = lean_ctor_get(v_b_1066_, 2);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_b_1066_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1072_ = v_b_1066_;
v_isShared_1073_ = v_isSharedCheck_1085_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_objectFieldKeys_1070_);
lean_inc(v_values_1069_);
lean_inc(v_kinds_1068_);
lean_dec(v_b_1066_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1085_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
size_t v___x_1074_; size_t v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1074_ = ((size_t)1ULL);
v___x_1075_ = lean_usize_sub(v_i_1064_, v___x_1074_);
v___x_1076_ = lean_array_uget_borrowed(v_as_1063_, v___x_1075_);
v___x_1077_ = 1;
v___x_1078_ = lean_box(v___x_1077_);
v___x_1079_ = lean_array_push(v_kinds_1068_, v___x_1078_);
lean_inc(v___x_1076_);
v___x_1080_ = lean_array_push(v_values_1069_, v___x_1076_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v___x_1080_);
lean_ctor_set(v___x_1072_, 0, v___x_1079_);
v___x_1082_ = v___x_1072_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v_objectFieldKeys_1070_);
v___x_1082_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
v_i_1064_ = v___x_1075_;
v_b_1066_ = v___x_1082_;
goto _start;
}
}
}
else
{
return v_b_1066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0___boxed(lean_object* v_as_1086_, lean_object* v_i_1087_, lean_object* v_stop_1088_, lean_object* v_b_1089_){
_start:
{
size_t v_i_boxed_1090_; size_t v_stop_boxed_1091_; lean_object* v_res_1092_; 
v_i_boxed_1090_ = lean_unbox_usize(v_i_1087_);
lean_dec(v_i_1087_);
v_stop_boxed_1091_ = lean_unbox_usize(v_stop_1088_);
lean_dec(v_stop_1088_);
v_res_1092_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_as_1086_, v_i_boxed_1090_, v_stop_boxed_1091_, v_b_1089_);
lean_dec_ref(v_as_1086_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(lean_object* v_init_1093_, lean_object* v_x_1094_){
_start:
{
if (lean_obj_tag(v_x_1094_) == 0)
{
lean_object* v_k_1095_; lean_object* v_v_1096_; lean_object* v_l_1097_; lean_object* v_r_1098_; lean_object* v___x_1099_; lean_object* v_kinds_1100_; lean_object* v_values_1101_; lean_object* v_objectFieldKeys_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1115_; 
v_k_1095_ = lean_ctor_get(v_x_1094_, 1);
lean_inc(v_k_1095_);
v_v_1096_ = lean_ctor_get(v_x_1094_, 2);
lean_inc(v_v_1096_);
v_l_1097_ = lean_ctor_get(v_x_1094_, 3);
lean_inc(v_l_1097_);
v_r_1098_ = lean_ctor_get(v_x_1094_, 4);
lean_inc(v_r_1098_);
lean_dec_ref_known(v_x_1094_, 5);
v___x_1099_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_init_1093_, v_r_1098_);
v_kinds_1100_ = lean_ctor_get(v___x_1099_, 0);
v_values_1101_ = lean_ctor_get(v___x_1099_, 1);
v_objectFieldKeys_1102_ = lean_ctor_get(v___x_1099_, 2);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1104_ = v___x_1099_;
v_isShared_1105_ = v_isSharedCheck_1115_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_objectFieldKeys_1102_);
lean_inc(v_values_1101_);
lean_inc(v_kinds_1100_);
lean_dec(v___x_1099_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1115_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1106_ = 3;
v___x_1107_ = lean_box(v___x_1106_);
v___x_1108_ = lean_array_push(v_kinds_1100_, v___x_1107_);
v___x_1109_ = lean_array_push(v_objectFieldKeys_1102_, v_k_1095_);
v___x_1110_ = lean_array_push(v_values_1101_, v_v_1096_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 2, v___x_1109_);
lean_ctor_set(v___x_1104_, 1, v___x_1110_);
lean_ctor_set(v___x_1104_, 0, v___x_1108_);
v___x_1112_ = v___x_1104_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v___x_1109_);
v___x_1112_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
v_init_1093_ = v___x_1112_;
v_x_1094_ = v_l_1097_;
goto _start;
}
}
}
else
{
return v_init_1093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(lean_object* v_acc_1126_, lean_object* v_q_1127_){
_start:
{
lean_object* v_kinds_1128_; lean_object* v_values_1129_; lean_object* v_objectFieldKeys_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1311_; 
v_kinds_1128_ = lean_ctor_get(v_q_1127_, 0);
v_values_1129_ = lean_ctor_get(v_q_1127_, 1);
v_objectFieldKeys_1130_ = lean_ctor_get(v_q_1127_, 2);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_q_1127_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1132_ = v_q_1127_;
v_isShared_1133_ = v_isSharedCheck_1311_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_objectFieldKeys_1130_);
lean_inc(v_values_1129_);
lean_inc(v_kinds_1128_);
lean_dec(v_q_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1311_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = lean_array_get_size(v_kinds_1128_);
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_nat_dec_eq(v___x_1134_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v_kind_1139_; lean_object* v___x_1140_; lean_object* v_q_1142_; 
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_nat_sub(v___x_1134_, v___x_1137_);
v_kind_1139_ = lean_array_fget(v_kinds_1128_, v___x_1138_);
lean_dec(v___x_1138_);
v___x_1140_ = lean_array_pop(v_kinds_1128_);
lean_inc_ref(v_objectFieldKeys_1130_);
lean_inc_ref(v_values_1129_);
lean_inc_ref(v___x_1140_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1140_);
v_q_1142_ = v___x_1132_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_values_1129_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_objectFieldKeys_1130_);
v_q_1142_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_unbox(v_kind_1139_);
lean_dec(v_kind_1139_);
switch(v___x_1143_)
{
case 0:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v_value_1147_; lean_object* v___x_1148_; lean_object* v_q_1149_; lean_object* v___y_1151_; 
lean_dec_ref(v_q_1142_);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_array_get_size(v_values_1129_);
v___x_1146_ = lean_nat_sub(v___x_1145_, v___x_1137_);
v_value_1147_ = lean_array_get(v___x_1144_, v_values_1129_, v___x_1146_);
lean_dec(v___x_1146_);
v___x_1148_ = lean_array_pop(v_values_1129_);
lean_inc_ref(v_objectFieldKeys_1130_);
lean_inc_ref(v___x_1148_);
lean_inc_ref(v___x_1140_);
v_q_1149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1149_, 0, v___x_1140_);
lean_ctor_set(v_q_1149_, 1, v___x_1148_);
lean_ctor_set(v_q_1149_, 2, v_objectFieldKeys_1130_);
switch(lean_obj_tag(v_value_1147_))
{
case 0:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec_ref(v___x_1148_);
lean_dec_ref(v___x_1140_);
lean_dec_ref(v_objectFieldKeys_1130_);
v___x_1154_ = ((lean_object*)(l_Lean_Json_render___closed__0));
v___x_1155_ = lean_string_append(v_acc_1126_, v___x_1154_);
v_acc_1126_ = v___x_1155_;
v_q_1127_ = v_q_1149_;
goto _start;
}
case 1:
{
uint8_t v_b_1157_; 
lean_dec_ref(v___x_1148_);
lean_dec_ref(v___x_1140_);
lean_dec_ref(v_objectFieldKeys_1130_);
v_b_1157_ = lean_ctor_get_uint8(v_value_1147_, 0);
lean_dec_ref_known(v_value_1147_, 0);
if (v_b_1157_ == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = ((lean_object*)(l_Lean_Json_render___closed__2));
v___y_1151_ = v___x_1158_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1159_; 
v___x_1159_ = ((lean_object*)(l_Lean_Json_render___closed__4));
v___y_1151_ = v___x_1159_;
goto v___jp_1150_;
}
}
case 2:
{
lean_object* v_n_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec_ref(v___x_1148_);
lean_dec_ref(v___x_1140_);
lean_dec_ref(v_objectFieldKeys_1130_);
v_n_1160_ = lean_ctor_get(v_value_1147_, 0);
lean_inc_ref(v_n_1160_);
lean_dec_ref_known(v_value_1147_, 1);
v___x_1161_ = l_Lean_JsonNumber_toString(v_n_1160_);
v___x_1162_ = lean_string_append(v_acc_1126_, v___x_1161_);
lean_dec_ref(v___x_1161_);
v_acc_1126_ = v___x_1162_;
v_q_1127_ = v_q_1149_;
goto _start;
}
case 3:
{
lean_object* v_s_1164_; lean_object* v___x_1165_; lean_object* v_acc_1166_; uint8_t v___x_1167_; 
lean_dec_ref(v___x_1148_);
lean_dec_ref(v___x_1140_);
lean_dec_ref(v_objectFieldKeys_1130_);
v_s_1164_ = lean_ctor_get(v_value_1147_, 0);
lean_inc_ref(v_s_1164_);
lean_dec_ref_known(v_value_1147_, 1);
v___x_1165_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1166_ = lean_string_append(v_acc_1126_, v___x_1165_);
v___x_1167_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_1164_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_string_append(v_acc_1166_, v_s_1164_);
lean_dec_ref(v_s_1164_);
v___x_1169_ = lean_string_append(v___x_1168_, v___x_1165_);
v_acc_1126_ = v___x_1169_;
v_q_1127_ = v_q_1149_;
goto _start;
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1171_ = lean_string_utf8_byte_size(v_s_1164_);
v___x_1172_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1171_, v_s_1164_, v___x_1135_, v_acc_1166_);
lean_dec_ref(v_s_1164_);
v___x_1173_ = lean_string_append(v___x_1172_, v___x_1165_);
v_acc_1126_ = v___x_1173_;
v_q_1127_ = v_q_1149_;
goto _start;
}
}
case 4:
{
lean_object* v_elems_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v_q_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
lean_dec_ref_known(v_q_1149_, 3);
v_elems_1175_ = lean_ctor_get(v_value_1147_, 0);
lean_inc_ref(v_elems_1175_);
lean_dec_ref_known(v_value_1147_, 1);
v___x_1176_ = 2;
v___x_1177_ = lean_box(v___x_1176_);
v___x_1178_ = lean_array_push(v___x_1140_, v___x_1177_);
v_q_1179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1179_, 0, v___x_1178_);
lean_ctor_set(v_q_1179_, 1, v___x_1148_);
lean_ctor_set(v_q_1179_, 2, v_objectFieldKeys_1130_);
v___x_1180_ = ((lean_object*)(l_Lean_Json_render___closed__9));
v___x_1181_ = lean_string_append(v_acc_1126_, v___x_1180_);
v___x_1182_ = lean_array_get_size(v_elems_1175_);
v___x_1183_ = lean_nat_dec_lt(v___x_1135_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_dec_ref(v_elems_1175_);
v_acc_1126_ = v___x_1181_;
v_q_1127_ = v_q_1179_;
goto _start;
}
else
{
size_t v___x_1185_; size_t v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_usize_of_nat(v___x_1182_);
v___x_1186_ = ((size_t)0ULL);
v___x_1187_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_elems_1175_, v___x_1185_, v___x_1186_, v_q_1179_);
lean_dec_ref(v_elems_1175_);
v_acc_1126_ = v___x_1181_;
v_q_1127_ = v___x_1187_;
goto _start;
}
}
default: 
{
lean_object* v_kvPairs_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v_q_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref_known(v_q_1149_, 3);
v_kvPairs_1189_ = lean_ctor_get(v_value_1147_, 0);
lean_inc(v_kvPairs_1189_);
lean_dec_ref_known(v_value_1147_, 1);
v___x_1190_ = 4;
v___x_1191_ = lean_box(v___x_1190_);
v___x_1192_ = lean_array_push(v___x_1140_, v___x_1191_);
v_q_1193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1193_, 0, v___x_1192_);
lean_ctor_set(v_q_1193_, 1, v___x_1148_);
lean_ctor_set(v_q_1193_, 2, v_objectFieldKeys_1130_);
v___x_1194_ = ((lean_object*)(l_Lean_Json_render___closed__15));
v___x_1195_ = lean_string_append(v_acc_1126_, v___x_1194_);
v___x_1196_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_q_1193_, v_kvPairs_1189_);
v_acc_1126_ = v___x_1195_;
v_q_1127_ = v___x_1196_;
goto _start;
}
}
v___jp_1150_:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_string_append(v_acc_1126_, v___y_1151_);
v_acc_1126_ = v___x_1152_;
v_q_1127_ = v_q_1149_;
goto _start;
}
}
case 1:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v_value_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
lean_dec_ref(v_q_1142_);
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_array_get_size(v_values_1129_);
v___x_1200_ = lean_nat_sub(v___x_1199_, v___x_1137_);
v_value_1201_ = lean_array_get(v___x_1198_, v_values_1129_, v___x_1200_);
lean_dec(v___x_1200_);
v___x_1202_ = lean_array_get_size(v___x_1140_);
v___x_1203_ = lean_nat_dec_eq(v___x_1202_, v___x_1135_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_kind_1206_; uint8_t v___x_1207_; 
v___x_1204_ = lean_array_pop(v_values_1129_);
v___x_1205_ = lean_nat_sub(v___x_1202_, v___x_1137_);
v_kind_1206_ = lean_array_fget_borrowed(v___x_1140_, v___x_1205_);
lean_dec(v___x_1205_);
v___x_1207_ = lean_unbox(v_kind_1206_);
if (v___x_1207_ == 2)
{
uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1208_ = 0;
v___x_1209_ = lean_box(v___x_1208_);
v___x_1210_ = lean_array_push(v___x_1140_, v___x_1209_);
v___x_1211_ = lean_array_push(v___x_1204_, v_value_1201_);
v___x_1212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
lean_ctor_set(v___x_1212_, 2, v_objectFieldKeys_1130_);
v_q_1127_ = v___x_1212_;
goto _start;
}
else
{
uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1214_ = 5;
v___x_1215_ = lean_box(v___x_1214_);
v___x_1216_ = lean_array_push(v___x_1140_, v___x_1215_);
v___x_1217_ = 0;
v___x_1218_ = lean_box(v___x_1217_);
v___x_1219_ = lean_array_push(v___x_1216_, v___x_1218_);
v___x_1220_ = lean_array_push(v___x_1204_, v_value_1201_);
v___x_1221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
lean_ctor_set(v___x_1221_, 2, v_objectFieldKeys_1130_);
v_q_1127_ = v___x_1221_;
goto _start;
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v___x_1140_);
lean_dec_ref(v_objectFieldKeys_1130_);
lean_dec_ref(v_values_1129_);
v___x_1223_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0));
v___x_1224_ = lean_mk_empty_array_with_capacity(v___x_1137_);
v___x_1225_ = lean_array_push(v___x_1224_, v_value_1201_);
v___x_1226_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1223_);
lean_ctor_set(v___x_1227_, 1, v___x_1225_);
lean_ctor_set(v___x_1227_, 2, v___x_1226_);
v_q_1127_ = v___x_1227_;
goto _start;
}
}
case 2:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec_ref(v___x_1140_);
lean_dec_ref(v_objectFieldKeys_1130_);
lean_dec_ref(v_values_1129_);
v___x_1229_ = ((lean_object*)(l_Lean_Json_render___closed__10));
v___x_1230_ = lean_string_append(v_acc_1126_, v___x_1229_);
v_acc_1126_ = v___x_1230_;
v_q_1127_ = v_q_1142_;
goto _start;
}
case 3:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v_objectFieldKey_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_value_1239_; lean_object* v___y_1241_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
lean_dec_ref(v_q_1142_);
v___x_1232_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1233_ = lean_array_get_size(v_objectFieldKeys_1130_);
v___x_1234_ = lean_nat_sub(v___x_1233_, v___x_1137_);
v_objectFieldKey_1235_ = lean_array_get(v___x_1232_, v_objectFieldKeys_1130_, v___x_1234_);
lean_dec(v___x_1234_);
v___x_1236_ = lean_box(0);
v___x_1237_ = lean_array_get_size(v_values_1129_);
v___x_1238_ = lean_nat_sub(v___x_1237_, v___x_1137_);
v_value_1239_ = lean_array_get(v___x_1236_, v_values_1129_, v___x_1238_);
lean_dec(v___x_1238_);
v___x_1250_ = lean_array_get_size(v___x_1140_);
v___x_1251_ = lean_nat_dec_eq(v___x_1250_, v___x_1135_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___y_1255_; lean_object* v___y_1268_; lean_object* v___x_1277_; lean_object* v_kind_1278_; uint8_t v___x_1279_; 
v___x_1252_ = lean_array_pop(v_objectFieldKeys_1130_);
v___x_1253_ = lean_array_pop(v_values_1129_);
v___x_1277_ = lean_nat_sub(v___x_1250_, v___x_1137_);
v_kind_1278_ = lean_array_fget_borrowed(v___x_1140_, v___x_1277_);
lean_dec(v___x_1277_);
v___x_1279_ = lean_unbox(v_kind_1278_);
if (v___x_1279_ == 4)
{
lean_object* v___x_1280_; lean_object* v_acc_1281_; uint8_t v___x_1282_; 
v___x_1280_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1281_ = lean_string_append(v_acc_1126_, v___x_1280_);
v___x_1282_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1235_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_string_append(v_acc_1281_, v_objectFieldKey_1235_);
lean_dec(v_objectFieldKey_1235_);
v___x_1284_ = lean_string_append(v___x_1283_, v___x_1280_);
v___y_1268_ = v___x_1284_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_string_utf8_byte_size(v_objectFieldKey_1235_);
v___x_1286_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1285_, v_objectFieldKey_1235_, v___x_1135_, v_acc_1281_);
lean_dec(v_objectFieldKey_1235_);
v___x_1287_ = lean_string_append(v___x_1286_, v___x_1280_);
v___y_1268_ = v___x_1287_;
goto v___jp_1267_;
}
}
else
{
lean_object* v___x_1288_; lean_object* v_acc_1289_; uint8_t v___x_1290_; 
v___x_1288_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1289_ = lean_string_append(v_acc_1126_, v___x_1288_);
v___x_1290_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1235_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_string_append(v_acc_1289_, v_objectFieldKey_1235_);
lean_dec(v_objectFieldKey_1235_);
v___x_1292_ = lean_string_append(v___x_1291_, v___x_1288_);
v___y_1255_ = v___x_1292_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = lean_string_utf8_byte_size(v_objectFieldKey_1235_);
v___x_1294_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1293_, v_objectFieldKey_1235_, v___x_1135_, v_acc_1289_);
lean_dec(v_objectFieldKey_1235_);
v___x_1295_ = lean_string_append(v___x_1294_, v___x_1288_);
v___y_1255_ = v___x_1295_;
goto v___jp_1254_;
}
}
v___jp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1256_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1257_ = lean_string_append(v___y_1255_, v___x_1256_);
v___x_1258_ = 5;
v___x_1259_ = lean_box(v___x_1258_);
v___x_1260_ = lean_array_push(v___x_1140_, v___x_1259_);
v___x_1261_ = 0;
v___x_1262_ = lean_box(v___x_1261_);
v___x_1263_ = lean_array_push(v___x_1260_, v___x_1262_);
v___x_1264_ = lean_array_push(v___x_1253_, v_value_1239_);
v___x_1265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
lean_ctor_set(v___x_1265_, 2, v___x_1252_);
v_acc_1126_ = v___x_1257_;
v_q_1127_ = v___x_1265_;
goto _start;
}
v___jp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1269_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1270_ = lean_string_append(v___y_1268_, v___x_1269_);
v___x_1271_ = 0;
v___x_1272_ = lean_box(v___x_1271_);
v___x_1273_ = lean_array_push(v___x_1140_, v___x_1272_);
v___x_1274_ = lean_array_push(v___x_1253_, v_value_1239_);
v___x_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
lean_ctor_set(v___x_1275_, 2, v___x_1252_);
v_acc_1126_ = v___x_1270_;
v_q_1127_ = v___x_1275_;
goto _start;
}
}
else
{
lean_object* v___x_1296_; lean_object* v_acc_1297_; uint8_t v___x_1298_; 
lean_dec_ref(v___x_1140_);
lean_dec_ref(v_objectFieldKeys_1130_);
lean_dec_ref(v_values_1129_);
v___x_1296_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1297_ = lean_string_append(v_acc_1126_, v___x_1296_);
v___x_1298_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1235_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_string_append(v_acc_1297_, v_objectFieldKey_1235_);
lean_dec(v_objectFieldKey_1235_);
v___x_1300_ = lean_string_append(v___x_1299_, v___x_1296_);
v___y_1241_ = v___x_1300_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_string_utf8_byte_size(v_objectFieldKey_1235_);
v___x_1302_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1301_, v_objectFieldKey_1235_, v___x_1135_, v_acc_1297_);
lean_dec(v_objectFieldKey_1235_);
v___x_1303_ = lean_string_append(v___x_1302_, v___x_1296_);
v___y_1241_ = v___x_1303_;
goto v___jp_1240_;
}
}
v___jp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1242_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1243_ = lean_string_append(v___y_1241_, v___x_1242_);
v___x_1244_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0));
v___x_1245_ = lean_mk_empty_array_with_capacity(v___x_1137_);
v___x_1246_ = lean_array_push(v___x_1245_, v_value_1239_);
v___x_1247_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1244_);
lean_ctor_set(v___x_1248_, 1, v___x_1246_);
lean_ctor_set(v___x_1248_, 2, v___x_1247_);
v_acc_1126_ = v___x_1243_;
v_q_1127_ = v___x_1248_;
goto _start;
}
}
case 4:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v___x_1140_);
lean_dec_ref(v_objectFieldKeys_1130_);
lean_dec_ref(v_values_1129_);
v___x_1304_ = ((lean_object*)(l_Lean_Json_render___closed__16));
v___x_1305_ = lean_string_append(v_acc_1126_, v___x_1304_);
v_acc_1126_ = v___x_1305_;
v_q_1127_ = v_q_1142_;
goto _start;
}
default: 
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec_ref(v___x_1140_);
lean_dec_ref(v_objectFieldKeys_1130_);
lean_dec_ref(v_values_1129_);
v___x_1307_ = ((lean_object*)(l_Lean_Json_render___closed__6));
v___x_1308_ = lean_string_append(v_acc_1126_, v___x_1307_);
v_acc_1126_ = v___x_1308_;
v_q_1127_ = v_q_1142_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_1132_);
lean_dec_ref(v_objectFieldKeys_1130_);
lean_dec_ref(v_values_1129_);
lean_dec_ref(v_kinds_1128_);
return v_acc_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_compress(lean_object* v_j_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1318_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = lean_mk_empty_array_with_capacity(v___x_1319_);
v___x_1321_ = ((lean_object*)(l_Lean_Json_compress___closed__0));
v___x_1322_ = lean_array_push(v___x_1320_, v_j_1317_);
v___x_1323_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1321_);
lean_ctor_set(v___x_1324_, 1, v___x_1322_);
lean_ctor_set(v___x_1324_, 2, v___x_1323_);
v___x_1325_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(v___x_1318_, v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instToString___lam__0(lean_object* v_j_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_unsigned_to_nat(80u);
v___x_1330_ = l_Lean_Json_pretty(v_j_1328_, v___x_1329_);
return v___x_1330_;
}
}
lean_object* runtime_initialize_Lean_Data_Format(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_Printer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Json_Printer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Format(uint8_t builtin);
lean_object* initialize_Lean_Data_Json_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Printer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Json_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Json_Printer(builtin);
}
#ifdef __cplusplus
}
#endif
