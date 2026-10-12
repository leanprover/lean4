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
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(lean_object* v_acc_524_, uint32_t v_c_525_){
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
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_524_ = stack[0].m_obj;
uint32_t v_c_525_ = stack[1].m_num;
lean_object* v_res_571_;
v_res_571_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_524_, v_c_525_);
stack->m_obj
 = v_res_571_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___boxed(lean_object* v_acc_572_, lean_object* v_c_573_){
_start:
{
uint32_t v_c_boxed_574_; lean_object* v_res_575_; 
v_c_boxed_574_ = lean_unbox_uint32(v_c_573_);
lean_dec(v_c_573_);
v_res_575_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_572_, v_c_boxed_574_);
return v_res_575_;
}
}
uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(lean_object* v_s_576_, lean_object* v_i_577_){
_start:
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_string_utf8_byte_size(v_s_576_);
v___x_579_ = lean_nat_dec_lt(v_i_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_dec(v_i_577_);
return v___x_579_;
}
else
{
uint8_t v_byte_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; uint8_t v___x_584_; uint8_t v___x_585_; 
lean_inc(v_i_577_);
v_byte_580_ = lean_string_get_byte_fast(v_s_576_, v_i_577_);
v___x_581_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable));
v___x_582_ = lean_uint8_to_nat(v_byte_580_);
v___x_583_ = lean_byte_array_fget(v___x_581_, v___x_582_);
v___x_584_ = 0;
v___x_585_ = lean_uint8_dec_eq(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_dec(v_i_577_);
return v___x_579_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_add(v_i_577_, v___x_586_);
lean_dec(v_i_577_);
v_i_577_ = v___x_587_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_576_ = stack[0].m_obj;
lean_object* v_i_577_ = stack[1].m_obj;
uint8_t v_res_589_;
v_res_589_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(v_s_576_, v_i_577_);
stack->m_num = v_res_589_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go___boxed(lean_object* v_s_590_, lean_object* v_i_591_){
_start:
{
uint8_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(v_s_590_, v_i_591_);
lean_dec_ref(v_s_590_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(lean_object* v_s_594_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(v_s_594_, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_594_ = stack[0].m_obj;
uint8_t v_res_597_;
v_res_597_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_594_);
stack->m_num = v_res_597_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape___boxed(lean_object* v_s_598_){
_start:
{
uint8_t v_res_599_; lean_object* v_r_600_; 
v_res_599_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_598_);
lean_dec_ref(v_s_598_);
v_r_600_ = lean_box(v_res_599_);
return v_r_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape___lam__0(lean_object* v___x_601_, lean_object* v_s_602_, lean_object* v_it_603_, lean_object* v_acc_604_, lean_object* v_hP_605_, lean_object* v_recur_606_){
_start:
{
uint8_t v_decide_607_; 
v_decide_607_ = lean_nat_dec_eq(v_it_603_, v___x_601_);
if (v_decide_607_ == 0)
{
uint32_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_608_ = lean_string_utf8_get_fast(v_s_602_, v_it_603_);
v___x_609_ = lean_string_utf8_next_fast(v_s_602_, v_it_603_);
v___x_610_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_604_, v___x_608_);
v___x_611_ = lean_apply_4(v_recur_606_, v___x_609_, v___x_610_, lean_box(0), lean_box(0));
return v___x_611_;
}
else
{
lean_dec_ref(v_recur_606_);
return v_acc_604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape___lam__0___boxed(lean_object* v___x_612_, lean_object* v_s_613_, lean_object* v_it_614_, lean_object* v_acc_615_, lean_object* v_hP_616_, lean_object* v_recur_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Json_escape___lam__0(v___x_612_, v_s_613_, v_it_614_, v_acc_615_, v_hP_616_, v_recur_617_);
lean_dec(v_it_614_);
lean_dec_ref(v_s_613_);
lean_dec(v___x_612_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object* v_s_619_, lean_object* v_acc_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_619_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
v___x_622_ = lean_string_append(v_acc_620_, v_s_619_);
lean_dec_ref(v_s_619_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___f_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_string_utf8_byte_size(v_s_619_);
v___f_624_ = lean_alloc_closure((void*)(l_Lean_Json_escape___lam__0___boxed), 6, 2);
lean_closure_set(v___f_624_, 0, v___x_623_);
lean_closure_set(v___f_624_, 1, v_s_619_);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_624_, v___x_625_, v_acc_620_, lean_box(0));
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object* v_s_628_, lean_object* v_acc_629_){
_start:
{
lean_object* v___x_630_; lean_object* v_acc_631_; uint8_t v___x_632_; 
v___x_630_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_631_ = lean_string_append(v_acc_629_, v___x_630_);
v___x_632_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_628_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_string_append(v_acc_631_, v_s_628_);
lean_dec_ref(v_s_628_);
v___x_634_ = lean_string_append(v___x_633_, v___x_630_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_635_ = lean_string_utf8_byte_size(v_s_628_);
v___f_636_ = lean_alloc_closure((void*)(l_Lean_Json_escape___lam__0___boxed), 6, 2);
lean_closure_set(v___f_636_, 0, v___x_635_);
lean_closure_set(v___f_636_, 1, v_s_628_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_636_, v___x_637_, v_acc_631_, lean_box(0));
v___x_639_ = lean_string_append(v___x_638_, v___x_630_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_render_spec__3(lean_object* v_a_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_nat_to_int(v_a_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(lean_object* v___x_642_, lean_object* v_k_643_, lean_object* v_a_644_, lean_object* v_b_645_){
_start:
{
uint8_t v_decide_646_; 
v_decide_646_ = lean_nat_dec_eq(v_a_644_, v___x_642_);
if (v_decide_646_ == 0)
{
uint32_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_string_utf8_get_fast(v_k_643_, v_a_644_);
v___x_648_ = lean_string_utf8_next_fast(v_k_643_, v_a_644_);
lean_dec(v_a_644_);
v___x_649_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_b_645_, v___x_647_);
v_a_644_ = v___x_648_;
v_b_645_ = v___x_649_;
goto _start;
}
else
{
lean_dec(v_a_644_);
return v_b_645_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg___boxed(lean_object* v___x_651_, lean_object* v_k_652_, lean_object* v_a_653_, lean_object* v_b_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_651_, v_k_652_, v_a_653_, v_b_654_);
lean_dec_ref(v_k_652_);
lean_dec(v___x_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Json_render_spec__2_spec__2(lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_dec(v_x_656_);
return v_x_657_;
}
else
{
lean_object* v_head_659_; lean_object* v_tail_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_669_; 
v_head_659_ = lean_ctor_get(v_x_658_, 0);
v_tail_660_ = lean_ctor_get(v_x_658_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_669_ == 0)
{
v___x_662_ = v_x_658_;
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_tail_660_);
lean_inc(v_head_659_);
lean_dec(v_x_658_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
lean_inc(v_x_656_);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 5);
lean_ctor_set(v___x_662_, 1, v_x_656_);
lean_ctor_set(v___x_662_, 0, v_x_657_);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_x_657_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_x_656_);
v___x_665_ = v_reuseFailAlloc_668_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v_head_659_);
v_x_657_ = v___x_666_;
v_x_658_ = v_tail_660_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
lean_object* v___x_672_; 
lean_dec(v_x_671_);
v___x_672_ = lean_box(0);
return v___x_672_;
}
else
{
lean_object* v_tail_673_; 
v_tail_673_ = lean_ctor_get(v_x_670_, 1);
if (lean_obj_tag(v_tail_673_) == 0)
{
lean_object* v_head_674_; 
lean_dec(v_x_671_);
v_head_674_ = lean_ctor_get(v_x_670_, 0);
lean_inc(v_head_674_);
lean_dec_ref_known(v_x_670_, 2);
return v_head_674_;
}
else
{
lean_object* v_head_675_; lean_object* v___x_676_; 
lean_inc(v_tail_673_);
v_head_675_ = lean_ctor_get(v_x_670_, 0);
lean_inc(v_head_675_);
lean_dec_ref_known(v_x_670_, 2);
v___x_676_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Json_render_spec__2_spec__2(v_x_671_, v_head_675_, v_tail_673_);
return v___x_676_;
}
}
}
}
static lean_object* _init_l_Lean_Json_render___closed__11(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_Json_render___closed__9));
v___x_694_ = lean_string_length(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_Json_render___closed__12(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_obj_once(&l_Lean_Json_render___closed__11, &l_Lean_Json_render___closed__11_once, _init_l_Lean_Json_render___closed__11);
v___x_696_ = lean_nat_to_int(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(lean_object* v_init_705_, lean_object* v_x_706_){
_start:
{
if (lean_obj_tag(v_x_706_) == 0)
{
lean_object* v_k_707_; lean_object* v_v_708_; lean_object* v_l_709_; lean_object* v_r_710_; lean_object* v___x_711_; lean_object* v___y_713_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_k_707_ = lean_ctor_get(v_x_706_, 1);
lean_inc(v_k_707_);
v_v_708_ = lean_ctor_get(v_x_706_, 2);
lean_inc(v_v_708_);
v_l_709_ = lean_ctor_get(v_x_706_, 3);
lean_inc(v_l_709_);
v_r_710_ = lean_ctor_get(v_x_706_, 4);
lean_inc(v_r_710_);
lean_dec_ref_known(v_x_706_, 5);
v___x_711_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v_init_705_, v_l_709_);
v___x_725_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v___x_726_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_k_707_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_string_append(v___x_725_, v_k_707_);
lean_dec(v_k_707_);
v___x_728_ = lean_string_append(v___x_727_, v___x_725_);
v___y_713_ = v___x_728_;
goto v___jp_712_;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_729_ = lean_string_utf8_byte_size(v_k_707_);
v___x_730_ = lean_unsigned_to_nat(0u);
v___x_731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_729_, v_k_707_, v___x_730_, v___x_725_);
lean_dec(v_k_707_);
v___x_732_ = lean_string_append(v___x_731_, v___x_725_);
v___y_713_ = v___x_732_;
goto v___jp_712_;
}
v___jp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_714_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_714_, 0, v___y_713_);
v___x_715_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__1));
v___x_716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_box(1);
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l_Lean_Json_render(v_v_708_);
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = 0;
v___x_722_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*1, v___x_721_);
v___x_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___x_711_);
v_init_705_ = v___x_723_;
v_x_706_ = v_r_710_;
goto _start;
}
}
else
{
return v_init_705_;
}
}
}
static lean_object* _init_l_Lean_Json_render___closed__17(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = ((lean_object*)(l_Lean_Json_render___closed__15));
v___x_735_ = lean_string_length(v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Json_render___closed__18(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_obj_once(&l_Lean_Json_render___closed__17, &l_Lean_Json_render___closed__17_once, _init_l_Lean_Json_render___closed__17);
v___x_737_ = lean_nat_to_int(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_render(lean_object* v_x_743_){
_start:
{
switch(lean_obj_tag(v_x_743_))
{
case 0:
{
lean_object* v___x_744_; 
v___x_744_ = ((lean_object*)(l_Lean_Json_render___closed__1));
return v___x_744_;
}
case 1:
{
uint8_t v_b_745_; 
v_b_745_ = lean_ctor_get_uint8(v_x_743_, 0);
lean_dec_ref_known(v_x_743_, 0);
if (v_b_745_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = ((lean_object*)(l_Lean_Json_render___closed__3));
return v___x_746_;
}
else
{
lean_object* v___x_747_; 
v___x_747_ = ((lean_object*)(l_Lean_Json_render___closed__5));
return v___x_747_;
}
}
case 2:
{
lean_object* v_n_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
v_n_748_ = lean_ctor_get(v_x_743_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_x_743_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v_x_743_;
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_n_748_);
lean_dec(v_x_743_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_752_ = l_Lean_JsonNumber_toString(v_n_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 3);
lean_ctor_set(v___x_750_, 0, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
case 3:
{
lean_object* v_s_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_775_; 
v_s_757_ = lean_ctor_get(v_x_743_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_x_743_);
if (v_isSharedCheck_775_ == 0)
{
v___x_759_ = v_x_743_;
v_isShared_760_ = v_isSharedCheck_775_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_s_757_);
lean_dec(v_x_743_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_775_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v___x_762_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_757_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_763_ = lean_string_append(v___x_761_, v_s_757_);
lean_dec_ref(v_s_757_);
v___x_764_ = lean_string_append(v___x_763_, v___x_761_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_764_);
v___x_766_ = v___x_759_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_768_ = lean_string_utf8_byte_size(v_s_757_);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_768_, v_s_757_, v___x_769_, v___x_761_);
lean_dec_ref(v_s_757_);
v___x_771_ = lean_string_append(v___x_770_, v___x_761_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_771_);
v___x_773_ = v___x_759_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
case 4:
{
lean_object* v_elems_776_; size_t v_sz_777_; size_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v_elems_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; lean_object* v___x_790_; 
v_elems_776_ = lean_ctor_get(v_x_743_, 0);
lean_inc_ref(v_elems_776_);
lean_dec_ref_known(v_x_743_, 1);
v_sz_777_ = lean_array_size(v_elems_776_);
v___x_778_ = ((size_t)0ULL);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(v_sz_777_, v___x_778_, v_elems_776_);
v___x_780_ = lean_array_to_list(v___x_779_);
v___x_781_ = ((lean_object*)(l_Lean_Json_render___closed__8));
v_elems_782_ = l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(v___x_780_, v___x_781_);
v___x_783_ = lean_obj_once(&l_Lean_Json_render___closed__12, &l_Lean_Json_render___closed__12_once, _init_l_Lean_Json_render___closed__12);
v___x_784_ = ((lean_object*)(l_Lean_Json_render___closed__13));
v___x_785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v_elems_782_);
v___x_786_ = ((lean_object*)(l_Lean_Json_render___closed__14));
v___x_787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_783_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = 0;
v___x_790_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*1, v___x_789_);
return v___x_790_;
}
default: 
{
lean_object* v_kvPairs_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_kvs_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; 
v_kvPairs_791_ = lean_ctor_get(v_x_743_, 0);
lean_inc(v_kvPairs_791_);
lean_dec_ref_known(v_x_743_, 1);
v___x_792_ = lean_box(0);
v___x_793_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v___x_792_, v_kvPairs_791_);
v___x_794_ = ((lean_object*)(l_Lean_Json_render___closed__8));
v_kvs_795_ = l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(v___x_793_, v___x_794_);
v___x_796_ = lean_obj_once(&l_Lean_Json_render___closed__18, &l_Lean_Json_render___closed__18_once, _init_l_Lean_Json_render___closed__18);
v___x_797_ = ((lean_object*)(l_Lean_Json_render___closed__19));
v___x_798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v_kvs_795_);
v___x_799_ = ((lean_object*)(l_Lean_Json_render___closed__20));
v___x_800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_796_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = 0;
v___x_803_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*1, v___x_802_);
return v___x_803_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(size_t v_sz_804_, size_t v_i_805_, lean_object* v_bs_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = lean_usize_dec_lt(v_i_805_, v_sz_804_);
if (v___x_807_ == 0)
{
return v_bs_806_;
}
else
{
lean_object* v_v_808_; lean_object* v___x_809_; lean_object* v_bs_x27_810_; lean_object* v___x_811_; size_t v___x_812_; size_t v___x_813_; lean_object* v___x_814_; 
v_v_808_ = lean_array_uget(v_bs_806_, v_i_805_);
v___x_809_ = lean_unsigned_to_nat(0u);
v_bs_x27_810_ = lean_array_uset(v_bs_806_, v_i_805_, v___x_809_);
v___x_811_ = l_Lean_Json_render(v_v_808_);
v___x_812_ = ((size_t)1ULL);
v___x_813_ = lean_usize_add(v_i_805_, v___x_812_);
v___x_814_ = lean_array_uset(v_bs_x27_810_, v_i_805_, v___x_811_);
v_i_805_ = v___x_813_;
v_bs_806_ = v___x_814_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_804_ = stack[0].m_num;
size_t v_i_805_ = stack[1].m_num;
lean_object* v_bs_806_ = stack[2].m_obj;
lean_object* v_res_816_;
v_res_816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(v_sz_804_, v_i_805_, v_bs_806_);
stack->m_obj
 = v_res_816_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1___boxed(lean_object* v_sz_817_, lean_object* v_i_818_, lean_object* v_bs_819_){
_start:
{
size_t v_sz_boxed_820_; size_t v_i_boxed_821_; lean_object* v_res_822_; 
v_sz_boxed_820_ = lean_unbox_usize(v_sz_817_);
lean_dec(v_sz_817_);
v_i_boxed_821_ = lean_unbox_usize(v_i_818_);
lean_dec(v_i_818_);
v_res_822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(v_sz_boxed_820_, v_i_boxed_821_, v_bs_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(lean_object* v___x_823_, lean_object* v___x_824_, lean_object* v_k_825_, lean_object* v_inst_826_, lean_object* v_R_827_, lean_object* v_a_828_, lean_object* v_b_829_, lean_object* v_c_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_824_, v_k_825_, v_a_828_, v_b_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___boxed(lean_object* v___x_832_, lean_object* v___x_833_, lean_object* v_k_834_, lean_object* v_inst_835_, lean_object* v_R_836_, lean_object* v_a_837_, lean_object* v_b_838_, lean_object* v_c_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(v___x_832_, v___x_833_, v_k_834_, v_inst_835_, v_R_836_, v_a_837_, v_b_838_, v_c_839_);
lean_dec_ref(v_k_834_);
lean_dec(v___x_833_);
lean_dec_ref(v___x_832_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4(lean_object* v_init_841_, lean_object* v_t_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v_init_841_, v_t_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_pretty(lean_object* v_j_844_, lean_object* v_lineWidth_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = l_Lean_Json_render(v_j_844_);
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = l_Std_Format_pretty(v___x_846_, v_lineWidth_845_, v___x_847_, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_pretty___boxed(lean_object* v_j_849_, lean_object* v_lineWidth_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Json_pretty(v_j_849_, v_lineWidth_850_);
lean_dec(v_lineWidth_850_);
return v_res_851_;
}
}
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___impl(uint8_t v_x_852_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_box(v_x_852_);
v___x_854_ = lean_obj_tag_nat(v___x_853_);
lean_dec(v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_852_ = stack[0].m_num;
lean_object* v_res_855_;
v_res_855_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___impl(v_x_852_);
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___impl___boxed(lean_object* v_x_856_){
_start:
{
uint8_t v_x_4__boxed_857_; lean_object* v_res_858_; 
v_x_4__boxed_857_ = lean_unbox(v_x_856_);
v_res_858_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___impl(v_x_4__boxed_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg(lean_object* v_k_859_){
_start:
{
lean_inc(v_k_859_);
return v_k_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg___boxed(lean_object* v_k_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg(v_k_860_);
lean_dec(v_k_860_);
return v_res_861_;
}
}
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(lean_object* v_motive_862_, lean_object* v_ctorIdx_863_, uint8_t v_t_864_, lean_object* v_h_865_, lean_object* v_k_866_){
_start:
{
lean_inc(v_k_866_);
return v_k_866_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_863_ = stack[1].m_obj;
uint8_t v_t_864_ = stack[2].m_num;
lean_object* v_k_866_ = stack[4].m_obj;
lean_object* v_res_867_;
v_res_867_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(lean_box(0), v_ctorIdx_863_, v_t_864_, lean_box(0), v_k_866_);
stack->m_obj
 = v_res_867_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___boxed(lean_object* v_motive_868_, lean_object* v_ctorIdx_869_, lean_object* v_t_870_, lean_object* v_h_871_, lean_object* v_k_872_){
_start:
{
uint8_t v_t_boxed_873_; lean_object* v_res_874_; 
v_t_boxed_873_ = lean_unbox(v_t_870_);
v_res_874_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(v_motive_868_, v_ctorIdx_869_, v_t_boxed_873_, v_h_871_, v_k_872_);
lean_dec(v_k_872_);
lean_dec(v_ctorIdx_869_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(lean_object* v_json_875_){
_start:
{
lean_inc(v_json_875_);
return v_json_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg___boxed(lean_object* v_json_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(v_json_876_);
lean_dec(v_json_876_);
return v_res_877_;
}
}
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(lean_object* v_motive_878_, uint8_t v_t_879_, lean_object* v_h_880_, lean_object* v_json_881_){
_start:
{
lean_inc(v_json_881_);
return v_json_881_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_879_ = stack[1].m_num;
lean_object* v_json_881_ = stack[3].m_obj;
lean_object* v_res_882_;
v_res_882_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(lean_box(0), v_t_879_, lean_box(0), v_json_881_);
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___boxed(lean_object* v_motive_883_, lean_object* v_t_884_, lean_object* v_h_885_, lean_object* v_json_886_){
_start:
{
uint8_t v_t_boxed_887_; lean_object* v_res_888_; 
v_t_boxed_887_ = lean_unbox(v_t_884_);
v_res_888_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(v_motive_883_, v_t_boxed_887_, v_h_885_, v_json_886_);
lean_dec(v_json_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(lean_object* v_arrayElem_889_){
_start:
{
lean_inc(v_arrayElem_889_);
return v_arrayElem_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg___boxed(lean_object* v_arrayElem_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(v_arrayElem_890_);
lean_dec(v_arrayElem_890_);
return v_res_891_;
}
}
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(lean_object* v_motive_892_, uint8_t v_t_893_, lean_object* v_h_894_, lean_object* v_arrayElem_895_){
_start:
{
lean_inc(v_arrayElem_895_);
return v_arrayElem_895_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_893_ = stack[1].m_num;
lean_object* v_arrayElem_895_ = stack[3].m_obj;
lean_object* v_res_896_;
v_res_896_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(lean_box(0), v_t_893_, lean_box(0), v_arrayElem_895_);
stack->m_obj
 = v_res_896_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___boxed(lean_object* v_motive_897_, lean_object* v_t_898_, lean_object* v_h_899_, lean_object* v_arrayElem_900_){
_start:
{
uint8_t v_t_boxed_901_; lean_object* v_res_902_; 
v_t_boxed_901_ = lean_unbox(v_t_898_);
v_res_902_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(v_motive_897_, v_t_boxed_901_, v_h_899_, v_arrayElem_900_);
lean_dec(v_arrayElem_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(lean_object* v_arrayEnd_903_){
_start:
{
lean_inc(v_arrayEnd_903_);
return v_arrayEnd_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg___boxed(lean_object* v_arrayEnd_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(v_arrayEnd_904_);
lean_dec(v_arrayEnd_904_);
return v_res_905_;
}
}
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(lean_object* v_motive_906_, uint8_t v_t_907_, lean_object* v_h_908_, lean_object* v_arrayEnd_909_){
_start:
{
lean_inc(v_arrayEnd_909_);
return v_arrayEnd_909_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_907_ = stack[1].m_num;
lean_object* v_arrayEnd_909_ = stack[3].m_obj;
lean_object* v_res_910_;
v_res_910_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(lean_box(0), v_t_907_, lean_box(0), v_arrayEnd_909_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___boxed(lean_object* v_motive_911_, lean_object* v_t_912_, lean_object* v_h_913_, lean_object* v_arrayEnd_914_){
_start:
{
uint8_t v_t_boxed_915_; lean_object* v_res_916_; 
v_t_boxed_915_ = lean_unbox(v_t_912_);
v_res_916_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(v_motive_911_, v_t_boxed_915_, v_h_913_, v_arrayEnd_914_);
lean_dec(v_arrayEnd_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(lean_object* v_objectField_917_){
_start:
{
lean_inc(v_objectField_917_);
return v_objectField_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg___boxed(lean_object* v_objectField_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(v_objectField_918_);
lean_dec(v_objectField_918_);
return v_res_919_;
}
}
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(lean_object* v_motive_920_, uint8_t v_t_921_, lean_object* v_h_922_, lean_object* v_objectField_923_){
_start:
{
lean_inc(v_objectField_923_);
return v_objectField_923_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_921_ = stack[1].m_num;
lean_object* v_objectField_923_ = stack[3].m_obj;
lean_object* v_res_924_;
v_res_924_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(lean_box(0), v_t_921_, lean_box(0), v_objectField_923_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___boxed(lean_object* v_motive_925_, lean_object* v_t_926_, lean_object* v_h_927_, lean_object* v_objectField_928_){
_start:
{
uint8_t v_t_boxed_929_; lean_object* v_res_930_; 
v_t_boxed_929_ = lean_unbox(v_t_926_);
v_res_930_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(v_motive_925_, v_t_boxed_929_, v_h_927_, v_objectField_928_);
lean_dec(v_objectField_928_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(lean_object* v_objectEnd_931_){
_start:
{
lean_inc(v_objectEnd_931_);
return v_objectEnd_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg___boxed(lean_object* v_objectEnd_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(v_objectEnd_932_);
lean_dec(v_objectEnd_932_);
return v_res_933_;
}
}
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(lean_object* v_motive_934_, uint8_t v_t_935_, lean_object* v_h_936_, lean_object* v_objectEnd_937_){
_start:
{
lean_inc(v_objectEnd_937_);
return v_objectEnd_937_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_935_ = stack[1].m_num;
lean_object* v_objectEnd_937_ = stack[3].m_obj;
lean_object* v_res_938_;
v_res_938_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(lean_box(0), v_t_935_, lean_box(0), v_objectEnd_937_);
stack->m_obj
 = v_res_938_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___boxed(lean_object* v_motive_939_, lean_object* v_t_940_, lean_object* v_h_941_, lean_object* v_objectEnd_942_){
_start:
{
uint8_t v_t_boxed_943_; lean_object* v_res_944_; 
v_t_boxed_943_ = lean_unbox(v_t_940_);
v_res_944_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(v_motive_939_, v_t_boxed_943_, v_h_941_, v_objectEnd_942_);
lean_dec(v_objectEnd_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(lean_object* v_comma_945_){
_start:
{
lean_inc(v_comma_945_);
return v_comma_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg___boxed(lean_object* v_comma_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(v_comma_946_);
lean_dec(v_comma_946_);
return v_res_947_;
}
}
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(lean_object* v_motive_948_, uint8_t v_t_949_, lean_object* v_h_950_, lean_object* v_comma_951_){
_start:
{
lean_inc(v_comma_951_);
return v_comma_951_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_949_ = stack[1].m_num;
lean_object* v_comma_951_ = stack[3].m_obj;
lean_object* v_res_952_;
v_res_952_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(lean_box(0), v_t_949_, lean_box(0), v_comma_951_);
stack->m_obj
 = v_res_952_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___boxed(lean_object* v_motive_953_, lean_object* v_t_954_, lean_object* v_h_955_, lean_object* v_comma_956_){
_start:
{
uint8_t v_t_boxed_957_; lean_object* v_res_958_; 
v_t_boxed_957_ = lean_unbox(v_t_954_);
v_res_958_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(v_motive_953_, v_t_boxed_957_, v_h_955_, v_comma_956_);
lean_dec(v_comma_956_);
return v_res_958_;
}
}
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(lean_object* v_q_959_, uint8_t v_kind_960_){
_start:
{
lean_object* v_kinds_961_; lean_object* v_values_962_; lean_object* v_objectFieldKeys_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_972_; 
v_kinds_961_ = lean_ctor_get(v_q_959_, 0);
v_values_962_ = lean_ctor_get(v_q_959_, 1);
v_objectFieldKeys_963_ = lean_ctor_get(v_q_959_, 2);
v_isSharedCheck_972_ = !lean_is_exclusive(v_q_959_);
if (v_isSharedCheck_972_ == 0)
{
v___x_965_ = v_q_959_;
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_objectFieldKeys_963_);
lean_inc(v_values_962_);
lean_inc(v_kinds_961_);
lean_dec(v_q_959_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = lean_box(v_kind_960_);
v___x_968_ = lean_array_push(v_kinds_961_, v___x_967_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_968_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_values_962_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_objectFieldKeys_963_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_959_ = stack[0].m_obj;
uint8_t v_kind_960_ = stack[1].m_num;
lean_object* v_res_973_;
v_res_973_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(v_q_959_, v_kind_960_);
stack->m_obj
 = v_res_973_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind___boxed(lean_object* v_q_974_, lean_object* v_kind_975_){
_start:
{
uint8_t v_kind_boxed_976_; lean_object* v_res_977_; 
v_kind_boxed_976_ = lean_unbox(v_kind_975_);
v_res_977_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(v_q_974_, v_kind_boxed_976_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushValue(lean_object* v_q_978_, lean_object* v_value_979_){
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
v___x_986_ = lean_array_push(v_values_981_, v_value_979_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 1, v___x_986_);
v___x_988_ = v___x_984_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_kinds_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_objectFieldKeys_982_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushObjectFieldKey(lean_object* v_q_991_, lean_object* v_objectFieldKey_992_){
_start:
{
lean_object* v_kinds_993_; lean_object* v_values_994_; lean_object* v_objectFieldKeys_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1003_; 
v_kinds_993_ = lean_ctor_get(v_q_991_, 0);
v_values_994_ = lean_ctor_get(v_q_991_, 1);
v_objectFieldKeys_995_ = lean_ctor_get(v_q_991_, 2);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_q_991_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_997_ = v_q_991_;
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_objectFieldKeys_995_);
lean_inc(v_values_994_);
lean_inc(v_kinds_993_);
lean_dec(v_q_991_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = lean_array_push(v_objectFieldKeys_995_, v_objectFieldKey_992_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 2, v___x_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_kinds_993_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_values_994_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind___redArg(lean_object* v_q_1004_){
_start:
{
lean_object* v_kinds_1005_; lean_object* v_values_1006_; lean_object* v_objectFieldKeys_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1020_; 
v_kinds_1005_ = lean_ctor_get(v_q_1004_, 0);
v_values_1006_ = lean_ctor_get(v_q_1004_, 1);
v_objectFieldKeys_1007_ = lean_ctor_get(v_q_1004_, 2);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_q_1004_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1009_ = v_q_1004_;
v_isShared_1010_ = v_isSharedCheck_1020_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_objectFieldKeys_1007_);
lean_inc(v_values_1006_);
lean_inc(v_kinds_1005_);
lean_dec(v_q_1004_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1020_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_kind_1014_; lean_object* v___x_1015_; lean_object* v_q_1017_; 
v___x_1011_ = lean_array_get_size(v_kinds_1005_);
v___x_1012_ = lean_unsigned_to_nat(1u);
v___x_1013_ = lean_nat_sub(v___x_1011_, v___x_1012_);
v_kind_1014_ = lean_array_fget(v_kinds_1005_, v___x_1013_);
lean_dec(v___x_1013_);
v___x_1015_ = lean_array_pop(v_kinds_1005_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1015_);
v_q_1017_ = v___x_1009_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_values_1006_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_objectFieldKeys_1007_);
v_q_1017_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v_kind_1014_);
lean_ctor_set(v___x_1018_, 1, v_q_1017_);
return v___x_1018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind(lean_object* v_q_1021_, lean_object* v_h_1022_){
_start:
{
lean_object* v_kinds_1023_; lean_object* v_values_1024_; lean_object* v_objectFieldKeys_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1038_; 
v_kinds_1023_ = lean_ctor_get(v_q_1021_, 0);
v_values_1024_ = lean_ctor_get(v_q_1021_, 1);
v_objectFieldKeys_1025_ = lean_ctor_get(v_q_1021_, 2);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_q_1021_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1027_ = v_q_1021_;
v_isShared_1028_ = v_isSharedCheck_1038_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_objectFieldKeys_1025_);
lean_inc(v_values_1024_);
lean_inc(v_kinds_1023_);
lean_dec(v_q_1021_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1038_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_kind_1032_; lean_object* v___x_1033_; lean_object* v_q_1035_; 
v___x_1029_ = lean_array_get_size(v_kinds_1023_);
v___x_1030_ = lean_unsigned_to_nat(1u);
v___x_1031_ = lean_nat_sub(v___x_1029_, v___x_1030_);
v_kind_1032_ = lean_array_fget(v_kinds_1023_, v___x_1031_);
lean_dec(v___x_1031_);
v___x_1033_ = lean_array_pop(v_kinds_1023_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1033_);
v_q_1035_ = v___x_1027_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_values_1024_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_objectFieldKeys_1025_);
v_q_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_kind_1032_);
lean_ctor_set(v___x_1036_, 1, v_q_1035_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popValue_x21(lean_object* v_q_1039_){
_start:
{
lean_object* v_kinds_1040_; lean_object* v_values_1041_; lean_object* v_objectFieldKeys_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1056_; 
v_kinds_1040_ = lean_ctor_get(v_q_1039_, 0);
v_values_1041_ = lean_ctor_get(v_q_1039_, 1);
v_objectFieldKeys_1042_ = lean_ctor_get(v_q_1039_, 2);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_q_1039_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1044_ = v_q_1039_;
v_isShared_1045_ = v_isSharedCheck_1056_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_objectFieldKeys_1042_);
lean_inc(v_values_1041_);
lean_inc(v_kinds_1040_);
lean_dec(v_q_1039_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1056_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_value_1050_; lean_object* v___x_1051_; lean_object* v_q_1053_; 
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_array_get_size(v_values_1041_);
v___x_1048_ = lean_unsigned_to_nat(1u);
v___x_1049_ = lean_nat_sub(v___x_1047_, v___x_1048_);
v_value_1050_ = lean_array_get(v___x_1046_, v_values_1041_, v___x_1049_);
lean_dec(v___x_1049_);
v___x_1051_ = lean_array_pop(v_values_1041_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v___x_1051_);
v_q_1053_ = v___x_1044_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_kinds_1040_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1055_, 2, v_objectFieldKeys_1042_);
v_q_1053_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_value_1050_);
lean_ctor_set(v___x_1054_, 1, v_q_1053_);
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21(lean_object* v_q_1058_){
_start:
{
lean_object* v_kinds_1059_; lean_object* v_values_1060_; lean_object* v_objectFieldKeys_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1075_; 
v_kinds_1059_ = lean_ctor_get(v_q_1058_, 0);
v_values_1060_ = lean_ctor_get(v_q_1058_, 1);
v_objectFieldKeys_1061_ = lean_ctor_get(v_q_1058_, 2);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_q_1058_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1063_ = v_q_1058_;
v_isShared_1064_ = v_isSharedCheck_1075_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_objectFieldKeys_1061_);
lean_inc(v_values_1060_);
lean_inc(v_kinds_1059_);
lean_dec(v_q_1058_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1075_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v_objectFieldKey_1069_; lean_object* v___x_1070_; lean_object* v_q_1072_; 
v___x_1065_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1066_ = lean_array_get_size(v_objectFieldKeys_1061_);
v___x_1067_ = lean_unsigned_to_nat(1u);
v___x_1068_ = lean_nat_sub(v___x_1066_, v___x_1067_);
v_objectFieldKey_1069_ = lean_array_get(v___x_1065_, v_objectFieldKeys_1061_, v___x_1068_);
lean_dec(v___x_1068_);
v___x_1070_ = lean_array_pop(v_objectFieldKeys_1061_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 2, v___x_1070_);
v_q_1072_ = v___x_1063_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_kinds_1059_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_values_1060_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v___x_1070_);
v_q_1072_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_objectFieldKey_1069_);
lean_ctor_set(v___x_1073_, 1, v_q_1072_);
return v___x_1073_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(lean_object* v_as_1076_, size_t v_i_1077_, size_t v_stop_1078_, lean_object* v_b_1079_){
_start:
{
uint8_t v___x_1080_; 
v___x_1080_ = lean_usize_dec_eq(v_i_1077_, v_stop_1078_);
if (v___x_1080_ == 0)
{
lean_object* v_kinds_1081_; lean_object* v_values_1082_; lean_object* v_objectFieldKeys_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1098_; 
v_kinds_1081_ = lean_ctor_get(v_b_1079_, 0);
v_values_1082_ = lean_ctor_get(v_b_1079_, 1);
v_objectFieldKeys_1083_ = lean_ctor_get(v_b_1079_, 2);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_b_1079_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1085_ = v_b_1079_;
v_isShared_1086_ = v_isSharedCheck_1098_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_objectFieldKeys_1083_);
lean_inc(v_values_1082_);
lean_inc(v_kinds_1081_);
lean_dec(v_b_1079_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1098_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1087_ = ((size_t)1ULL);
v___x_1088_ = lean_usize_sub(v_i_1077_, v___x_1087_);
v___x_1089_ = lean_array_uget_borrowed(v_as_1076_, v___x_1088_);
v___x_1090_ = 1;
v___x_1091_ = lean_box(v___x_1090_);
v___x_1092_ = lean_array_push(v_kinds_1081_, v___x_1091_);
lean_inc(v___x_1089_);
v___x_1093_ = lean_array_push(v_values_1082_, v___x_1089_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 1, v___x_1093_);
lean_ctor_set(v___x_1085_, 0, v___x_1092_);
v___x_1095_ = v___x_1085_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_objectFieldKeys_1083_);
v___x_1095_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v_i_1077_ = v___x_1088_;
v_b_1079_ = v___x_1095_;
goto _start;
}
}
}
else
{
return v_b_1079_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1076_ = stack[0].m_obj;
size_t v_i_1077_ = stack[1].m_num;
size_t v_stop_1078_ = stack[2].m_num;
lean_object* v_b_1079_ = stack[3].m_obj;
lean_object* v_res_1099_;
v_res_1099_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_as_1076_, v_i_1077_, v_stop_1078_, v_b_1079_);
stack->m_obj
 = v_res_1099_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0___boxed(lean_object* v_as_1100_, lean_object* v_i_1101_, lean_object* v_stop_1102_, lean_object* v_b_1103_){
_start:
{
size_t v_i_boxed_1104_; size_t v_stop_boxed_1105_; lean_object* v_res_1106_; 
v_i_boxed_1104_ = lean_unbox_usize(v_i_1101_);
lean_dec(v_i_1101_);
v_stop_boxed_1105_ = lean_unbox_usize(v_stop_1102_);
lean_dec(v_stop_1102_);
v_res_1106_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_as_1100_, v_i_boxed_1104_, v_stop_boxed_1105_, v_b_1103_);
lean_dec_ref(v_as_1100_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(lean_object* v_init_1107_, lean_object* v_x_1108_){
_start:
{
if (lean_obj_tag(v_x_1108_) == 0)
{
lean_object* v_k_1109_; lean_object* v_v_1110_; lean_object* v_l_1111_; lean_object* v_r_1112_; lean_object* v___x_1113_; lean_object* v_kinds_1114_; lean_object* v_values_1115_; lean_object* v_objectFieldKeys_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1129_; 
v_k_1109_ = lean_ctor_get(v_x_1108_, 1);
lean_inc(v_k_1109_);
v_v_1110_ = lean_ctor_get(v_x_1108_, 2);
lean_inc(v_v_1110_);
v_l_1111_ = lean_ctor_get(v_x_1108_, 3);
lean_inc(v_l_1111_);
v_r_1112_ = lean_ctor_get(v_x_1108_, 4);
lean_inc(v_r_1112_);
lean_dec_ref_known(v_x_1108_, 5);
v___x_1113_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_init_1107_, v_r_1112_);
v_kinds_1114_ = lean_ctor_get(v___x_1113_, 0);
v_values_1115_ = lean_ctor_get(v___x_1113_, 1);
v_objectFieldKeys_1116_ = lean_ctor_get(v___x_1113_, 2);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1118_ = v___x_1113_;
v_isShared_1119_ = v_isSharedCheck_1129_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_objectFieldKeys_1116_);
lean_inc(v_values_1115_);
lean_inc(v_kinds_1114_);
lean_dec(v___x_1113_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1129_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1120_ = 3;
v___x_1121_ = lean_box(v___x_1120_);
v___x_1122_ = lean_array_push(v_kinds_1114_, v___x_1121_);
v___x_1123_ = lean_array_push(v_objectFieldKeys_1116_, v_k_1109_);
v___x_1124_ = lean_array_push(v_values_1115_, v_v_1110_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 2, v___x_1123_);
lean_ctor_set(v___x_1118_, 1, v___x_1124_);
lean_ctor_set(v___x_1118_, 0, v___x_1122_);
v___x_1126_ = v___x_1118_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v___x_1123_);
v___x_1126_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
v_init_1107_ = v___x_1126_;
v_x_1108_ = v_l_1111_;
goto _start;
}
}
}
else
{
return v_init_1107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(lean_object* v_acc_1140_, lean_object* v_q_1141_){
_start:
{
lean_object* v_kinds_1142_; lean_object* v_values_1143_; lean_object* v_objectFieldKeys_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1325_; 
v_kinds_1142_ = lean_ctor_get(v_q_1141_, 0);
v_values_1143_ = lean_ctor_get(v_q_1141_, 1);
v_objectFieldKeys_1144_ = lean_ctor_get(v_q_1141_, 2);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_q_1141_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1146_ = v_q_1141_;
v_isShared_1147_ = v_isSharedCheck_1325_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_objectFieldKeys_1144_);
lean_inc(v_values_1143_);
lean_inc(v_kinds_1142_);
lean_dec(v_q_1141_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1325_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1148_ = lean_array_get_size(v_kinds_1142_);
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = lean_nat_dec_eq(v___x_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_kind_1153_; lean_object* v___x_1154_; lean_object* v_q_1156_; 
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_sub(v___x_1148_, v___x_1151_);
v_kind_1153_ = lean_array_fget(v_kinds_1142_, v___x_1152_);
lean_dec(v___x_1152_);
v___x_1154_ = lean_array_pop(v_kinds_1142_);
lean_inc_ref(v_objectFieldKeys_1144_);
lean_inc_ref(v_values_1143_);
lean_inc_ref(v___x_1154_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1154_);
v_q_1156_ = v___x_1146_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_values_1143_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v_objectFieldKeys_1144_);
v_q_1156_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_unbox(v_kind_1153_);
lean_dec(v_kind_1153_);
switch(v___x_1157_)
{
case 0:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v_value_1161_; lean_object* v___x_1162_; lean_object* v_q_1163_; lean_object* v___y_1165_; 
lean_dec_ref(v_q_1156_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_array_get_size(v_values_1143_);
v___x_1160_ = lean_nat_sub(v___x_1159_, v___x_1151_);
v_value_1161_ = lean_array_get(v___x_1158_, v_values_1143_, v___x_1160_);
lean_dec(v___x_1160_);
v___x_1162_ = lean_array_pop(v_values_1143_);
lean_inc_ref(v_objectFieldKeys_1144_);
lean_inc_ref(v___x_1162_);
lean_inc_ref(v___x_1154_);
v_q_1163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1163_, 0, v___x_1154_);
lean_ctor_set(v_q_1163_, 1, v___x_1162_);
lean_ctor_set(v_q_1163_, 2, v_objectFieldKeys_1144_);
switch(lean_obj_tag(v_value_1161_))
{
case 0:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec_ref(v___x_1162_);
lean_dec_ref(v___x_1154_);
lean_dec_ref(v_objectFieldKeys_1144_);
v___x_1168_ = ((lean_object*)(l_Lean_Json_render___closed__0));
v___x_1169_ = lean_string_append(v_acc_1140_, v___x_1168_);
v_acc_1140_ = v___x_1169_;
v_q_1141_ = v_q_1163_;
goto _start;
}
case 1:
{
uint8_t v_b_1171_; 
lean_dec_ref(v___x_1162_);
lean_dec_ref(v___x_1154_);
lean_dec_ref(v_objectFieldKeys_1144_);
v_b_1171_ = lean_ctor_get_uint8(v_value_1161_, 0);
lean_dec_ref_known(v_value_1161_, 0);
if (v_b_1171_ == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = ((lean_object*)(l_Lean_Json_render___closed__2));
v___y_1165_ = v___x_1172_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1173_; 
v___x_1173_ = ((lean_object*)(l_Lean_Json_render___closed__4));
v___y_1165_ = v___x_1173_;
goto v___jp_1164_;
}
}
case 2:
{
lean_object* v_n_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec_ref(v___x_1162_);
lean_dec_ref(v___x_1154_);
lean_dec_ref(v_objectFieldKeys_1144_);
v_n_1174_ = lean_ctor_get(v_value_1161_, 0);
lean_inc_ref(v_n_1174_);
lean_dec_ref_known(v_value_1161_, 1);
v___x_1175_ = l_Lean_JsonNumber_toString(v_n_1174_);
v___x_1176_ = lean_string_append(v_acc_1140_, v___x_1175_);
lean_dec_ref(v___x_1175_);
v_acc_1140_ = v___x_1176_;
v_q_1141_ = v_q_1163_;
goto _start;
}
case 3:
{
lean_object* v_s_1178_; lean_object* v___x_1179_; lean_object* v_acc_1180_; uint8_t v___x_1181_; 
lean_dec_ref(v___x_1162_);
lean_dec_ref(v___x_1154_);
lean_dec_ref(v_objectFieldKeys_1144_);
v_s_1178_ = lean_ctor_get(v_value_1161_, 0);
lean_inc_ref(v_s_1178_);
lean_dec_ref_known(v_value_1161_, 1);
v___x_1179_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1180_ = lean_string_append(v_acc_1140_, v___x_1179_);
v___x_1181_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_1178_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_string_append(v_acc_1180_, v_s_1178_);
lean_dec_ref(v_s_1178_);
v___x_1183_ = lean_string_append(v___x_1182_, v___x_1179_);
v_acc_1140_ = v___x_1183_;
v_q_1141_ = v_q_1163_;
goto _start;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_string_utf8_byte_size(v_s_1178_);
v___x_1186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1185_, v_s_1178_, v___x_1149_, v_acc_1180_);
lean_dec_ref(v_s_1178_);
v___x_1187_ = lean_string_append(v___x_1186_, v___x_1179_);
v_acc_1140_ = v___x_1187_;
v_q_1141_ = v_q_1163_;
goto _start;
}
}
case 4:
{
lean_object* v_elems_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v_q_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
lean_dec_ref_known(v_q_1163_, 3);
v_elems_1189_ = lean_ctor_get(v_value_1161_, 0);
lean_inc_ref(v_elems_1189_);
lean_dec_ref_known(v_value_1161_, 1);
v___x_1190_ = 2;
v___x_1191_ = lean_box(v___x_1190_);
v___x_1192_ = lean_array_push(v___x_1154_, v___x_1191_);
v_q_1193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1193_, 0, v___x_1192_);
lean_ctor_set(v_q_1193_, 1, v___x_1162_);
lean_ctor_set(v_q_1193_, 2, v_objectFieldKeys_1144_);
v___x_1194_ = ((lean_object*)(l_Lean_Json_render___closed__9));
v___x_1195_ = lean_string_append(v_acc_1140_, v___x_1194_);
v___x_1196_ = lean_array_get_size(v_elems_1189_);
v___x_1197_ = lean_nat_dec_lt(v___x_1149_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_dec_ref(v_elems_1189_);
v_acc_1140_ = v___x_1195_;
v_q_1141_ = v_q_1193_;
goto _start;
}
else
{
size_t v___x_1199_; size_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_usize_of_nat(v___x_1196_);
v___x_1200_ = ((size_t)0ULL);
v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_elems_1189_, v___x_1199_, v___x_1200_, v_q_1193_);
lean_dec_ref(v_elems_1189_);
v_acc_1140_ = v___x_1195_;
v_q_1141_ = v___x_1201_;
goto _start;
}
}
default: 
{
lean_object* v_kvPairs_1203_; uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_q_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref_known(v_q_1163_, 3);
v_kvPairs_1203_ = lean_ctor_get(v_value_1161_, 0);
lean_inc(v_kvPairs_1203_);
lean_dec_ref_known(v_value_1161_, 1);
v___x_1204_ = 4;
v___x_1205_ = lean_box(v___x_1204_);
v___x_1206_ = lean_array_push(v___x_1154_, v___x_1205_);
v_q_1207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1207_, 0, v___x_1206_);
lean_ctor_set(v_q_1207_, 1, v___x_1162_);
lean_ctor_set(v_q_1207_, 2, v_objectFieldKeys_1144_);
v___x_1208_ = ((lean_object*)(l_Lean_Json_render___closed__15));
v___x_1209_ = lean_string_append(v_acc_1140_, v___x_1208_);
v___x_1210_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_q_1207_, v_kvPairs_1203_);
v_acc_1140_ = v___x_1209_;
v_q_1141_ = v___x_1210_;
goto _start;
}
}
v___jp_1164_:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_string_append(v_acc_1140_, v___y_1165_);
v_acc_1140_ = v___x_1166_;
v_q_1141_ = v_q_1163_;
goto _start;
}
}
case 1:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_value_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
lean_dec_ref(v_q_1156_);
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_array_get_size(v_values_1143_);
v___x_1214_ = lean_nat_sub(v___x_1213_, v___x_1151_);
v_value_1215_ = lean_array_get(v___x_1212_, v_values_1143_, v___x_1214_);
lean_dec(v___x_1214_);
v___x_1216_ = lean_array_get_size(v___x_1154_);
v___x_1217_ = lean_nat_dec_eq(v___x_1216_, v___x_1149_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_kind_1220_; uint8_t v___x_1221_; 
v___x_1218_ = lean_array_pop(v_values_1143_);
v___x_1219_ = lean_nat_sub(v___x_1216_, v___x_1151_);
v_kind_1220_ = lean_array_fget_borrowed(v___x_1154_, v___x_1219_);
lean_dec(v___x_1219_);
v___x_1221_ = lean_unbox(v_kind_1220_);
if (v___x_1221_ == 2)
{
uint8_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1222_ = 0;
v___x_1223_ = lean_box(v___x_1222_);
v___x_1224_ = lean_array_push(v___x_1154_, v___x_1223_);
v___x_1225_ = lean_array_push(v___x_1218_, v_value_1215_);
v___x_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
lean_ctor_set(v___x_1226_, 2, v_objectFieldKeys_1144_);
v_q_1141_ = v___x_1226_;
goto _start;
}
else
{
uint8_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1228_ = 5;
v___x_1229_ = lean_box(v___x_1228_);
v___x_1230_ = lean_array_push(v___x_1154_, v___x_1229_);
v___x_1231_ = 0;
v___x_1232_ = lean_box(v___x_1231_);
v___x_1233_ = lean_array_push(v___x_1230_, v___x_1232_);
v___x_1234_ = lean_array_push(v___x_1218_, v_value_1215_);
v___x_1235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
lean_ctor_set(v___x_1235_, 2, v_objectFieldKeys_1144_);
v_q_1141_ = v___x_1235_;
goto _start;
}
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec_ref(v___x_1154_);
lean_dec_ref(v_objectFieldKeys_1144_);
lean_dec_ref(v_values_1143_);
v___x_1237_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0));
v___x_1238_ = lean_mk_empty_array_with_capacity(v___x_1151_);
v___x_1239_ = lean_array_push(v___x_1238_, v_value_1215_);
v___x_1240_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1237_);
lean_ctor_set(v___x_1241_, 1, v___x_1239_);
lean_ctor_set(v___x_1241_, 2, v___x_1240_);
v_q_1141_ = v___x_1241_;
goto _start;
}
}
case 2:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec_ref(v___x_1154_);
lean_dec_ref(v_objectFieldKeys_1144_);
lean_dec_ref(v_values_1143_);
v___x_1243_ = ((lean_object*)(l_Lean_Json_render___closed__10));
v___x_1244_ = lean_string_append(v_acc_1140_, v___x_1243_);
v_acc_1140_ = v___x_1244_;
v_q_1141_ = v_q_1156_;
goto _start;
}
case 3:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_objectFieldKey_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_value_1253_; lean_object* v___y_1255_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
lean_dec_ref(v_q_1156_);
v___x_1246_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1247_ = lean_array_get_size(v_objectFieldKeys_1144_);
v___x_1248_ = lean_nat_sub(v___x_1247_, v___x_1151_);
v_objectFieldKey_1249_ = lean_array_get(v___x_1246_, v_objectFieldKeys_1144_, v___x_1248_);
lean_dec(v___x_1248_);
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_array_get_size(v_values_1143_);
v___x_1252_ = lean_nat_sub(v___x_1251_, v___x_1151_);
v_value_1253_ = lean_array_get(v___x_1250_, v_values_1143_, v___x_1252_);
lean_dec(v___x_1252_);
v___x_1264_ = lean_array_get_size(v___x_1154_);
v___x_1265_ = lean_nat_dec_eq(v___x_1264_, v___x_1149_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___y_1269_; lean_object* v___y_1282_; lean_object* v___x_1291_; lean_object* v_kind_1292_; uint8_t v___x_1293_; 
v___x_1266_ = lean_array_pop(v_objectFieldKeys_1144_);
v___x_1267_ = lean_array_pop(v_values_1143_);
v___x_1291_ = lean_nat_sub(v___x_1264_, v___x_1151_);
v_kind_1292_ = lean_array_fget_borrowed(v___x_1154_, v___x_1291_);
lean_dec(v___x_1291_);
v___x_1293_ = lean_unbox(v_kind_1292_);
if (v___x_1293_ == 4)
{
lean_object* v___x_1294_; lean_object* v_acc_1295_; uint8_t v___x_1296_; 
v___x_1294_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1295_ = lean_string_append(v_acc_1140_, v___x_1294_);
v___x_1296_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1249_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_string_append(v_acc_1295_, v_objectFieldKey_1249_);
lean_dec(v_objectFieldKey_1249_);
v___x_1298_ = lean_string_append(v___x_1297_, v___x_1294_);
v___y_1282_ = v___x_1298_;
goto v___jp_1281_;
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_string_utf8_byte_size(v_objectFieldKey_1249_);
v___x_1300_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1299_, v_objectFieldKey_1249_, v___x_1149_, v_acc_1295_);
lean_dec(v_objectFieldKey_1249_);
v___x_1301_ = lean_string_append(v___x_1300_, v___x_1294_);
v___y_1282_ = v___x_1301_;
goto v___jp_1281_;
}
}
else
{
lean_object* v___x_1302_; lean_object* v_acc_1303_; uint8_t v___x_1304_; 
v___x_1302_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1303_ = lean_string_append(v_acc_1140_, v___x_1302_);
v___x_1304_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1249_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_string_append(v_acc_1303_, v_objectFieldKey_1249_);
lean_dec(v_objectFieldKey_1249_);
v___x_1306_ = lean_string_append(v___x_1305_, v___x_1302_);
v___y_1269_ = v___x_1306_;
goto v___jp_1268_;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_string_utf8_byte_size(v_objectFieldKey_1249_);
v___x_1308_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1307_, v_objectFieldKey_1249_, v___x_1149_, v_acc_1303_);
lean_dec(v_objectFieldKey_1249_);
v___x_1309_ = lean_string_append(v___x_1308_, v___x_1302_);
v___y_1269_ = v___x_1309_;
goto v___jp_1268_;
}
}
v___jp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1270_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1271_ = lean_string_append(v___y_1269_, v___x_1270_);
v___x_1272_ = 5;
v___x_1273_ = lean_box(v___x_1272_);
v___x_1274_ = lean_array_push(v___x_1154_, v___x_1273_);
v___x_1275_ = 0;
v___x_1276_ = lean_box(v___x_1275_);
v___x_1277_ = lean_array_push(v___x_1274_, v___x_1276_);
v___x_1278_ = lean_array_push(v___x_1267_, v_value_1253_);
v___x_1279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
lean_ctor_set(v___x_1279_, 2, v___x_1266_);
v_acc_1140_ = v___x_1271_;
v_q_1141_ = v___x_1279_;
goto _start;
}
v___jp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1283_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1284_ = lean_string_append(v___y_1282_, v___x_1283_);
v___x_1285_ = 0;
v___x_1286_ = lean_box(v___x_1285_);
v___x_1287_ = lean_array_push(v___x_1154_, v___x_1286_);
v___x_1288_ = lean_array_push(v___x_1267_, v_value_1253_);
v___x_1289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
lean_ctor_set(v___x_1289_, 2, v___x_1266_);
v_acc_1140_ = v___x_1284_;
v_q_1141_ = v___x_1289_;
goto _start;
}
}
else
{
lean_object* v___x_1310_; lean_object* v_acc_1311_; uint8_t v___x_1312_; 
lean_dec_ref(v___x_1154_);
lean_dec_ref(v_objectFieldKeys_1144_);
lean_dec_ref(v_values_1143_);
v___x_1310_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1311_ = lean_string_append(v_acc_1140_, v___x_1310_);
v___x_1312_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1249_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_string_append(v_acc_1311_, v_objectFieldKey_1249_);
lean_dec(v_objectFieldKey_1249_);
v___x_1314_ = lean_string_append(v___x_1313_, v___x_1310_);
v___y_1255_ = v___x_1314_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = lean_string_utf8_byte_size(v_objectFieldKey_1249_);
v___x_1316_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1315_, v_objectFieldKey_1249_, v___x_1149_, v_acc_1311_);
lean_dec(v_objectFieldKey_1249_);
v___x_1317_ = lean_string_append(v___x_1316_, v___x_1310_);
v___y_1255_ = v___x_1317_;
goto v___jp_1254_;
}
}
v___jp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1256_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1257_ = lean_string_append(v___y_1255_, v___x_1256_);
v___x_1258_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0));
v___x_1259_ = lean_mk_empty_array_with_capacity(v___x_1151_);
v___x_1260_ = lean_array_push(v___x_1259_, v_value_1253_);
v___x_1261_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1258_);
lean_ctor_set(v___x_1262_, 1, v___x_1260_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
v_acc_1140_ = v___x_1257_;
v_q_1141_ = v___x_1262_;
goto _start;
}
}
case 4:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref(v___x_1154_);
lean_dec_ref(v_objectFieldKeys_1144_);
lean_dec_ref(v_values_1143_);
v___x_1318_ = ((lean_object*)(l_Lean_Json_render___closed__16));
v___x_1319_ = lean_string_append(v_acc_1140_, v___x_1318_);
v_acc_1140_ = v___x_1319_;
v_q_1141_ = v_q_1156_;
goto _start;
}
default: 
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec_ref(v___x_1154_);
lean_dec_ref(v_objectFieldKeys_1144_);
lean_dec_ref(v_values_1143_);
v___x_1321_ = ((lean_object*)(l_Lean_Json_render___closed__6));
v___x_1322_ = lean_string_append(v_acc_1140_, v___x_1321_);
v_acc_1140_ = v___x_1322_;
v_q_1141_ = v_q_1156_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_1146_);
lean_dec_ref(v_objectFieldKeys_1144_);
lean_dec_ref(v_values_1143_);
lean_dec_ref(v_kinds_1142_);
return v_acc_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_compress(lean_object* v_j_1331_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1333_ = lean_unsigned_to_nat(1u);
v___x_1334_ = lean_mk_empty_array_with_capacity(v___x_1333_);
v___x_1335_ = ((lean_object*)(l_Lean_Json_compress___closed__0));
v___x_1336_ = lean_array_push(v___x_1334_, v_j_1331_);
v___x_1337_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1335_);
lean_ctor_set(v___x_1338_, 1, v___x_1336_);
lean_ctor_set(v___x_1338_, 2, v___x_1337_);
v___x_1339_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(v___x_1332_, v___x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instToString___lam__0(lean_object* v_j_1342_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_unsigned_to_nat(80u);
v___x_1344_ = l_Lean_Json_pretty(v_j_1342_, v___x_1343_);
return v___x_1344_;
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
