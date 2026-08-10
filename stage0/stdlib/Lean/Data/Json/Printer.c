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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_String_Slice_positions(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_pretty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___boxed(lean_object*);
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
uint8_t v___x_604_; 
v___x_604_ = lean_nat_dec_eq(v_it_600_, v___x_598_);
if (v___x_604_ == 0)
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
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_string_utf8_byte_size(v_s_616_);
lean_inc_ref(v_s_616_);
v___f_622_ = lean_alloc_closure((void*)(l_Lean_Json_escape___lam__0___boxed), 6, 2);
lean_closure_set(v___f_622_, 0, v___x_621_);
lean_closure_set(v___f_622_, 1, v_s_616_);
v___x_623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_623_, 0, v_s_616_);
lean_ctor_set(v___x_623_, 1, v___x_620_);
lean_ctor_set(v___x_623_, 2, v___x_621_);
v___x_624_ = l_String_Slice_positions(v___x_623_);
lean_dec_ref_known(v___x_623_, 3);
v___x_625_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_622_, v___x_624_, v_acc_617_, lean_box(0));
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object* v_s_627_, lean_object* v_acc_628_){
_start:
{
lean_object* v___x_629_; lean_object* v_acc_630_; uint8_t v___x_631_; 
v___x_629_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_630_ = lean_string_append(v_acc_628_, v___x_629_);
v___x_631_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_627_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_string_append(v_acc_630_, v_s_627_);
lean_dec_ref(v_s_627_);
v___x_633_ = lean_string_append(v___x_632_, v___x_629_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = lean_string_utf8_byte_size(v_s_627_);
lean_inc_ref(v_s_627_);
v___f_636_ = lean_alloc_closure((void*)(l_Lean_Json_escape___lam__0___boxed), 6, 2);
lean_closure_set(v___f_636_, 0, v___x_635_);
lean_closure_set(v___f_636_, 1, v_s_627_);
v___x_637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_637_, 0, v_s_627_);
lean_ctor_set(v___x_637_, 1, v___x_634_);
lean_ctor_set(v___x_637_, 2, v___x_635_);
v___x_638_ = l_String_Slice_positions(v___x_637_);
lean_dec_ref_known(v___x_637_, 3);
v___x_639_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_636_, v___x_638_, v_acc_630_, lean_box(0));
v___x_640_ = lean_string_append(v___x_639_, v___x_629_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_render_spec__3(lean_object* v_a_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_nat_to_int(v_a_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(lean_object* v___x_643_, lean_object* v_k_644_, lean_object* v_a_645_, lean_object* v_b_646_){
_start:
{
lean_object* v_startInclusive_647_; lean_object* v_endExclusive_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_startInclusive_647_ = lean_ctor_get(v___x_643_, 1);
v_endExclusive_648_ = lean_ctor_get(v___x_643_, 2);
v___x_649_ = lean_nat_sub(v_endExclusive_648_, v_startInclusive_647_);
v___x_650_ = lean_nat_dec_eq(v_a_645_, v___x_649_);
lean_dec(v___x_649_);
if (v___x_650_ == 0)
{
uint32_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = lean_string_utf8_get_fast(v_k_644_, v_a_645_);
v___x_652_ = lean_string_utf8_next_fast(v_k_644_, v_a_645_);
lean_dec(v_a_645_);
v___x_653_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_b_646_, v___x_651_);
v_a_645_ = v___x_652_;
v_b_646_ = v___x_653_;
goto _start;
}
else
{
lean_dec(v_a_645_);
return v_b_646_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg___boxed(lean_object* v___x_655_, lean_object* v_k_656_, lean_object* v_a_657_, lean_object* v_b_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_655_, v_k_656_, v_a_657_, v_b_658_);
lean_dec_ref(v_k_656_);
lean_dec_ref(v___x_655_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Json_render_spec__2_spec__2(lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
lean_dec(v_x_660_);
return v_x_661_;
}
else
{
lean_object* v_head_663_; lean_object* v_tail_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_673_; 
v_head_663_ = lean_ctor_get(v_x_662_, 0);
v_tail_664_ = lean_ctor_get(v_x_662_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_662_);
if (v_isSharedCheck_673_ == 0)
{
v___x_666_ = v_x_662_;
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_tail_664_);
lean_inc(v_head_663_);
lean_dec(v_x_662_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
lean_inc(v_x_660_);
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 5);
lean_ctor_set(v___x_666_, 1, v_x_660_);
lean_ctor_set(v___x_666_, 0, v_x_661_);
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_x_661_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_x_660_);
v___x_669_ = v_reuseFailAlloc_672_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v_head_663_);
v_x_661_ = v___x_670_;
v_x_662_ = v_tail_664_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
if (lean_obj_tag(v_x_674_) == 0)
{
lean_object* v___x_676_; 
lean_dec(v_x_675_);
v___x_676_ = lean_box(0);
return v___x_676_;
}
else
{
lean_object* v_tail_677_; 
v_tail_677_ = lean_ctor_get(v_x_674_, 1);
if (lean_obj_tag(v_tail_677_) == 0)
{
lean_object* v_head_678_; 
lean_dec(v_x_675_);
v_head_678_ = lean_ctor_get(v_x_674_, 0);
lean_inc(v_head_678_);
lean_dec_ref_known(v_x_674_, 2);
return v_head_678_;
}
else
{
lean_object* v_head_679_; lean_object* v___x_680_; 
lean_inc(v_tail_677_);
v_head_679_ = lean_ctor_get(v_x_674_, 0);
lean_inc(v_head_679_);
lean_dec_ref_known(v_x_674_, 2);
v___x_680_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Json_render_spec__2_spec__2(v_x_675_, v_head_679_, v_tail_677_);
return v___x_680_;
}
}
}
}
static lean_object* _init_l_Lean_Json_render___closed__11(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lean_Json_render___closed__9));
v___x_698_ = lean_string_length(v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_Json_render___closed__12(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_obj_once(&l_Lean_Json_render___closed__11, &l_Lean_Json_render___closed__11_once, _init_l_Lean_Json_render___closed__11);
v___x_700_ = lean_nat_to_int(v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(lean_object* v_init_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_710_) == 0)
{
lean_object* v_k_711_; lean_object* v_v_712_; lean_object* v_l_713_; lean_object* v_r_714_; lean_object* v___x_715_; lean_object* v___y_717_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_k_711_ = lean_ctor_get(v_x_710_, 1);
lean_inc(v_k_711_);
v_v_712_ = lean_ctor_get(v_x_710_, 2);
lean_inc(v_v_712_);
v_l_713_ = lean_ctor_get(v_x_710_, 3);
lean_inc(v_l_713_);
v_r_714_ = lean_ctor_get(v_x_710_, 4);
lean_inc(v_r_714_);
lean_dec_ref_known(v_x_710_, 5);
v___x_715_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v_init_709_, v_l_713_);
v___x_729_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v___x_730_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_k_711_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_string_append(v___x_729_, v_k_711_);
lean_dec(v_k_711_);
v___x_732_ = lean_string_append(v___x_731_, v___x_729_);
v___y_717_ = v___x_732_;
goto v___jp_716_;
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_string_utf8_byte_size(v_k_711_);
lean_inc(v_k_711_);
v___x_735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_735_, 0, v_k_711_);
lean_ctor_set(v___x_735_, 1, v___x_733_);
lean_ctor_set(v___x_735_, 2, v___x_734_);
v___x_736_ = l_String_Slice_positions(v___x_735_);
v___x_737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_735_, v_k_711_, v___x_736_, v___x_729_);
lean_dec(v_k_711_);
lean_dec_ref_known(v___x_735_, 3);
v___x_738_ = lean_string_append(v___x_737_, v___x_729_);
v___y_717_ = v___x_738_;
goto v___jp_716_;
}
v___jp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_718_, 0, v___y_717_);
v___x_719_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__1));
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_box(1);
v___x_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = l_Lean_Json_render(v_v_712_);
v___x_724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = 0;
v___x_726_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*1, v___x_725_);
v___x_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_715_);
v_init_709_ = v___x_727_;
v_x_710_ = v_r_714_;
goto _start;
}
}
else
{
return v_init_709_;
}
}
}
static lean_object* _init_l_Lean_Json_render___closed__17(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(l_Lean_Json_render___closed__15));
v___x_741_ = lean_string_length(v___x_740_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_Json_render___closed__18(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_obj_once(&l_Lean_Json_render___closed__17, &l_Lean_Json_render___closed__17_once, _init_l_Lean_Json_render___closed__17);
v___x_743_ = lean_nat_to_int(v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_render(lean_object* v_x_749_){
_start:
{
switch(lean_obj_tag(v_x_749_))
{
case 0:
{
lean_object* v___x_750_; 
v___x_750_ = ((lean_object*)(l_Lean_Json_render___closed__1));
return v___x_750_;
}
case 1:
{
uint8_t v_b_751_; 
v_b_751_ = lean_ctor_get_uint8(v_x_749_, 0);
lean_dec_ref_known(v_x_749_, 0);
if (v_b_751_ == 0)
{
lean_object* v___x_752_; 
v___x_752_ = ((lean_object*)(l_Lean_Json_render___closed__3));
return v___x_752_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = ((lean_object*)(l_Lean_Json_render___closed__5));
return v___x_753_;
}
}
case 2:
{
lean_object* v_n_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_n_754_ = lean_ctor_get(v_x_749_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v_x_749_);
if (v_isSharedCheck_762_ == 0)
{
v___x_756_ = v_x_749_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_n_754_);
lean_dec(v_x_749_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = l_Lean_JsonNumber_toString(v_n_754_);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 3);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
case 3:
{
lean_object* v_s_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_783_; 
v_s_763_ = lean_ctor_get(v_x_749_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_x_749_);
if (v_isSharedCheck_783_ == 0)
{
v___x_765_ = v_x_749_;
v_isShared_766_ = v_isSharedCheck_783_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_s_763_);
lean_dec(v_x_749_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_783_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v___x_768_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_763_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_769_ = lean_string_append(v___x_767_, v_s_763_);
lean_dec_ref(v_s_763_);
v___x_770_ = lean_string_append(v___x_769_, v___x_767_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_770_);
v___x_772_ = v___x_765_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_string_utf8_byte_size(v_s_763_);
lean_inc_ref(v_s_763_);
v___x_776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_776_, 0, v_s_763_);
lean_ctor_set(v___x_776_, 1, v___x_774_);
lean_ctor_set(v___x_776_, 2, v___x_775_);
v___x_777_ = l_String_Slice_positions(v___x_776_);
v___x_778_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_776_, v_s_763_, v___x_777_, v___x_767_);
lean_dec_ref(v_s_763_);
lean_dec_ref_known(v___x_776_, 3);
v___x_779_ = lean_string_append(v___x_778_, v___x_767_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_779_);
v___x_781_ = v___x_765_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
case 4:
{
lean_object* v_elems_784_; size_t v_sz_785_; size_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_elems_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; 
v_elems_784_ = lean_ctor_get(v_x_749_, 0);
lean_inc_ref(v_elems_784_);
lean_dec_ref_known(v_x_749_, 1);
v_sz_785_ = lean_array_size(v_elems_784_);
v___x_786_ = ((size_t)0ULL);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(v_sz_785_, v___x_786_, v_elems_784_);
v___x_788_ = lean_array_to_list(v___x_787_);
v___x_789_ = ((lean_object*)(l_Lean_Json_render___closed__8));
v_elems_790_ = l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(v___x_788_, v___x_789_);
v___x_791_ = lean_obj_once(&l_Lean_Json_render___closed__12, &l_Lean_Json_render___closed__12_once, _init_l_Lean_Json_render___closed__12);
v___x_792_ = ((lean_object*)(l_Lean_Json_render___closed__13));
v___x_793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v_elems_790_);
v___x_794_ = ((lean_object*)(l_Lean_Json_render___closed__14));
v___x_795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_791_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = 0;
v___x_798_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*1, v___x_797_);
return v___x_798_;
}
default: 
{
lean_object* v_kvPairs_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_kvs_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; lean_object* v___x_811_; 
v_kvPairs_799_ = lean_ctor_get(v_x_749_, 0);
lean_inc(v_kvPairs_799_);
lean_dec_ref_known(v_x_749_, 1);
v___x_800_ = lean_box(0);
v___x_801_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v___x_800_, v_kvPairs_799_);
v___x_802_ = ((lean_object*)(l_Lean_Json_render___closed__8));
v_kvs_803_ = l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(v___x_801_, v___x_802_);
v___x_804_ = lean_obj_once(&l_Lean_Json_render___closed__18, &l_Lean_Json_render___closed__18_once, _init_l_Lean_Json_render___closed__18);
v___x_805_ = ((lean_object*)(l_Lean_Json_render___closed__19));
v___x_806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v_kvs_803_);
v___x_807_ = ((lean_object*)(l_Lean_Json_render___closed__20));
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_804_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = 0;
v___x_811_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*1, v___x_810_);
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(size_t v_sz_812_, size_t v_i_813_, lean_object* v_bs_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_usize_dec_lt(v_i_813_, v_sz_812_);
if (v___x_815_ == 0)
{
return v_bs_814_;
}
else
{
lean_object* v_v_816_; lean_object* v___x_817_; lean_object* v_bs_x27_818_; lean_object* v___x_819_; size_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; 
v_v_816_ = lean_array_uget(v_bs_814_, v_i_813_);
v___x_817_ = lean_unsigned_to_nat(0u);
v_bs_x27_818_ = lean_array_uset(v_bs_814_, v_i_813_, v___x_817_);
v___x_819_ = l_Lean_Json_render(v_v_816_);
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_add(v_i_813_, v___x_820_);
v___x_822_ = lean_array_uset(v_bs_x27_818_, v_i_813_, v___x_819_);
v_i_813_ = v___x_821_;
v_bs_814_ = v___x_822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1___boxed(lean_object* v_sz_824_, lean_object* v_i_825_, lean_object* v_bs_826_){
_start:
{
size_t v_sz_boxed_827_; size_t v_i_boxed_828_; lean_object* v_res_829_; 
v_sz_boxed_827_ = lean_unbox_usize(v_sz_824_);
lean_dec(v_sz_824_);
v_i_boxed_828_ = lean_unbox_usize(v_i_825_);
lean_dec(v_i_825_);
v_res_829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(v_sz_boxed_827_, v_i_boxed_828_, v_bs_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(lean_object* v___x_830_, lean_object* v_k_831_, lean_object* v_inst_832_, lean_object* v_R_833_, lean_object* v_a_834_, lean_object* v_b_835_, lean_object* v_c_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_830_, v_k_831_, v_a_834_, v_b_835_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___boxed(lean_object* v___x_838_, lean_object* v_k_839_, lean_object* v_inst_840_, lean_object* v_R_841_, lean_object* v_a_842_, lean_object* v_b_843_, lean_object* v_c_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(v___x_838_, v_k_839_, v_inst_840_, v_R_841_, v_a_842_, v_b_843_, v_c_844_);
lean_dec_ref(v_k_839_);
lean_dec_ref(v___x_838_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4(lean_object* v_init_846_, lean_object* v_t_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v_init_846_, v_t_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_pretty(lean_object* v_j_849_, lean_object* v_lineWidth_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = l_Lean_Json_render(v_j_849_);
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = l_Std_Format_pretty(v___x_851_, v_lineWidth_850_, v___x_852_, v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_pretty___boxed(lean_object* v_j_854_, lean_object* v_lineWidth_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Json_pretty(v_j_854_, v_lineWidth_855_);
lean_dec(v_lineWidth_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx(uint8_t v_x_857_){
_start:
{
switch(v_x_857_)
{
case 0:
{
lean_object* v___x_858_; 
v___x_858_ = lean_unsigned_to_nat(0u);
return v___x_858_;
}
case 1:
{
lean_object* v___x_859_; 
v___x_859_ = lean_unsigned_to_nat(1u);
return v___x_859_;
}
case 2:
{
lean_object* v___x_860_; 
v___x_860_ = lean_unsigned_to_nat(2u);
return v___x_860_;
}
case 3:
{
lean_object* v___x_861_; 
v___x_861_ = lean_unsigned_to_nat(3u);
return v___x_861_;
}
case 4:
{
lean_object* v___x_862_; 
v___x_862_ = lean_unsigned_to_nat(4u);
return v___x_862_;
}
default: 
{
lean_object* v___x_863_; 
v___x_863_ = lean_unsigned_to_nat(5u);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___boxed(lean_object* v_x_864_){
_start:
{
uint8_t v_x_boxed_865_; lean_object* v_res_866_; 
v_x_boxed_865_ = lean_unbox(v_x_864_);
v_res_866_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx(v_x_boxed_865_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg(lean_object* v_k_867_){
_start:
{
lean_inc(v_k_867_);
return v_k_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg___boxed(lean_object* v_k_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg(v_k_868_);
lean_dec(v_k_868_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(lean_object* v_motive_870_, lean_object* v_ctorIdx_871_, uint8_t v_t_872_, lean_object* v_h_873_, lean_object* v_k_874_){
_start:
{
lean_inc(v_k_874_);
return v_k_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___boxed(lean_object* v_motive_875_, lean_object* v_ctorIdx_876_, lean_object* v_t_877_, lean_object* v_h_878_, lean_object* v_k_879_){
_start:
{
uint8_t v_t_boxed_880_; lean_object* v_res_881_; 
v_t_boxed_880_ = lean_unbox(v_t_877_);
v_res_881_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(v_motive_875_, v_ctorIdx_876_, v_t_boxed_880_, v_h_878_, v_k_879_);
lean_dec(v_k_879_);
lean_dec(v_ctorIdx_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(lean_object* v_json_882_){
_start:
{
lean_inc(v_json_882_);
return v_json_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg___boxed(lean_object* v_json_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(v_json_883_);
lean_dec(v_json_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(lean_object* v_motive_885_, uint8_t v_t_886_, lean_object* v_h_887_, lean_object* v_json_888_){
_start:
{
lean_inc(v_json_888_);
return v_json_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___boxed(lean_object* v_motive_889_, lean_object* v_t_890_, lean_object* v_h_891_, lean_object* v_json_892_){
_start:
{
uint8_t v_t_boxed_893_; lean_object* v_res_894_; 
v_t_boxed_893_ = lean_unbox(v_t_890_);
v_res_894_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(v_motive_889_, v_t_boxed_893_, v_h_891_, v_json_892_);
lean_dec(v_json_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(lean_object* v_arrayElem_895_){
_start:
{
lean_inc(v_arrayElem_895_);
return v_arrayElem_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg___boxed(lean_object* v_arrayElem_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(v_arrayElem_896_);
lean_dec(v_arrayElem_896_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(lean_object* v_motive_898_, uint8_t v_t_899_, lean_object* v_h_900_, lean_object* v_arrayElem_901_){
_start:
{
lean_inc(v_arrayElem_901_);
return v_arrayElem_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___boxed(lean_object* v_motive_902_, lean_object* v_t_903_, lean_object* v_h_904_, lean_object* v_arrayElem_905_){
_start:
{
uint8_t v_t_boxed_906_; lean_object* v_res_907_; 
v_t_boxed_906_ = lean_unbox(v_t_903_);
v_res_907_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(v_motive_902_, v_t_boxed_906_, v_h_904_, v_arrayElem_905_);
lean_dec(v_arrayElem_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(lean_object* v_arrayEnd_908_){
_start:
{
lean_inc(v_arrayEnd_908_);
return v_arrayEnd_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg___boxed(lean_object* v_arrayEnd_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(v_arrayEnd_909_);
lean_dec(v_arrayEnd_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(lean_object* v_motive_911_, uint8_t v_t_912_, lean_object* v_h_913_, lean_object* v_arrayEnd_914_){
_start:
{
lean_inc(v_arrayEnd_914_);
return v_arrayEnd_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___boxed(lean_object* v_motive_915_, lean_object* v_t_916_, lean_object* v_h_917_, lean_object* v_arrayEnd_918_){
_start:
{
uint8_t v_t_boxed_919_; lean_object* v_res_920_; 
v_t_boxed_919_ = lean_unbox(v_t_916_);
v_res_920_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(v_motive_915_, v_t_boxed_919_, v_h_917_, v_arrayEnd_918_);
lean_dec(v_arrayEnd_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(lean_object* v_objectField_921_){
_start:
{
lean_inc(v_objectField_921_);
return v_objectField_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg___boxed(lean_object* v_objectField_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(v_objectField_922_);
lean_dec(v_objectField_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(lean_object* v_motive_924_, uint8_t v_t_925_, lean_object* v_h_926_, lean_object* v_objectField_927_){
_start:
{
lean_inc(v_objectField_927_);
return v_objectField_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___boxed(lean_object* v_motive_928_, lean_object* v_t_929_, lean_object* v_h_930_, lean_object* v_objectField_931_){
_start:
{
uint8_t v_t_boxed_932_; lean_object* v_res_933_; 
v_t_boxed_932_ = lean_unbox(v_t_929_);
v_res_933_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(v_motive_928_, v_t_boxed_932_, v_h_930_, v_objectField_931_);
lean_dec(v_objectField_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(lean_object* v_objectEnd_934_){
_start:
{
lean_inc(v_objectEnd_934_);
return v_objectEnd_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg___boxed(lean_object* v_objectEnd_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(v_objectEnd_935_);
lean_dec(v_objectEnd_935_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(lean_object* v_motive_937_, uint8_t v_t_938_, lean_object* v_h_939_, lean_object* v_objectEnd_940_){
_start:
{
lean_inc(v_objectEnd_940_);
return v_objectEnd_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___boxed(lean_object* v_motive_941_, lean_object* v_t_942_, lean_object* v_h_943_, lean_object* v_objectEnd_944_){
_start:
{
uint8_t v_t_boxed_945_; lean_object* v_res_946_; 
v_t_boxed_945_ = lean_unbox(v_t_942_);
v_res_946_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(v_motive_941_, v_t_boxed_945_, v_h_943_, v_objectEnd_944_);
lean_dec(v_objectEnd_944_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(lean_object* v_comma_947_){
_start:
{
lean_inc(v_comma_947_);
return v_comma_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg___boxed(lean_object* v_comma_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(v_comma_948_);
lean_dec(v_comma_948_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(lean_object* v_motive_950_, uint8_t v_t_951_, lean_object* v_h_952_, lean_object* v_comma_953_){
_start:
{
lean_inc(v_comma_953_);
return v_comma_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___boxed(lean_object* v_motive_954_, lean_object* v_t_955_, lean_object* v_h_956_, lean_object* v_comma_957_){
_start:
{
uint8_t v_t_boxed_958_; lean_object* v_res_959_; 
v_t_boxed_958_ = lean_unbox(v_t_955_);
v_res_959_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(v_motive_954_, v_t_boxed_958_, v_h_956_, v_comma_957_);
lean_dec(v_comma_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(lean_object* v_q_960_, uint8_t v_kind_961_){
_start:
{
lean_object* v_kinds_962_; lean_object* v_values_963_; lean_object* v_objectFieldKeys_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_973_; 
v_kinds_962_ = lean_ctor_get(v_q_960_, 0);
v_values_963_ = lean_ctor_get(v_q_960_, 1);
v_objectFieldKeys_964_ = lean_ctor_get(v_q_960_, 2);
v_isSharedCheck_973_ = !lean_is_exclusive(v_q_960_);
if (v_isSharedCheck_973_ == 0)
{
v___x_966_ = v_q_960_;
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_objectFieldKeys_964_);
lean_inc(v_values_963_);
lean_inc(v_kinds_962_);
lean_dec(v_q_960_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_968_ = lean_box(v_kind_961_);
v___x_969_ = lean_array_push(v_kinds_962_, v___x_968_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_969_);
v___x_971_ = v___x_966_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_values_963_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_objectFieldKeys_964_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(lean_object* v_as_1076_, size_t v_i_1077_, size_t v_stop_1078_, lean_object* v_b_1079_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0___boxed(lean_object* v_as_1099_, lean_object* v_i_1100_, lean_object* v_stop_1101_, lean_object* v_b_1102_){
_start:
{
size_t v_i_boxed_1103_; size_t v_stop_boxed_1104_; lean_object* v_res_1105_; 
v_i_boxed_1103_ = lean_unbox_usize(v_i_1100_);
lean_dec(v_i_1100_);
v_stop_boxed_1104_ = lean_unbox_usize(v_stop_1101_);
lean_dec(v_stop_1101_);
v_res_1105_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_as_1099_, v_i_boxed_1103_, v_stop_boxed_1104_, v_b_1102_);
lean_dec_ref(v_as_1099_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(lean_object* v_init_1106_, lean_object* v_x_1107_){
_start:
{
if (lean_obj_tag(v_x_1107_) == 0)
{
lean_object* v_k_1108_; lean_object* v_v_1109_; lean_object* v_l_1110_; lean_object* v_r_1111_; lean_object* v___x_1112_; lean_object* v_kinds_1113_; lean_object* v_values_1114_; lean_object* v_objectFieldKeys_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1128_; 
v_k_1108_ = lean_ctor_get(v_x_1107_, 1);
lean_inc(v_k_1108_);
v_v_1109_ = lean_ctor_get(v_x_1107_, 2);
lean_inc(v_v_1109_);
v_l_1110_ = lean_ctor_get(v_x_1107_, 3);
lean_inc(v_l_1110_);
v_r_1111_ = lean_ctor_get(v_x_1107_, 4);
lean_inc(v_r_1111_);
lean_dec_ref_known(v_x_1107_, 5);
v___x_1112_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_init_1106_, v_r_1111_);
v_kinds_1113_ = lean_ctor_get(v___x_1112_, 0);
v_values_1114_ = lean_ctor_get(v___x_1112_, 1);
v_objectFieldKeys_1115_ = lean_ctor_get(v___x_1112_, 2);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1117_ = v___x_1112_;
v_isShared_1118_ = v_isSharedCheck_1128_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_objectFieldKeys_1115_);
lean_inc(v_values_1114_);
lean_inc(v_kinds_1113_);
lean_dec(v___x_1112_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1128_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1119_ = 3;
v___x_1120_ = lean_box(v___x_1119_);
v___x_1121_ = lean_array_push(v_kinds_1113_, v___x_1120_);
v___x_1122_ = lean_array_push(v_objectFieldKeys_1115_, v_k_1108_);
v___x_1123_ = lean_array_push(v_values_1114_, v_v_1109_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 2, v___x_1122_);
lean_ctor_set(v___x_1117_, 1, v___x_1123_);
lean_ctor_set(v___x_1117_, 0, v___x_1121_);
v___x_1125_ = v___x_1117_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v___x_1122_);
v___x_1125_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
v_init_1106_ = v___x_1125_;
v_x_1107_ = v_l_1110_;
goto _start;
}
}
}
else
{
return v_init_1106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(lean_object* v_acc_1139_, lean_object* v_q_1140_){
_start:
{
lean_object* v_kinds_1141_; lean_object* v_values_1142_; lean_object* v_objectFieldKeys_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1332_; 
v_kinds_1141_ = lean_ctor_get(v_q_1140_, 0);
v_values_1142_ = lean_ctor_get(v_q_1140_, 1);
v_objectFieldKeys_1143_ = lean_ctor_get(v_q_1140_, 2);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_q_1140_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1145_ = v_q_1140_;
v_isShared_1146_ = v_isSharedCheck_1332_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_objectFieldKeys_1143_);
lean_inc(v_values_1142_);
lean_inc(v_kinds_1141_);
lean_dec(v_q_1140_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1332_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = lean_array_get_size(v_kinds_1141_);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_nat_dec_eq(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_kind_1152_; lean_object* v___x_1153_; lean_object* v_q_1155_; 
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_nat_sub(v___x_1147_, v___x_1150_);
v_kind_1152_ = lean_array_fget(v_kinds_1141_, v___x_1151_);
lean_dec(v___x_1151_);
v___x_1153_ = lean_array_pop(v_kinds_1141_);
lean_inc_ref(v_objectFieldKeys_1143_);
lean_inc_ref(v_values_1142_);
lean_inc_ref(v___x_1153_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1153_);
v_q_1155_ = v___x_1145_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_values_1142_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_objectFieldKeys_1143_);
v_q_1155_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_unbox(v_kind_1152_);
lean_dec(v_kind_1152_);
switch(v___x_1156_)
{
case 0:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_value_1160_; lean_object* v___x_1161_; lean_object* v_q_1162_; lean_object* v___y_1164_; 
lean_dec_ref(v_q_1155_);
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_array_get_size(v_values_1142_);
v___x_1159_ = lean_nat_sub(v___x_1158_, v___x_1150_);
v_value_1160_ = lean_array_get(v___x_1157_, v_values_1142_, v___x_1159_);
lean_dec(v___x_1159_);
v___x_1161_ = lean_array_pop(v_values_1142_);
lean_inc_ref(v_objectFieldKeys_1143_);
lean_inc_ref(v___x_1161_);
lean_inc_ref(v___x_1153_);
v_q_1162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1162_, 0, v___x_1153_);
lean_ctor_set(v_q_1162_, 1, v___x_1161_);
lean_ctor_set(v_q_1162_, 2, v_objectFieldKeys_1143_);
switch(lean_obj_tag(v_value_1160_))
{
case 0:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec_ref(v___x_1161_);
lean_dec_ref(v___x_1153_);
lean_dec_ref(v_objectFieldKeys_1143_);
v___x_1167_ = ((lean_object*)(l_Lean_Json_render___closed__0));
v___x_1168_ = lean_string_append(v_acc_1139_, v___x_1167_);
v_acc_1139_ = v___x_1168_;
v_q_1140_ = v_q_1162_;
goto _start;
}
case 1:
{
uint8_t v_b_1170_; 
lean_dec_ref(v___x_1161_);
lean_dec_ref(v___x_1153_);
lean_dec_ref(v_objectFieldKeys_1143_);
v_b_1170_ = lean_ctor_get_uint8(v_value_1160_, 0);
lean_dec_ref_known(v_value_1160_, 0);
if (v_b_1170_ == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = ((lean_object*)(l_Lean_Json_render___closed__2));
v___y_1164_ = v___x_1171_;
goto v___jp_1163_;
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = ((lean_object*)(l_Lean_Json_render___closed__4));
v___y_1164_ = v___x_1172_;
goto v___jp_1163_;
}
}
case 2:
{
lean_object* v_n_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec_ref(v___x_1161_);
lean_dec_ref(v___x_1153_);
lean_dec_ref(v_objectFieldKeys_1143_);
v_n_1173_ = lean_ctor_get(v_value_1160_, 0);
lean_inc_ref(v_n_1173_);
lean_dec_ref_known(v_value_1160_, 1);
v___x_1174_ = l_Lean_JsonNumber_toString(v_n_1173_);
v___x_1175_ = lean_string_append(v_acc_1139_, v___x_1174_);
lean_dec_ref(v___x_1174_);
v_acc_1139_ = v___x_1175_;
v_q_1140_ = v_q_1162_;
goto _start;
}
case 3:
{
lean_object* v_s_1177_; lean_object* v___x_1178_; lean_object* v_acc_1179_; uint8_t v___x_1180_; 
lean_dec_ref(v___x_1161_);
lean_dec_ref(v___x_1153_);
lean_dec_ref(v_objectFieldKeys_1143_);
v_s_1177_ = lean_ctor_get(v_value_1160_, 0);
lean_inc_ref(v_s_1177_);
lean_dec_ref_known(v_value_1160_, 1);
v___x_1178_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1179_ = lean_string_append(v_acc_1139_, v___x_1178_);
v___x_1180_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_1177_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_string_append(v_acc_1179_, v_s_1177_);
lean_dec_ref(v_s_1177_);
v___x_1182_ = lean_string_append(v___x_1181_, v___x_1178_);
v_acc_1139_ = v___x_1182_;
v_q_1140_ = v_q_1162_;
goto _start;
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1184_ = lean_string_utf8_byte_size(v_s_1177_);
lean_inc_ref(v_s_1177_);
v___x_1185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1185_, 0, v_s_1177_);
lean_ctor_set(v___x_1185_, 1, v___x_1148_);
lean_ctor_set(v___x_1185_, 2, v___x_1184_);
v___x_1186_ = l_String_Slice_positions(v___x_1185_);
v___x_1187_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1185_, v_s_1177_, v___x_1186_, v_acc_1179_);
lean_dec_ref(v_s_1177_);
lean_dec_ref_known(v___x_1185_, 3);
v___x_1188_ = lean_string_append(v___x_1187_, v___x_1178_);
v_acc_1139_ = v___x_1188_;
v_q_1140_ = v_q_1162_;
goto _start;
}
}
case 4:
{
lean_object* v_elems_1190_; uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_q_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
lean_dec_ref_known(v_q_1162_, 3);
v_elems_1190_ = lean_ctor_get(v_value_1160_, 0);
lean_inc_ref(v_elems_1190_);
lean_dec_ref_known(v_value_1160_, 1);
v___x_1191_ = 2;
v___x_1192_ = lean_box(v___x_1191_);
v___x_1193_ = lean_array_push(v___x_1153_, v___x_1192_);
v_q_1194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1194_, 0, v___x_1193_);
lean_ctor_set(v_q_1194_, 1, v___x_1161_);
lean_ctor_set(v_q_1194_, 2, v_objectFieldKeys_1143_);
v___x_1195_ = ((lean_object*)(l_Lean_Json_render___closed__9));
v___x_1196_ = lean_string_append(v_acc_1139_, v___x_1195_);
v___x_1197_ = lean_array_get_size(v_elems_1190_);
v___x_1198_ = lean_nat_dec_lt(v___x_1148_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_dec_ref(v_elems_1190_);
v_acc_1139_ = v___x_1196_;
v_q_1140_ = v_q_1194_;
goto _start;
}
else
{
size_t v___x_1200_; size_t v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_usize_of_nat(v___x_1197_);
v___x_1201_ = ((size_t)0ULL);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_elems_1190_, v___x_1200_, v___x_1201_, v_q_1194_);
lean_dec_ref(v_elems_1190_);
v_acc_1139_ = v___x_1196_;
v_q_1140_ = v___x_1202_;
goto _start;
}
}
default: 
{
lean_object* v_kvPairs_1204_; uint8_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_q_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec_ref_known(v_q_1162_, 3);
v_kvPairs_1204_ = lean_ctor_get(v_value_1160_, 0);
lean_inc(v_kvPairs_1204_);
lean_dec_ref_known(v_value_1160_, 1);
v___x_1205_ = 4;
v___x_1206_ = lean_box(v___x_1205_);
v___x_1207_ = lean_array_push(v___x_1153_, v___x_1206_);
v_q_1208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1208_, 0, v___x_1207_);
lean_ctor_set(v_q_1208_, 1, v___x_1161_);
lean_ctor_set(v_q_1208_, 2, v_objectFieldKeys_1143_);
v___x_1209_ = ((lean_object*)(l_Lean_Json_render___closed__15));
v___x_1210_ = lean_string_append(v_acc_1139_, v___x_1209_);
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_q_1208_, v_kvPairs_1204_);
v_acc_1139_ = v___x_1210_;
v_q_1140_ = v___x_1211_;
goto _start;
}
}
v___jp_1163_:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_string_append(v_acc_1139_, v___y_1164_);
v_acc_1139_ = v___x_1165_;
v_q_1140_ = v_q_1162_;
goto _start;
}
}
case 1:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_value_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
lean_dec_ref(v_q_1155_);
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_array_get_size(v_values_1142_);
v___x_1215_ = lean_nat_sub(v___x_1214_, v___x_1150_);
v_value_1216_ = lean_array_get(v___x_1213_, v_values_1142_, v___x_1215_);
lean_dec(v___x_1215_);
v___x_1217_ = lean_array_get_size(v___x_1153_);
v___x_1218_ = lean_nat_dec_eq(v___x_1217_, v___x_1148_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_kind_1221_; uint8_t v___x_1222_; 
v___x_1219_ = lean_array_pop(v_values_1142_);
v___x_1220_ = lean_nat_sub(v___x_1217_, v___x_1150_);
v_kind_1221_ = lean_array_fget(v___x_1153_, v___x_1220_);
lean_dec(v___x_1220_);
v___x_1222_ = lean_unbox(v_kind_1221_);
lean_dec(v_kind_1221_);
if (v___x_1222_ == 2)
{
uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1223_ = 0;
v___x_1224_ = lean_box(v___x_1223_);
v___x_1225_ = lean_array_push(v___x_1153_, v___x_1224_);
v___x_1226_ = lean_array_push(v___x_1219_, v_value_1216_);
v___x_1227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
lean_ctor_set(v___x_1227_, 2, v_objectFieldKeys_1143_);
v_q_1140_ = v___x_1227_;
goto _start;
}
else
{
uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1229_ = 5;
v___x_1230_ = lean_box(v___x_1229_);
v___x_1231_ = lean_array_push(v___x_1153_, v___x_1230_);
v___x_1232_ = 0;
v___x_1233_ = lean_box(v___x_1232_);
v___x_1234_ = lean_array_push(v___x_1231_, v___x_1233_);
v___x_1235_ = lean_array_push(v___x_1219_, v_value_1216_);
v___x_1236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
lean_ctor_set(v___x_1236_, 2, v_objectFieldKeys_1143_);
v_q_1140_ = v___x_1236_;
goto _start;
}
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec_ref(v___x_1153_);
lean_dec_ref(v_objectFieldKeys_1143_);
lean_dec_ref(v_values_1142_);
v___x_1238_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0));
v___x_1239_ = lean_mk_empty_array_with_capacity(v___x_1150_);
v___x_1240_ = lean_array_push(v___x_1239_, v_value_1216_);
v___x_1241_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1238_);
lean_ctor_set(v___x_1242_, 1, v___x_1240_);
lean_ctor_set(v___x_1242_, 2, v___x_1241_);
v_q_1140_ = v___x_1242_;
goto _start;
}
}
case 2:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v___x_1153_);
lean_dec_ref(v_objectFieldKeys_1143_);
lean_dec_ref(v_values_1142_);
v___x_1244_ = ((lean_object*)(l_Lean_Json_render___closed__10));
v___x_1245_ = lean_string_append(v_acc_1139_, v___x_1244_);
v_acc_1139_ = v___x_1245_;
v_q_1140_ = v_q_1155_;
goto _start;
}
case 3:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v_objectFieldKey_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_value_1254_; lean_object* v___y_1256_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
lean_dec_ref(v_q_1155_);
v___x_1247_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1248_ = lean_array_get_size(v_objectFieldKeys_1143_);
v___x_1249_ = lean_nat_sub(v___x_1248_, v___x_1150_);
v_objectFieldKey_1250_ = lean_array_get(v___x_1247_, v_objectFieldKeys_1143_, v___x_1249_);
lean_dec(v___x_1249_);
v___x_1251_ = lean_box(0);
v___x_1252_ = lean_array_get_size(v_values_1142_);
v___x_1253_ = lean_nat_sub(v___x_1252_, v___x_1150_);
v_value_1254_ = lean_array_get(v___x_1251_, v_values_1142_, v___x_1253_);
lean_dec(v___x_1253_);
v___x_1265_ = lean_array_get_size(v___x_1153_);
v___x_1266_ = lean_nat_dec_eq(v___x_1265_, v___x_1148_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___y_1270_; lean_object* v___y_1283_; lean_object* v___x_1292_; lean_object* v_kind_1293_; uint8_t v___x_1294_; 
v___x_1267_ = lean_array_pop(v_objectFieldKeys_1143_);
v___x_1268_ = lean_array_pop(v_values_1142_);
v___x_1292_ = lean_nat_sub(v___x_1265_, v___x_1150_);
v_kind_1293_ = lean_array_fget(v___x_1153_, v___x_1292_);
lean_dec(v___x_1292_);
v___x_1294_ = lean_unbox(v_kind_1293_);
lean_dec(v_kind_1293_);
if (v___x_1294_ == 4)
{
lean_object* v___x_1295_; lean_object* v_acc_1296_; uint8_t v___x_1297_; 
v___x_1295_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1296_ = lean_string_append(v_acc_1139_, v___x_1295_);
v___x_1297_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1250_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_string_append(v_acc_1296_, v_objectFieldKey_1250_);
lean_dec(v_objectFieldKey_1250_);
v___x_1299_ = lean_string_append(v___x_1298_, v___x_1295_);
v___y_1283_ = v___x_1299_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1300_ = lean_string_utf8_byte_size(v_objectFieldKey_1250_);
lean_inc(v_objectFieldKey_1250_);
v___x_1301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1301_, 0, v_objectFieldKey_1250_);
lean_ctor_set(v___x_1301_, 1, v___x_1148_);
lean_ctor_set(v___x_1301_, 2, v___x_1300_);
v___x_1302_ = l_String_Slice_positions(v___x_1301_);
v___x_1303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1301_, v_objectFieldKey_1250_, v___x_1302_, v_acc_1296_);
lean_dec(v_objectFieldKey_1250_);
lean_dec_ref_known(v___x_1301_, 3);
v___x_1304_ = lean_string_append(v___x_1303_, v___x_1295_);
v___y_1283_ = v___x_1304_;
goto v___jp_1282_;
}
}
else
{
lean_object* v___x_1305_; lean_object* v_acc_1306_; uint8_t v___x_1307_; 
v___x_1305_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1306_ = lean_string_append(v_acc_1139_, v___x_1305_);
v___x_1307_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1250_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_string_append(v_acc_1306_, v_objectFieldKey_1250_);
lean_dec(v_objectFieldKey_1250_);
v___x_1309_ = lean_string_append(v___x_1308_, v___x_1305_);
v___y_1270_ = v___x_1309_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1310_ = lean_string_utf8_byte_size(v_objectFieldKey_1250_);
lean_inc(v_objectFieldKey_1250_);
v___x_1311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1311_, 0, v_objectFieldKey_1250_);
lean_ctor_set(v___x_1311_, 1, v___x_1148_);
lean_ctor_set(v___x_1311_, 2, v___x_1310_);
v___x_1312_ = l_String_Slice_positions(v___x_1311_);
v___x_1313_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1311_, v_objectFieldKey_1250_, v___x_1312_, v_acc_1306_);
lean_dec(v_objectFieldKey_1250_);
lean_dec_ref_known(v___x_1311_, 3);
v___x_1314_ = lean_string_append(v___x_1313_, v___x_1305_);
v___y_1270_ = v___x_1314_;
goto v___jp_1269_;
}
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1271_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1272_ = lean_string_append(v___y_1270_, v___x_1271_);
v___x_1273_ = 5;
v___x_1274_ = lean_box(v___x_1273_);
v___x_1275_ = lean_array_push(v___x_1153_, v___x_1274_);
v___x_1276_ = 0;
v___x_1277_ = lean_box(v___x_1276_);
v___x_1278_ = lean_array_push(v___x_1275_, v___x_1277_);
v___x_1279_ = lean_array_push(v___x_1268_, v_value_1254_);
v___x_1280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
lean_ctor_set(v___x_1280_, 2, v___x_1267_);
v_acc_1139_ = v___x_1272_;
v_q_1140_ = v___x_1280_;
goto _start;
}
v___jp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1284_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1285_ = lean_string_append(v___y_1283_, v___x_1284_);
v___x_1286_ = 0;
v___x_1287_ = lean_box(v___x_1286_);
v___x_1288_ = lean_array_push(v___x_1153_, v___x_1287_);
v___x_1289_ = lean_array_push(v___x_1268_, v_value_1254_);
v___x_1290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
lean_ctor_set(v___x_1290_, 2, v___x_1267_);
v_acc_1139_ = v___x_1285_;
v_q_1140_ = v___x_1290_;
goto _start;
}
}
else
{
lean_object* v___x_1315_; lean_object* v_acc_1316_; uint8_t v___x_1317_; 
lean_dec_ref(v___x_1153_);
lean_dec_ref(v_objectFieldKeys_1143_);
lean_dec_ref(v_values_1142_);
v___x_1315_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1316_ = lean_string_append(v_acc_1139_, v___x_1315_);
v___x_1317_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1250_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_string_append(v_acc_1316_, v_objectFieldKey_1250_);
lean_dec(v_objectFieldKey_1250_);
v___x_1319_ = lean_string_append(v___x_1318_, v___x_1315_);
v___y_1256_ = v___x_1319_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1320_ = lean_string_utf8_byte_size(v_objectFieldKey_1250_);
lean_inc(v_objectFieldKey_1250_);
v___x_1321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1321_, 0, v_objectFieldKey_1250_);
lean_ctor_set(v___x_1321_, 1, v___x_1148_);
lean_ctor_set(v___x_1321_, 2, v___x_1320_);
v___x_1322_ = l_String_Slice_positions(v___x_1321_);
v___x_1323_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1321_, v_objectFieldKey_1250_, v___x_1322_, v_acc_1316_);
lean_dec(v_objectFieldKey_1250_);
lean_dec_ref_known(v___x_1321_, 3);
v___x_1324_ = lean_string_append(v___x_1323_, v___x_1315_);
v___y_1256_ = v___x_1324_;
goto v___jp_1255_;
}
}
v___jp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1257_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1258_ = lean_string_append(v___y_1256_, v___x_1257_);
v___x_1259_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0));
v___x_1260_ = lean_mk_empty_array_with_capacity(v___x_1150_);
v___x_1261_ = lean_array_push(v___x_1260_, v_value_1254_);
v___x_1262_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1259_);
lean_ctor_set(v___x_1263_, 1, v___x_1261_);
lean_ctor_set(v___x_1263_, 2, v___x_1262_);
v_acc_1139_ = v___x_1258_;
v_q_1140_ = v___x_1263_;
goto _start;
}
}
case 4:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec_ref(v___x_1153_);
lean_dec_ref(v_objectFieldKeys_1143_);
lean_dec_ref(v_values_1142_);
v___x_1325_ = ((lean_object*)(l_Lean_Json_render___closed__16));
v___x_1326_ = lean_string_append(v_acc_1139_, v___x_1325_);
v_acc_1139_ = v___x_1326_;
v_q_1140_ = v_q_1155_;
goto _start;
}
default: 
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v___x_1153_);
lean_dec_ref(v_objectFieldKeys_1143_);
lean_dec_ref(v_values_1142_);
v___x_1328_ = ((lean_object*)(l_Lean_Json_render___closed__6));
v___x_1329_ = lean_string_append(v_acc_1139_, v___x_1328_);
v_acc_1139_ = v___x_1329_;
v_q_1140_ = v_q_1155_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_1145_);
lean_dec_ref(v_objectFieldKeys_1143_);
lean_dec_ref(v_values_1142_);
lean_dec_ref(v_kinds_1141_);
return v_acc_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_compress(lean_object* v_j_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1340_ = lean_unsigned_to_nat(1u);
v___x_1341_ = lean_mk_empty_array_with_capacity(v___x_1340_);
v___x_1342_ = ((lean_object*)(l_Lean_Json_compress___closed__0));
v___x_1343_ = lean_array_push(v___x_1341_, v_j_1338_);
v___x_1344_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1342_);
lean_ctor_set(v___x_1345_, 1, v___x_1343_);
lean_ctor_set(v___x_1345_, 2, v___x_1344_);
v___x_1346_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(v___x_1339_, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instToString___lam__0(lean_object* v_j_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_unsigned_to_nat(80u);
v___x_1351_ = l_Lean_Json_pretty(v_j_1349_, v___x_1350_);
return v___x_1351_;
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
