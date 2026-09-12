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
uint8_t v___y_527_; uint32_t v___x_552_; uint8_t v___x_553_; 
v___x_552_ = 34;
v___x_553_ = lean_uint32_dec_eq(v_c_525_, v___x_552_);
if (v___x_553_ == 0)
{
uint32_t v___x_554_; uint8_t v___x_555_; 
v___x_554_ = 92;
v___x_555_ = lean_uint32_dec_eq(v_c_525_, v___x_554_);
if (v___x_555_ == 0)
{
uint32_t v___x_556_; uint8_t v___x_557_; 
v___x_556_ = 10;
v___x_557_ = lean_uint32_dec_eq(v_c_525_, v___x_556_);
if (v___x_557_ == 0)
{
uint32_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 13;
v___x_559_ = lean_uint32_dec_eq(v_c_525_, v___x_558_);
if (v___x_559_ == 0)
{
uint32_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = 32;
v___x_561_ = lean_uint32_dec_le(v___x_560_, v_c_525_);
if (v___x_561_ == 0)
{
v___y_527_ = v___x_561_;
goto v___jp_526_;
}
else
{
uint32_t v___x_562_; uint8_t v___x_563_; 
v___x_562_ = 1114111;
v___x_563_ = lean_uint32_dec_le(v_c_525_, v___x_562_);
v___y_527_ = v___x_563_;
goto v___jp_526_;
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1));
v___x_565_ = lean_string_append(v_acc_524_, v___x_564_);
return v___x_565_;
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2));
v___x_567_ = lean_string_append(v_acc_524_, v___x_566_);
return v___x_567_;
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3));
v___x_569_ = lean_string_append(v_acc_524_, v___x_568_);
return v___x_569_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4));
v___x_571_ = lean_string_append(v_acc_524_, v___x_570_);
return v___x_571_;
}
v___jp_526_:
{
if (v___y_527_ == 0)
{
lean_object* v_n_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint32_t v_d1_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint32_t v_d2_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint32_t v_d3_542_; lean_object* v___x_543_; uint32_t v_d4_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_n_528_ = lean_uint32_to_nat(v_c_525_);
v___x_529_ = lean_unsigned_to_nat(4096u);
v___x_530_ = lean_unsigned_to_nat(12u);
v___x_531_ = lean_nat_shiftr(v_n_528_, v___x_530_);
v_d1_532_ = l_Nat_digitChar(v___x_531_);
lean_dec(v___x_531_);
v___x_533_ = lean_nat_mod(v_n_528_, v___x_529_);
v___x_534_ = lean_unsigned_to_nat(256u);
v___x_535_ = lean_unsigned_to_nat(8u);
v___x_536_ = lean_nat_shiftr(v___x_533_, v___x_535_);
lean_dec(v___x_533_);
v_d2_537_ = l_Nat_digitChar(v___x_536_);
lean_dec(v___x_536_);
v___x_538_ = lean_nat_mod(v_n_528_, v___x_534_);
v___x_539_ = lean_unsigned_to_nat(16u);
v___x_540_ = lean_unsigned_to_nat(4u);
v___x_541_ = lean_nat_shiftr(v___x_538_, v___x_540_);
lean_dec(v___x_538_);
v_d3_542_ = l_Nat_digitChar(v___x_541_);
lean_dec(v___x_541_);
v___x_543_ = lean_nat_mod(v_n_528_, v___x_539_);
lean_dec(v_n_528_);
v_d4_544_ = l_Nat_digitChar(v___x_543_);
lean_dec(v___x_543_);
v___x_545_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__0));
v___x_546_ = lean_string_append(v_acc_524_, v___x_545_);
v___x_547_ = lean_string_push(v___x_546_, v_d1_532_);
v___x_548_ = lean_string_push(v___x_547_, v_d2_537_);
v___x_549_ = lean_string_push(v___x_548_, v_d3_542_);
v___x_550_ = lean_string_push(v___x_549_, v_d4_544_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; 
v___x_551_ = lean_string_push(v_acc_524_, v_c_525_);
return v___x_551_;
}
}
}
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
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(lean_object* v_s_576_, lean_object* v_i_577_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go___boxed(lean_object* v_s_589_, lean_object* v_i_590_){
_start:
{
uint8_t v_res_591_; lean_object* v_r_592_; 
v_res_591_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(v_s_589_, v_i_590_);
lean_dec_ref(v_s_589_);
v_r_592_ = lean_box(v_res_591_);
return v_r_592_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(lean_object* v_s_593_){
_start:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(v_s_593_, v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape___boxed(lean_object* v_s_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_596_);
lean_dec_ref(v_s_596_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape___lam__0(lean_object* v___x_599_, lean_object* v_s_600_, lean_object* v_it_601_, lean_object* v_acc_602_, lean_object* v_hP_603_, lean_object* v_recur_604_){
_start:
{
uint8_t v_decide_605_; 
v_decide_605_ = lean_nat_dec_eq(v_it_601_, v___x_599_);
if (v_decide_605_ == 0)
{
uint32_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_606_ = lean_string_utf8_get_fast(v_s_600_, v_it_601_);
v___x_607_ = lean_string_utf8_next_fast(v_s_600_, v_it_601_);
v___x_608_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_602_, v___x_606_);
v___x_609_ = lean_apply_4(v_recur_604_, v___x_607_, v___x_608_, lean_box(0), lean_box(0));
return v___x_609_;
}
else
{
lean_dec_ref(v_recur_604_);
return v_acc_602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape___lam__0___boxed(lean_object* v___x_610_, lean_object* v_s_611_, lean_object* v_it_612_, lean_object* v_acc_613_, lean_object* v_hP_614_, lean_object* v_recur_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Json_escape___lam__0(v___x_610_, v_s_611_, v_it_612_, v_acc_613_, v_hP_614_, v_recur_615_);
lean_dec(v_it_612_);
lean_dec_ref(v_s_611_);
lean_dec(v___x_610_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object* v_s_617_, lean_object* v_acc_618_){
_start:
{
uint8_t v___x_619_; 
v___x_619_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_617_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
v___x_620_ = lean_string_append(v_acc_618_, v_s_617_);
lean_dec_ref(v_s_617_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_621_ = lean_string_utf8_byte_size(v_s_617_);
v___f_622_ = lean_alloc_closure((void*)(l_Lean_Json_escape___lam__0___boxed), 6, 2);
lean_closure_set(v___f_622_, 0, v___x_621_);
lean_closure_set(v___f_622_, 1, v_s_617_);
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_622_, v___x_623_, v_acc_618_, lean_box(0));
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object* v_s_626_, lean_object* v_acc_627_){
_start:
{
lean_object* v___x_628_; lean_object* v_acc_629_; uint8_t v___x_630_; 
v___x_628_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_629_ = lean_string_append(v_acc_627_, v___x_628_);
v___x_630_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_626_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_string_append(v_acc_629_, v_s_626_);
lean_dec_ref(v_s_626_);
v___x_632_ = lean_string_append(v___x_631_, v___x_628_);
return v___x_632_;
}
else
{
lean_object* v___x_633_; lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_633_ = lean_string_utf8_byte_size(v_s_626_);
v___f_634_ = lean_alloc_closure((void*)(l_Lean_Json_escape___lam__0___boxed), 6, 2);
lean_closure_set(v___f_634_, 0, v___x_633_);
lean_closure_set(v___f_634_, 1, v_s_626_);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_634_, v___x_635_, v_acc_629_, lean_box(0));
v___x_637_ = lean_string_append(v___x_636_, v___x_628_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Json_render_spec__3(lean_object* v_a_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = lean_nat_to_int(v_a_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(lean_object* v___x_640_, lean_object* v_k_641_, lean_object* v_a_642_, lean_object* v_b_643_){
_start:
{
uint8_t v_decide_644_; 
v_decide_644_ = lean_nat_dec_eq(v_a_642_, v___x_640_);
if (v_decide_644_ == 0)
{
uint32_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_string_utf8_get_fast(v_k_641_, v_a_642_);
v___x_646_ = lean_string_utf8_next_fast(v_k_641_, v_a_642_);
lean_dec(v_a_642_);
v___x_647_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_b_643_, v___x_645_);
v_a_642_ = v___x_646_;
v_b_643_ = v___x_647_;
goto _start;
}
else
{
lean_dec(v_a_642_);
return v_b_643_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg___boxed(lean_object* v___x_649_, lean_object* v_k_650_, lean_object* v_a_651_, lean_object* v_b_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_649_, v_k_650_, v_a_651_, v_b_652_);
lean_dec_ref(v_k_650_);
lean_dec(v___x_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Json_render_spec__2_spec__2(lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
if (lean_obj_tag(v_x_656_) == 0)
{
lean_dec(v_x_654_);
return v_x_655_;
}
else
{
lean_object* v_head_657_; lean_object* v_tail_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_667_; 
v_head_657_ = lean_ctor_get(v_x_656_, 0);
v_tail_658_ = lean_ctor_get(v_x_656_, 1);
v_isSharedCheck_667_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_667_ == 0)
{
v___x_660_ = v_x_656_;
v_isShared_661_ = v_isSharedCheck_667_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_tail_658_);
lean_inc(v_head_657_);
lean_dec(v_x_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_667_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
lean_inc(v_x_654_);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 5);
lean_ctor_set(v___x_660_, 1, v_x_654_);
lean_ctor_set(v___x_660_, 0, v_x_655_);
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_x_655_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_x_654_);
v___x_663_ = v_reuseFailAlloc_666_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; 
v___x_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v_head_657_);
v_x_655_ = v___x_664_;
v_x_656_ = v_tail_658_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_668_) == 0)
{
lean_object* v___x_670_; 
lean_dec(v_x_669_);
v___x_670_ = lean_box(0);
return v___x_670_;
}
else
{
lean_object* v_tail_671_; 
v_tail_671_ = lean_ctor_get(v_x_668_, 1);
if (lean_obj_tag(v_tail_671_) == 0)
{
lean_object* v_head_672_; 
lean_dec(v_x_669_);
v_head_672_ = lean_ctor_get(v_x_668_, 0);
lean_inc(v_head_672_);
lean_dec_ref_known(v_x_668_, 2);
return v_head_672_;
}
else
{
lean_object* v_head_673_; lean_object* v___x_674_; 
lean_inc(v_tail_671_);
v_head_673_ = lean_ctor_get(v_x_668_, 0);
lean_inc(v_head_673_);
lean_dec_ref_known(v_x_668_, 2);
v___x_674_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Json_render_spec__2_spec__2(v_x_669_, v_head_673_, v_tail_671_);
return v___x_674_;
}
}
}
}
static lean_object* _init_l_Lean_Json_render___closed__11(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_Json_render___closed__9));
v___x_692_ = lean_string_length(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Json_render___closed__12(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_obj_once(&l_Lean_Json_render___closed__11, &l_Lean_Json_render___closed__11_once, _init_l_Lean_Json_render___closed__11);
v___x_694_ = lean_nat_to_int(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(lean_object* v_init_703_, lean_object* v_x_704_){
_start:
{
if (lean_obj_tag(v_x_704_) == 0)
{
lean_object* v_k_705_; lean_object* v_v_706_; lean_object* v_l_707_; lean_object* v_r_708_; lean_object* v___x_709_; lean_object* v___y_711_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_k_705_ = lean_ctor_get(v_x_704_, 1);
lean_inc(v_k_705_);
v_v_706_ = lean_ctor_get(v_x_704_, 2);
lean_inc(v_v_706_);
v_l_707_ = lean_ctor_get(v_x_704_, 3);
lean_inc(v_l_707_);
v_r_708_ = lean_ctor_get(v_x_704_, 4);
lean_inc(v_r_708_);
lean_dec_ref_known(v_x_704_, 5);
v___x_709_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v_init_703_, v_l_707_);
v___x_723_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v___x_724_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_k_705_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_string_append(v___x_723_, v_k_705_);
lean_dec(v_k_705_);
v___x_726_ = lean_string_append(v___x_725_, v___x_723_);
v___y_711_ = v___x_726_;
goto v___jp_710_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = lean_string_utf8_byte_size(v_k_705_);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_727_, v_k_705_, v___x_728_, v___x_723_);
lean_dec(v_k_705_);
v___x_730_ = lean_string_append(v___x_729_, v___x_723_);
v___y_711_ = v___x_730_;
goto v___jp_710_;
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_712_, 0, v___y_711_);
v___x_713_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__1));
v___x_714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = lean_box(1);
v___x_716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = l_Lean_Json_render(v_v_706_);
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = 0;
v___x_720_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set_uint8(v___x_720_, sizeof(void*)*1, v___x_719_);
v___x_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___x_709_);
v_init_703_ = v___x_721_;
v_x_704_ = v_r_708_;
goto _start;
}
}
else
{
return v_init_703_;
}
}
}
static lean_object* _init_l_Lean_Json_render___closed__17(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = ((lean_object*)(l_Lean_Json_render___closed__15));
v___x_733_ = lean_string_length(v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_Json_render___closed__18(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_obj_once(&l_Lean_Json_render___closed__17, &l_Lean_Json_render___closed__17_once, _init_l_Lean_Json_render___closed__17);
v___x_735_ = lean_nat_to_int(v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_render(lean_object* v_x_741_){
_start:
{
switch(lean_obj_tag(v_x_741_))
{
case 0:
{
lean_object* v___x_742_; 
v___x_742_ = ((lean_object*)(l_Lean_Json_render___closed__1));
return v___x_742_;
}
case 1:
{
uint8_t v_b_743_; 
v_b_743_ = lean_ctor_get_uint8(v_x_741_, 0);
lean_dec_ref_known(v_x_741_, 0);
if (v_b_743_ == 0)
{
lean_object* v___x_744_; 
v___x_744_ = ((lean_object*)(l_Lean_Json_render___closed__3));
return v___x_744_;
}
else
{
lean_object* v___x_745_; 
v___x_745_ = ((lean_object*)(l_Lean_Json_render___closed__5));
return v___x_745_;
}
}
case 2:
{
lean_object* v_n_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_n_746_ = lean_ctor_get(v_x_741_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_754_ == 0)
{
v___x_748_ = v_x_741_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_n_746_);
lean_dec(v_x_741_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = l_Lean_JsonNumber_toString(v_n_746_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 3);
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
case 3:
{
lean_object* v_s_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_773_; 
v_s_755_ = lean_ctor_get(v_x_741_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_773_ == 0)
{
v___x_757_ = v_x_741_;
v_isShared_758_ = v_isSharedCheck_773_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_s_755_);
lean_dec(v_x_741_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_773_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v___x_760_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_755_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_761_ = lean_string_append(v___x_759_, v_s_755_);
lean_dec_ref(v_s_755_);
v___x_762_ = lean_string_append(v___x_761_, v___x_759_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_762_);
v___x_764_ = v___x_757_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_766_ = lean_string_utf8_byte_size(v_s_755_);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_766_, v_s_755_, v___x_767_, v___x_759_);
lean_dec_ref(v_s_755_);
v___x_769_ = lean_string_append(v___x_768_, v___x_759_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_769_);
v___x_771_ = v___x_757_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
case 4:
{
lean_object* v_elems_774_; size_t v_sz_775_; size_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_elems_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; lean_object* v___x_788_; 
v_elems_774_ = lean_ctor_get(v_x_741_, 0);
lean_inc_ref(v_elems_774_);
lean_dec_ref_known(v_x_741_, 1);
v_sz_775_ = lean_array_size(v_elems_774_);
v___x_776_ = ((size_t)0ULL);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(v_sz_775_, v___x_776_, v_elems_774_);
v___x_778_ = lean_array_to_list(v___x_777_);
v___x_779_ = ((lean_object*)(l_Lean_Json_render___closed__8));
v_elems_780_ = l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(v___x_778_, v___x_779_);
v___x_781_ = lean_obj_once(&l_Lean_Json_render___closed__12, &l_Lean_Json_render___closed__12_once, _init_l_Lean_Json_render___closed__12);
v___x_782_ = ((lean_object*)(l_Lean_Json_render___closed__13));
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_elems_780_);
v___x_784_ = ((lean_object*)(l_Lean_Json_render___closed__14));
v___x_785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_781_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = 0;
v___x_788_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*1, v___x_787_);
return v___x_788_;
}
default: 
{
lean_object* v_kvPairs_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_kvs_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; 
v_kvPairs_789_ = lean_ctor_get(v_x_741_, 0);
lean_inc(v_kvPairs_789_);
lean_dec_ref_known(v_x_741_, 1);
v___x_790_ = lean_box(0);
v___x_791_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v___x_790_, v_kvPairs_789_);
v___x_792_ = ((lean_object*)(l_Lean_Json_render___closed__8));
v_kvs_793_ = l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(v___x_791_, v___x_792_);
v___x_794_ = lean_obj_once(&l_Lean_Json_render___closed__18, &l_Lean_Json_render___closed__18_once, _init_l_Lean_Json_render___closed__18);
v___x_795_ = ((lean_object*)(l_Lean_Json_render___closed__19));
v___x_796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v_kvs_793_);
v___x_797_ = ((lean_object*)(l_Lean_Json_render___closed__20));
v___x_798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_794_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = 0;
v___x_801_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*1, v___x_800_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(size_t v_sz_802_, size_t v_i_803_, lean_object* v_bs_804_){
_start:
{
uint8_t v___x_805_; 
v___x_805_ = lean_usize_dec_lt(v_i_803_, v_sz_802_);
if (v___x_805_ == 0)
{
return v_bs_804_;
}
else
{
lean_object* v_v_806_; lean_object* v___x_807_; lean_object* v_bs_x27_808_; lean_object* v___x_809_; size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
v_v_806_ = lean_array_uget(v_bs_804_, v_i_803_);
v___x_807_ = lean_unsigned_to_nat(0u);
v_bs_x27_808_ = lean_array_uset(v_bs_804_, v_i_803_, v___x_807_);
v___x_809_ = l_Lean_Json_render(v_v_806_);
v___x_810_ = ((size_t)1ULL);
v___x_811_ = lean_usize_add(v_i_803_, v___x_810_);
v___x_812_ = lean_array_uset(v_bs_x27_808_, v_i_803_, v___x_809_);
v_i_803_ = v___x_811_;
v_bs_804_ = v___x_812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1___boxed(lean_object* v_sz_814_, lean_object* v_i_815_, lean_object* v_bs_816_){
_start:
{
size_t v_sz_boxed_817_; size_t v_i_boxed_818_; lean_object* v_res_819_; 
v_sz_boxed_817_ = lean_unbox_usize(v_sz_814_);
lean_dec(v_sz_814_);
v_i_boxed_818_ = lean_unbox_usize(v_i_815_);
lean_dec(v_i_815_);
v_res_819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(v_sz_boxed_817_, v_i_boxed_818_, v_bs_816_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(lean_object* v___x_820_, lean_object* v___x_821_, lean_object* v_k_822_, lean_object* v_inst_823_, lean_object* v_R_824_, lean_object* v_a_825_, lean_object* v_b_826_, lean_object* v_c_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_821_, v_k_822_, v_a_825_, v_b_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___boxed(lean_object* v___x_829_, lean_object* v___x_830_, lean_object* v_k_831_, lean_object* v_inst_832_, lean_object* v_R_833_, lean_object* v_a_834_, lean_object* v_b_835_, lean_object* v_c_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(v___x_829_, v___x_830_, v_k_831_, v_inst_832_, v_R_833_, v_a_834_, v_b_835_, v_c_836_);
lean_dec_ref(v_k_831_);
lean_dec(v___x_830_);
lean_dec_ref(v___x_829_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4(lean_object* v_init_838_, lean_object* v_t_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v_init_838_, v_t_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_pretty(lean_object* v_j_841_, lean_object* v_lineWidth_842_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = l_Lean_Json_render(v_j_841_);
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = l_Std_Format_pretty(v___x_843_, v_lineWidth_842_, v___x_844_, v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_pretty___boxed(lean_object* v_j_846_, lean_object* v_lineWidth_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Json_pretty(v_j_846_, v_lineWidth_847_);
lean_dec(v_lineWidth_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx(uint8_t v_x_849_){
_start:
{
switch(v_x_849_)
{
case 0:
{
lean_object* v___x_850_; 
v___x_850_ = lean_unsigned_to_nat(0u);
return v___x_850_;
}
case 1:
{
lean_object* v___x_851_; 
v___x_851_ = lean_unsigned_to_nat(1u);
return v___x_851_;
}
case 2:
{
lean_object* v___x_852_; 
v___x_852_ = lean_unsigned_to_nat(2u);
return v___x_852_;
}
case 3:
{
lean_object* v___x_853_; 
v___x_853_ = lean_unsigned_to_nat(3u);
return v___x_853_;
}
case 4:
{
lean_object* v___x_854_; 
v___x_854_ = lean_unsigned_to_nat(4u);
return v___x_854_;
}
default: 
{
lean_object* v___x_855_; 
v___x_855_ = lean_unsigned_to_nat(5u);
return v___x_855_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___boxed(lean_object* v_x_856_){
_start:
{
uint8_t v_x_boxed_857_; lean_object* v_res_858_; 
v_x_boxed_857_ = lean_unbox(v_x_856_);
v_res_858_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx(v_x_boxed_857_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(lean_object* v_motive_862_, lean_object* v_ctorIdx_863_, uint8_t v_t_864_, lean_object* v_h_865_, lean_object* v_k_866_){
_start:
{
lean_inc(v_k_866_);
return v_k_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___boxed(lean_object* v_motive_867_, lean_object* v_ctorIdx_868_, lean_object* v_t_869_, lean_object* v_h_870_, lean_object* v_k_871_){
_start:
{
uint8_t v_t_boxed_872_; lean_object* v_res_873_; 
v_t_boxed_872_ = lean_unbox(v_t_869_);
v_res_873_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(v_motive_867_, v_ctorIdx_868_, v_t_boxed_872_, v_h_870_, v_k_871_);
lean_dec(v_k_871_);
lean_dec(v_ctorIdx_868_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(lean_object* v_json_874_){
_start:
{
lean_inc(v_json_874_);
return v_json_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg___boxed(lean_object* v_json_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(v_json_875_);
lean_dec(v_json_875_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(lean_object* v_motive_877_, uint8_t v_t_878_, lean_object* v_h_879_, lean_object* v_json_880_){
_start:
{
lean_inc(v_json_880_);
return v_json_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___boxed(lean_object* v_motive_881_, lean_object* v_t_882_, lean_object* v_h_883_, lean_object* v_json_884_){
_start:
{
uint8_t v_t_boxed_885_; lean_object* v_res_886_; 
v_t_boxed_885_ = lean_unbox(v_t_882_);
v_res_886_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(v_motive_881_, v_t_boxed_885_, v_h_883_, v_json_884_);
lean_dec(v_json_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(lean_object* v_arrayElem_887_){
_start:
{
lean_inc(v_arrayElem_887_);
return v_arrayElem_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg___boxed(lean_object* v_arrayElem_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(v_arrayElem_888_);
lean_dec(v_arrayElem_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(lean_object* v_motive_890_, uint8_t v_t_891_, lean_object* v_h_892_, lean_object* v_arrayElem_893_){
_start:
{
lean_inc(v_arrayElem_893_);
return v_arrayElem_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___boxed(lean_object* v_motive_894_, lean_object* v_t_895_, lean_object* v_h_896_, lean_object* v_arrayElem_897_){
_start:
{
uint8_t v_t_boxed_898_; lean_object* v_res_899_; 
v_t_boxed_898_ = lean_unbox(v_t_895_);
v_res_899_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(v_motive_894_, v_t_boxed_898_, v_h_896_, v_arrayElem_897_);
lean_dec(v_arrayElem_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(lean_object* v_arrayEnd_900_){
_start:
{
lean_inc(v_arrayEnd_900_);
return v_arrayEnd_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg___boxed(lean_object* v_arrayEnd_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(v_arrayEnd_901_);
lean_dec(v_arrayEnd_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(lean_object* v_motive_903_, uint8_t v_t_904_, lean_object* v_h_905_, lean_object* v_arrayEnd_906_){
_start:
{
lean_inc(v_arrayEnd_906_);
return v_arrayEnd_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___boxed(lean_object* v_motive_907_, lean_object* v_t_908_, lean_object* v_h_909_, lean_object* v_arrayEnd_910_){
_start:
{
uint8_t v_t_boxed_911_; lean_object* v_res_912_; 
v_t_boxed_911_ = lean_unbox(v_t_908_);
v_res_912_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(v_motive_907_, v_t_boxed_911_, v_h_909_, v_arrayEnd_910_);
lean_dec(v_arrayEnd_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(lean_object* v_objectField_913_){
_start:
{
lean_inc(v_objectField_913_);
return v_objectField_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg___boxed(lean_object* v_objectField_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(v_objectField_914_);
lean_dec(v_objectField_914_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(lean_object* v_motive_916_, uint8_t v_t_917_, lean_object* v_h_918_, lean_object* v_objectField_919_){
_start:
{
lean_inc(v_objectField_919_);
return v_objectField_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___boxed(lean_object* v_motive_920_, lean_object* v_t_921_, lean_object* v_h_922_, lean_object* v_objectField_923_){
_start:
{
uint8_t v_t_boxed_924_; lean_object* v_res_925_; 
v_t_boxed_924_ = lean_unbox(v_t_921_);
v_res_925_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(v_motive_920_, v_t_boxed_924_, v_h_922_, v_objectField_923_);
lean_dec(v_objectField_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(lean_object* v_objectEnd_926_){
_start:
{
lean_inc(v_objectEnd_926_);
return v_objectEnd_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg___boxed(lean_object* v_objectEnd_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(v_objectEnd_927_);
lean_dec(v_objectEnd_927_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(lean_object* v_motive_929_, uint8_t v_t_930_, lean_object* v_h_931_, lean_object* v_objectEnd_932_){
_start:
{
lean_inc(v_objectEnd_932_);
return v_objectEnd_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___boxed(lean_object* v_motive_933_, lean_object* v_t_934_, lean_object* v_h_935_, lean_object* v_objectEnd_936_){
_start:
{
uint8_t v_t_boxed_937_; lean_object* v_res_938_; 
v_t_boxed_937_ = lean_unbox(v_t_934_);
v_res_938_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(v_motive_933_, v_t_boxed_937_, v_h_935_, v_objectEnd_936_);
lean_dec(v_objectEnd_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(lean_object* v_comma_939_){
_start:
{
lean_inc(v_comma_939_);
return v_comma_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg___boxed(lean_object* v_comma_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(v_comma_940_);
lean_dec(v_comma_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(lean_object* v_motive_942_, uint8_t v_t_943_, lean_object* v_h_944_, lean_object* v_comma_945_){
_start:
{
lean_inc(v_comma_945_);
return v_comma_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___boxed(lean_object* v_motive_946_, lean_object* v_t_947_, lean_object* v_h_948_, lean_object* v_comma_949_){
_start:
{
uint8_t v_t_boxed_950_; lean_object* v_res_951_; 
v_t_boxed_950_ = lean_unbox(v_t_947_);
v_res_951_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(v_motive_946_, v_t_boxed_950_, v_h_948_, v_comma_949_);
lean_dec(v_comma_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(lean_object* v_q_952_, uint8_t v_kind_953_){
_start:
{
lean_object* v_kinds_954_; lean_object* v_values_955_; lean_object* v_objectFieldKeys_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
v_kinds_954_ = lean_ctor_get(v_q_952_, 0);
v_values_955_ = lean_ctor_get(v_q_952_, 1);
v_objectFieldKeys_956_ = lean_ctor_get(v_q_952_, 2);
v_isSharedCheck_965_ = !lean_is_exclusive(v_q_952_);
if (v_isSharedCheck_965_ == 0)
{
v___x_958_ = v_q_952_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_objectFieldKeys_956_);
lean_inc(v_values_955_);
lean_inc(v_kinds_954_);
lean_dec(v_q_952_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = lean_box(v_kind_953_);
v___x_961_ = lean_array_push(v_kinds_954_, v___x_960_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_values_955_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_objectFieldKeys_956_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind___boxed(lean_object* v_q_966_, lean_object* v_kind_967_){
_start:
{
uint8_t v_kind_boxed_968_; lean_object* v_res_969_; 
v_kind_boxed_968_ = lean_unbox(v_kind_967_);
v_res_969_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(v_q_966_, v_kind_boxed_968_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushValue(lean_object* v_q_970_, lean_object* v_value_971_){
_start:
{
lean_object* v_kinds_972_; lean_object* v_values_973_; lean_object* v_objectFieldKeys_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_982_; 
v_kinds_972_ = lean_ctor_get(v_q_970_, 0);
v_values_973_ = lean_ctor_get(v_q_970_, 1);
v_objectFieldKeys_974_ = lean_ctor_get(v_q_970_, 2);
v_isSharedCheck_982_ = !lean_is_exclusive(v_q_970_);
if (v_isSharedCheck_982_ == 0)
{
v___x_976_ = v_q_970_;
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_objectFieldKeys_974_);
lean_inc(v_values_973_);
lean_inc(v_kinds_972_);
lean_dec(v_q_970_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_array_push(v_values_973_, v_value_971_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_kinds_972_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_objectFieldKeys_974_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushObjectFieldKey(lean_object* v_q_983_, lean_object* v_objectFieldKey_984_){
_start:
{
lean_object* v_kinds_985_; lean_object* v_values_986_; lean_object* v_objectFieldKeys_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_995_; 
v_kinds_985_ = lean_ctor_get(v_q_983_, 0);
v_values_986_ = lean_ctor_get(v_q_983_, 1);
v_objectFieldKeys_987_ = lean_ctor_get(v_q_983_, 2);
v_isSharedCheck_995_ = !lean_is_exclusive(v_q_983_);
if (v_isSharedCheck_995_ == 0)
{
v___x_989_ = v_q_983_;
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_objectFieldKeys_987_);
lean_inc(v_values_986_);
lean_inc(v_kinds_985_);
lean_dec(v_q_983_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_array_push(v_objectFieldKeys_987_, v_objectFieldKey_984_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 2, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_kinds_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_values_986_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind___redArg(lean_object* v_q_996_){
_start:
{
lean_object* v_kinds_997_; lean_object* v_values_998_; lean_object* v_objectFieldKeys_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1012_; 
v_kinds_997_ = lean_ctor_get(v_q_996_, 0);
v_values_998_ = lean_ctor_get(v_q_996_, 1);
v_objectFieldKeys_999_ = lean_ctor_get(v_q_996_, 2);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_q_996_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1001_ = v_q_996_;
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_objectFieldKeys_999_);
lean_inc(v_values_998_);
lean_inc(v_kinds_997_);
lean_dec(v_q_996_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_kind_1006_; lean_object* v___x_1007_; lean_object* v_q_1009_; 
v___x_1003_ = lean_array_get_size(v_kinds_997_);
v___x_1004_ = lean_unsigned_to_nat(1u);
v___x_1005_ = lean_nat_sub(v___x_1003_, v___x_1004_);
v_kind_1006_ = lean_array_fget(v_kinds_997_, v___x_1005_);
lean_dec(v___x_1005_);
v___x_1007_ = lean_array_pop(v_kinds_997_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1007_);
v_q_1009_ = v___x_1001_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_values_998_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_objectFieldKeys_999_);
v_q_1009_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_kind_1006_);
lean_ctor_set(v___x_1010_, 1, v_q_1009_);
return v___x_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind(lean_object* v_q_1013_, lean_object* v_h_1014_){
_start:
{
lean_object* v_kinds_1015_; lean_object* v_values_1016_; lean_object* v_objectFieldKeys_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1030_; 
v_kinds_1015_ = lean_ctor_get(v_q_1013_, 0);
v_values_1016_ = lean_ctor_get(v_q_1013_, 1);
v_objectFieldKeys_1017_ = lean_ctor_get(v_q_1013_, 2);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_q_1013_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1019_ = v_q_1013_;
v_isShared_1020_ = v_isSharedCheck_1030_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_objectFieldKeys_1017_);
lean_inc(v_values_1016_);
lean_inc(v_kinds_1015_);
lean_dec(v_q_1013_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1030_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_kind_1024_; lean_object* v___x_1025_; lean_object* v_q_1027_; 
v___x_1021_ = lean_array_get_size(v_kinds_1015_);
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1023_ = lean_nat_sub(v___x_1021_, v___x_1022_);
v_kind_1024_ = lean_array_fget(v_kinds_1015_, v___x_1023_);
lean_dec(v___x_1023_);
v___x_1025_ = lean_array_pop(v_kinds_1015_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1025_);
v_q_1027_ = v___x_1019_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_values_1016_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_objectFieldKeys_1017_);
v_q_1027_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_kind_1024_);
lean_ctor_set(v___x_1028_, 1, v_q_1027_);
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popValue_x21(lean_object* v_q_1031_){
_start:
{
lean_object* v_kinds_1032_; lean_object* v_values_1033_; lean_object* v_objectFieldKeys_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1048_; 
v_kinds_1032_ = lean_ctor_get(v_q_1031_, 0);
v_values_1033_ = lean_ctor_get(v_q_1031_, 1);
v_objectFieldKeys_1034_ = lean_ctor_get(v_q_1031_, 2);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_q_1031_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1036_ = v_q_1031_;
v_isShared_1037_ = v_isSharedCheck_1048_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_objectFieldKeys_1034_);
lean_inc(v_values_1033_);
lean_inc(v_kinds_1032_);
lean_dec(v_q_1031_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1048_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_value_1042_; lean_object* v___x_1043_; lean_object* v_q_1045_; 
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_array_get_size(v_values_1033_);
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = lean_nat_sub(v___x_1039_, v___x_1040_);
v_value_1042_ = lean_array_get(v___x_1038_, v_values_1033_, v___x_1041_);
lean_dec(v___x_1041_);
v___x_1043_ = lean_array_pop(v_values_1033_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1043_);
v_q_1045_ = v___x_1036_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_kinds_1032_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_objectFieldKeys_1034_);
v_q_1045_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_value_1042_);
lean_ctor_set(v___x_1046_, 1, v_q_1045_);
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21(lean_object* v_q_1050_){
_start:
{
lean_object* v_kinds_1051_; lean_object* v_values_1052_; lean_object* v_objectFieldKeys_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1067_; 
v_kinds_1051_ = lean_ctor_get(v_q_1050_, 0);
v_values_1052_ = lean_ctor_get(v_q_1050_, 1);
v_objectFieldKeys_1053_ = lean_ctor_get(v_q_1050_, 2);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_q_1050_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1055_ = v_q_1050_;
v_isShared_1056_ = v_isSharedCheck_1067_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_objectFieldKeys_1053_);
lean_inc(v_values_1052_);
lean_inc(v_kinds_1051_);
lean_dec(v_q_1050_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1067_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v_objectFieldKey_1061_; lean_object* v___x_1062_; lean_object* v_q_1064_; 
v___x_1057_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1058_ = lean_array_get_size(v_objectFieldKeys_1053_);
v___x_1059_ = lean_unsigned_to_nat(1u);
v___x_1060_ = lean_nat_sub(v___x_1058_, v___x_1059_);
v_objectFieldKey_1061_ = lean_array_get(v___x_1057_, v_objectFieldKeys_1053_, v___x_1060_);
lean_dec(v___x_1060_);
v___x_1062_ = lean_array_pop(v_objectFieldKeys_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 2, v___x_1062_);
v_q_1064_ = v___x_1055_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_kinds_1051_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_values_1052_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v___x_1062_);
v_q_1064_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_objectFieldKey_1061_);
lean_ctor_set(v___x_1065_, 1, v_q_1064_);
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(lean_object* v_as_1068_, size_t v_i_1069_, size_t v_stop_1070_, lean_object* v_b_1071_){
_start:
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_usize_dec_eq(v_i_1069_, v_stop_1070_);
if (v___x_1072_ == 0)
{
lean_object* v_kinds_1073_; lean_object* v_values_1074_; lean_object* v_objectFieldKeys_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1090_; 
v_kinds_1073_ = lean_ctor_get(v_b_1071_, 0);
v_values_1074_ = lean_ctor_get(v_b_1071_, 1);
v_objectFieldKeys_1075_ = lean_ctor_get(v_b_1071_, 2);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_b_1071_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1077_ = v_b_1071_;
v_isShared_1078_ = v_isSharedCheck_1090_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_objectFieldKeys_1075_);
lean_inc(v_values_1074_);
lean_inc(v_kinds_1073_);
lean_dec(v_b_1071_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1090_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1079_ = ((size_t)1ULL);
v___x_1080_ = lean_usize_sub(v_i_1069_, v___x_1079_);
v___x_1081_ = lean_array_uget_borrowed(v_as_1068_, v___x_1080_);
v___x_1082_ = 1;
v___x_1083_ = lean_box(v___x_1082_);
v___x_1084_ = lean_array_push(v_kinds_1073_, v___x_1083_);
lean_inc(v___x_1081_);
v___x_1085_ = lean_array_push(v_values_1074_, v___x_1081_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1085_);
lean_ctor_set(v___x_1077_, 0, v___x_1084_);
v___x_1087_ = v___x_1077_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_objectFieldKeys_1075_);
v___x_1087_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
v_i_1069_ = v___x_1080_;
v_b_1071_ = v___x_1087_;
goto _start;
}
}
}
else
{
return v_b_1071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0___boxed(lean_object* v_as_1091_, lean_object* v_i_1092_, lean_object* v_stop_1093_, lean_object* v_b_1094_){
_start:
{
size_t v_i_boxed_1095_; size_t v_stop_boxed_1096_; lean_object* v_res_1097_; 
v_i_boxed_1095_ = lean_unbox_usize(v_i_1092_);
lean_dec(v_i_1092_);
v_stop_boxed_1096_ = lean_unbox_usize(v_stop_1093_);
lean_dec(v_stop_1093_);
v_res_1097_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_as_1091_, v_i_boxed_1095_, v_stop_boxed_1096_, v_b_1094_);
lean_dec_ref(v_as_1091_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(lean_object* v_init_1098_, lean_object* v_x_1099_){
_start:
{
if (lean_obj_tag(v_x_1099_) == 0)
{
lean_object* v_k_1100_; lean_object* v_v_1101_; lean_object* v_l_1102_; lean_object* v_r_1103_; lean_object* v___x_1104_; lean_object* v_kinds_1105_; lean_object* v_values_1106_; lean_object* v_objectFieldKeys_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1120_; 
v_k_1100_ = lean_ctor_get(v_x_1099_, 1);
lean_inc(v_k_1100_);
v_v_1101_ = lean_ctor_get(v_x_1099_, 2);
lean_inc(v_v_1101_);
v_l_1102_ = lean_ctor_get(v_x_1099_, 3);
lean_inc(v_l_1102_);
v_r_1103_ = lean_ctor_get(v_x_1099_, 4);
lean_inc(v_r_1103_);
lean_dec_ref_known(v_x_1099_, 5);
v___x_1104_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_init_1098_, v_r_1103_);
v_kinds_1105_ = lean_ctor_get(v___x_1104_, 0);
v_values_1106_ = lean_ctor_get(v___x_1104_, 1);
v_objectFieldKeys_1107_ = lean_ctor_get(v___x_1104_, 2);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1109_ = v___x_1104_;
v_isShared_1110_ = v_isSharedCheck_1120_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_objectFieldKeys_1107_);
lean_inc(v_values_1106_);
lean_inc(v_kinds_1105_);
lean_dec(v___x_1104_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1120_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
uint8_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1111_ = 3;
v___x_1112_ = lean_box(v___x_1111_);
v___x_1113_ = lean_array_push(v_kinds_1105_, v___x_1112_);
v___x_1114_ = lean_array_push(v_objectFieldKeys_1107_, v_k_1100_);
v___x_1115_ = lean_array_push(v_values_1106_, v_v_1101_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 2, v___x_1114_);
lean_ctor_set(v___x_1109_, 1, v___x_1115_);
lean_ctor_set(v___x_1109_, 0, v___x_1113_);
v___x_1117_ = v___x_1109_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1119_, 2, v___x_1114_);
v___x_1117_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
v_init_1098_ = v___x_1117_;
v_x_1099_ = v_l_1102_;
goto _start;
}
}
}
else
{
return v_init_1098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(lean_object* v_acc_1131_, lean_object* v_q_1132_){
_start:
{
lean_object* v_kinds_1133_; lean_object* v_values_1134_; lean_object* v_objectFieldKeys_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1316_; 
v_kinds_1133_ = lean_ctor_get(v_q_1132_, 0);
v_values_1134_ = lean_ctor_get(v_q_1132_, 1);
v_objectFieldKeys_1135_ = lean_ctor_get(v_q_1132_, 2);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_q_1132_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1137_ = v_q_1132_;
v_isShared_1138_ = v_isSharedCheck_1316_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_objectFieldKeys_1135_);
lean_inc(v_values_1134_);
lean_inc(v_kinds_1133_);
lean_dec(v_q_1132_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1316_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1139_ = lean_array_get_size(v_kinds_1133_);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_nat_dec_eq(v___x_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_kind_1144_; lean_object* v___x_1145_; lean_object* v_q_1147_; 
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = lean_nat_sub(v___x_1139_, v___x_1142_);
v_kind_1144_ = lean_array_fget(v_kinds_1133_, v___x_1143_);
lean_dec(v___x_1143_);
v___x_1145_ = lean_array_pop(v_kinds_1133_);
lean_inc_ref(v_objectFieldKeys_1135_);
lean_inc_ref(v_values_1134_);
lean_inc_ref(v___x_1145_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1145_);
v_q_1147_ = v___x_1137_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_values_1134_);
lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_objectFieldKeys_1135_);
v_q_1147_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_unbox(v_kind_1144_);
lean_dec(v_kind_1144_);
switch(v___x_1148_)
{
case 0:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_value_1152_; lean_object* v___x_1153_; lean_object* v_q_1154_; lean_object* v___y_1156_; 
lean_dec_ref(v_q_1147_);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_array_get_size(v_values_1134_);
v___x_1151_ = lean_nat_sub(v___x_1150_, v___x_1142_);
v_value_1152_ = lean_array_get(v___x_1149_, v_values_1134_, v___x_1151_);
lean_dec(v___x_1151_);
v___x_1153_ = lean_array_pop(v_values_1134_);
lean_inc_ref(v_objectFieldKeys_1135_);
lean_inc_ref(v___x_1153_);
lean_inc_ref(v___x_1145_);
v_q_1154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1154_, 0, v___x_1145_);
lean_ctor_set(v_q_1154_, 1, v___x_1153_);
lean_ctor_set(v_q_1154_, 2, v_objectFieldKeys_1135_);
switch(lean_obj_tag(v_value_1152_))
{
case 0:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec_ref(v___x_1153_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v_objectFieldKeys_1135_);
v___x_1159_ = ((lean_object*)(l_Lean_Json_render___closed__0));
v___x_1160_ = lean_string_append(v_acc_1131_, v___x_1159_);
v_acc_1131_ = v___x_1160_;
v_q_1132_ = v_q_1154_;
goto _start;
}
case 1:
{
uint8_t v_b_1162_; 
lean_dec_ref(v___x_1153_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v_objectFieldKeys_1135_);
v_b_1162_ = lean_ctor_get_uint8(v_value_1152_, 0);
lean_dec_ref_known(v_value_1152_, 0);
if (v_b_1162_ == 0)
{
lean_object* v___x_1163_; 
v___x_1163_ = ((lean_object*)(l_Lean_Json_render___closed__2));
v___y_1156_ = v___x_1163_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1164_; 
v___x_1164_ = ((lean_object*)(l_Lean_Json_render___closed__4));
v___y_1156_ = v___x_1164_;
goto v___jp_1155_;
}
}
case 2:
{
lean_object* v_n_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec_ref(v___x_1153_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v_objectFieldKeys_1135_);
v_n_1165_ = lean_ctor_get(v_value_1152_, 0);
lean_inc_ref(v_n_1165_);
lean_dec_ref_known(v_value_1152_, 1);
v___x_1166_ = l_Lean_JsonNumber_toString(v_n_1165_);
v___x_1167_ = lean_string_append(v_acc_1131_, v___x_1166_);
lean_dec_ref(v___x_1166_);
v_acc_1131_ = v___x_1167_;
v_q_1132_ = v_q_1154_;
goto _start;
}
case 3:
{
lean_object* v_s_1169_; lean_object* v___x_1170_; lean_object* v_acc_1171_; uint8_t v___x_1172_; 
lean_dec_ref(v___x_1153_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v_objectFieldKeys_1135_);
v_s_1169_ = lean_ctor_get(v_value_1152_, 0);
lean_inc_ref(v_s_1169_);
lean_dec_ref_known(v_value_1152_, 1);
v___x_1170_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1171_ = lean_string_append(v_acc_1131_, v___x_1170_);
v___x_1172_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_1169_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_string_append(v_acc_1171_, v_s_1169_);
lean_dec_ref(v_s_1169_);
v___x_1174_ = lean_string_append(v___x_1173_, v___x_1170_);
v_acc_1131_ = v___x_1174_;
v_q_1132_ = v_q_1154_;
goto _start;
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = lean_string_utf8_byte_size(v_s_1169_);
v___x_1177_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1176_, v_s_1169_, v___x_1140_, v_acc_1171_);
lean_dec_ref(v_s_1169_);
v___x_1178_ = lean_string_append(v___x_1177_, v___x_1170_);
v_acc_1131_ = v___x_1178_;
v_q_1132_ = v_q_1154_;
goto _start;
}
}
case 4:
{
lean_object* v_elems_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_q_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
lean_dec_ref_known(v_q_1154_, 3);
v_elems_1180_ = lean_ctor_get(v_value_1152_, 0);
lean_inc_ref(v_elems_1180_);
lean_dec_ref_known(v_value_1152_, 1);
v___x_1181_ = 2;
v___x_1182_ = lean_box(v___x_1181_);
v___x_1183_ = lean_array_push(v___x_1145_, v___x_1182_);
v_q_1184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1184_, 0, v___x_1183_);
lean_ctor_set(v_q_1184_, 1, v___x_1153_);
lean_ctor_set(v_q_1184_, 2, v_objectFieldKeys_1135_);
v___x_1185_ = ((lean_object*)(l_Lean_Json_render___closed__9));
v___x_1186_ = lean_string_append(v_acc_1131_, v___x_1185_);
v___x_1187_ = lean_array_get_size(v_elems_1180_);
v___x_1188_ = lean_nat_dec_lt(v___x_1140_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_dec_ref(v_elems_1180_);
v_acc_1131_ = v___x_1186_;
v_q_1132_ = v_q_1184_;
goto _start;
}
else
{
size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_usize_of_nat(v___x_1187_);
v___x_1191_ = ((size_t)0ULL);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_elems_1180_, v___x_1190_, v___x_1191_, v_q_1184_);
lean_dec_ref(v_elems_1180_);
v_acc_1131_ = v___x_1186_;
v_q_1132_ = v___x_1192_;
goto _start;
}
}
default: 
{
lean_object* v_kvPairs_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v_q_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_dec_ref_known(v_q_1154_, 3);
v_kvPairs_1194_ = lean_ctor_get(v_value_1152_, 0);
lean_inc(v_kvPairs_1194_);
lean_dec_ref_known(v_value_1152_, 1);
v___x_1195_ = 4;
v___x_1196_ = lean_box(v___x_1195_);
v___x_1197_ = lean_array_push(v___x_1145_, v___x_1196_);
v_q_1198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1198_, 0, v___x_1197_);
lean_ctor_set(v_q_1198_, 1, v___x_1153_);
lean_ctor_set(v_q_1198_, 2, v_objectFieldKeys_1135_);
v___x_1199_ = ((lean_object*)(l_Lean_Json_render___closed__15));
v___x_1200_ = lean_string_append(v_acc_1131_, v___x_1199_);
v___x_1201_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_q_1198_, v_kvPairs_1194_);
v_acc_1131_ = v___x_1200_;
v_q_1132_ = v___x_1201_;
goto _start;
}
}
v___jp_1155_:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_string_append(v_acc_1131_, v___y_1156_);
v_acc_1131_ = v___x_1157_;
v_q_1132_ = v_q_1154_;
goto _start;
}
}
case 1:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_value_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
lean_dec_ref(v_q_1147_);
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_array_get_size(v_values_1134_);
v___x_1205_ = lean_nat_sub(v___x_1204_, v___x_1142_);
v_value_1206_ = lean_array_get(v___x_1203_, v_values_1134_, v___x_1205_);
lean_dec(v___x_1205_);
v___x_1207_ = lean_array_get_size(v___x_1145_);
v___x_1208_ = lean_nat_dec_eq(v___x_1207_, v___x_1140_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_kind_1211_; uint8_t v___x_1212_; 
v___x_1209_ = lean_array_pop(v_values_1134_);
v___x_1210_ = lean_nat_sub(v___x_1207_, v___x_1142_);
v_kind_1211_ = lean_array_fget(v___x_1145_, v___x_1210_);
lean_dec(v___x_1210_);
v___x_1212_ = lean_unbox(v_kind_1211_);
lean_dec(v_kind_1211_);
if (v___x_1212_ == 2)
{
uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1213_ = 0;
v___x_1214_ = lean_box(v___x_1213_);
v___x_1215_ = lean_array_push(v___x_1145_, v___x_1214_);
v___x_1216_ = lean_array_push(v___x_1209_, v_value_1206_);
v___x_1217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
lean_ctor_set(v___x_1217_, 2, v_objectFieldKeys_1135_);
v_q_1132_ = v___x_1217_;
goto _start;
}
else
{
uint8_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1219_ = 5;
v___x_1220_ = lean_box(v___x_1219_);
v___x_1221_ = lean_array_push(v___x_1145_, v___x_1220_);
v___x_1222_ = 0;
v___x_1223_ = lean_box(v___x_1222_);
v___x_1224_ = lean_array_push(v___x_1221_, v___x_1223_);
v___x_1225_ = lean_array_push(v___x_1209_, v_value_1206_);
v___x_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
lean_ctor_set(v___x_1226_, 2, v_objectFieldKeys_1135_);
v_q_1132_ = v___x_1226_;
goto _start;
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec_ref(v___x_1145_);
lean_dec_ref(v_objectFieldKeys_1135_);
lean_dec_ref(v_values_1134_);
v___x_1228_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0));
v___x_1229_ = lean_mk_empty_array_with_capacity(v___x_1142_);
v___x_1230_ = lean_array_push(v___x_1229_, v_value_1206_);
v___x_1231_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1228_);
lean_ctor_set(v___x_1232_, 1, v___x_1230_);
lean_ctor_set(v___x_1232_, 2, v___x_1231_);
v_q_1132_ = v___x_1232_;
goto _start;
}
}
case 2:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec_ref(v___x_1145_);
lean_dec_ref(v_objectFieldKeys_1135_);
lean_dec_ref(v_values_1134_);
v___x_1234_ = ((lean_object*)(l_Lean_Json_render___closed__10));
v___x_1235_ = lean_string_append(v_acc_1131_, v___x_1234_);
v_acc_1131_ = v___x_1235_;
v_q_1132_ = v_q_1147_;
goto _start;
}
case 3:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_objectFieldKey_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_value_1244_; lean_object* v___y_1246_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
lean_dec_ref(v_q_1147_);
v___x_1237_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1238_ = lean_array_get_size(v_objectFieldKeys_1135_);
v___x_1239_ = lean_nat_sub(v___x_1238_, v___x_1142_);
v_objectFieldKey_1240_ = lean_array_get(v___x_1237_, v_objectFieldKeys_1135_, v___x_1239_);
lean_dec(v___x_1239_);
v___x_1241_ = lean_box(0);
v___x_1242_ = lean_array_get_size(v_values_1134_);
v___x_1243_ = lean_nat_sub(v___x_1242_, v___x_1142_);
v_value_1244_ = lean_array_get(v___x_1241_, v_values_1134_, v___x_1243_);
lean_dec(v___x_1243_);
v___x_1255_ = lean_array_get_size(v___x_1145_);
v___x_1256_ = lean_nat_dec_eq(v___x_1255_, v___x_1140_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___y_1260_; lean_object* v___y_1273_; lean_object* v___x_1282_; lean_object* v_kind_1283_; uint8_t v___x_1284_; 
v___x_1257_ = lean_array_pop(v_objectFieldKeys_1135_);
v___x_1258_ = lean_array_pop(v_values_1134_);
v___x_1282_ = lean_nat_sub(v___x_1255_, v___x_1142_);
v_kind_1283_ = lean_array_fget(v___x_1145_, v___x_1282_);
lean_dec(v___x_1282_);
v___x_1284_ = lean_unbox(v_kind_1283_);
lean_dec(v_kind_1283_);
if (v___x_1284_ == 4)
{
lean_object* v___x_1285_; lean_object* v_acc_1286_; uint8_t v___x_1287_; 
v___x_1285_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1286_ = lean_string_append(v_acc_1131_, v___x_1285_);
v___x_1287_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1240_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_string_append(v_acc_1286_, v_objectFieldKey_1240_);
lean_dec(v_objectFieldKey_1240_);
v___x_1289_ = lean_string_append(v___x_1288_, v___x_1285_);
v___y_1273_ = v___x_1289_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_string_utf8_byte_size(v_objectFieldKey_1240_);
v___x_1291_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1290_, v_objectFieldKey_1240_, v___x_1140_, v_acc_1286_);
lean_dec(v_objectFieldKey_1240_);
v___x_1292_ = lean_string_append(v___x_1291_, v___x_1285_);
v___y_1273_ = v___x_1292_;
goto v___jp_1272_;
}
}
else
{
lean_object* v___x_1293_; lean_object* v_acc_1294_; uint8_t v___x_1295_; 
v___x_1293_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1294_ = lean_string_append(v_acc_1131_, v___x_1293_);
v___x_1295_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1240_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_string_append(v_acc_1294_, v_objectFieldKey_1240_);
lean_dec(v_objectFieldKey_1240_);
v___x_1297_ = lean_string_append(v___x_1296_, v___x_1293_);
v___y_1260_ = v___x_1297_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_string_utf8_byte_size(v_objectFieldKey_1240_);
v___x_1299_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1298_, v_objectFieldKey_1240_, v___x_1140_, v_acc_1294_);
lean_dec(v_objectFieldKey_1240_);
v___x_1300_ = lean_string_append(v___x_1299_, v___x_1293_);
v___y_1260_ = v___x_1300_;
goto v___jp_1259_;
}
}
v___jp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1261_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1262_ = lean_string_append(v___y_1260_, v___x_1261_);
v___x_1263_ = 5;
v___x_1264_ = lean_box(v___x_1263_);
v___x_1265_ = lean_array_push(v___x_1145_, v___x_1264_);
v___x_1266_ = 0;
v___x_1267_ = lean_box(v___x_1266_);
v___x_1268_ = lean_array_push(v___x_1265_, v___x_1267_);
v___x_1269_ = lean_array_push(v___x_1258_, v_value_1244_);
v___x_1270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
lean_ctor_set(v___x_1270_, 2, v___x_1257_);
v_acc_1131_ = v___x_1262_;
v_q_1132_ = v___x_1270_;
goto _start;
}
v___jp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1274_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1275_ = lean_string_append(v___y_1273_, v___x_1274_);
v___x_1276_ = 0;
v___x_1277_ = lean_box(v___x_1276_);
v___x_1278_ = lean_array_push(v___x_1145_, v___x_1277_);
v___x_1279_ = lean_array_push(v___x_1258_, v_value_1244_);
v___x_1280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
lean_ctor_set(v___x_1280_, 2, v___x_1257_);
v_acc_1131_ = v___x_1275_;
v_q_1132_ = v___x_1280_;
goto _start;
}
}
else
{
lean_object* v___x_1301_; lean_object* v_acc_1302_; uint8_t v___x_1303_; 
lean_dec_ref(v___x_1145_);
lean_dec_ref(v_objectFieldKeys_1135_);
lean_dec_ref(v_values_1134_);
v___x_1301_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1302_ = lean_string_append(v_acc_1131_, v___x_1301_);
v___x_1303_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1240_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_string_append(v_acc_1302_, v_objectFieldKey_1240_);
lean_dec(v_objectFieldKey_1240_);
v___x_1305_ = lean_string_append(v___x_1304_, v___x_1301_);
v___y_1246_ = v___x_1305_;
goto v___jp_1245_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_string_utf8_byte_size(v_objectFieldKey_1240_);
v___x_1307_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1306_, v_objectFieldKey_1240_, v___x_1140_, v_acc_1302_);
lean_dec(v_objectFieldKey_1240_);
v___x_1308_ = lean_string_append(v___x_1307_, v___x_1301_);
v___y_1246_ = v___x_1308_;
goto v___jp_1245_;
}
}
v___jp_1245_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1247_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1248_ = lean_string_append(v___y_1246_, v___x_1247_);
v___x_1249_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0));
v___x_1250_ = lean_mk_empty_array_with_capacity(v___x_1142_);
v___x_1251_ = lean_array_push(v___x_1250_, v_value_1244_);
v___x_1252_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1249_);
lean_ctor_set(v___x_1253_, 1, v___x_1251_);
lean_ctor_set(v___x_1253_, 2, v___x_1252_);
v_acc_1131_ = v___x_1248_;
v_q_1132_ = v___x_1253_;
goto _start;
}
}
case 4:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec_ref(v___x_1145_);
lean_dec_ref(v_objectFieldKeys_1135_);
lean_dec_ref(v_values_1134_);
v___x_1309_ = ((lean_object*)(l_Lean_Json_render___closed__16));
v___x_1310_ = lean_string_append(v_acc_1131_, v___x_1309_);
v_acc_1131_ = v___x_1310_;
v_q_1132_ = v_q_1147_;
goto _start;
}
default: 
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec_ref(v___x_1145_);
lean_dec_ref(v_objectFieldKeys_1135_);
lean_dec_ref(v_values_1134_);
v___x_1312_ = ((lean_object*)(l_Lean_Json_render___closed__6));
v___x_1313_ = lean_string_append(v_acc_1131_, v___x_1312_);
v_acc_1131_ = v___x_1313_;
v_q_1132_ = v_q_1147_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_1137_);
lean_dec_ref(v_objectFieldKeys_1135_);
lean_dec_ref(v_values_1134_);
lean_dec_ref(v_kinds_1133_);
return v_acc_1131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_compress(lean_object* v_j_1322_){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1324_ = lean_unsigned_to_nat(1u);
v___x_1325_ = lean_mk_empty_array_with_capacity(v___x_1324_);
v___x_1326_ = ((lean_object*)(l_Lean_Json_compress___closed__0));
v___x_1327_ = lean_array_push(v___x_1325_, v_j_1322_);
v___x_1328_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1326_);
lean_ctor_set(v___x_1329_, 1, v___x_1327_);
lean_ctor_set(v___x_1329_, 2, v___x_1328_);
v___x_1330_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(v___x_1323_, v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instToString___lam__0(lean_object* v_j_1333_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(80u);
v___x_1335_ = l_Lean_Json_pretty(v_j_1333_, v___x_1334_);
return v___x_1335_;
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
