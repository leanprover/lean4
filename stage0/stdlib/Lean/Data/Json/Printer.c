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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_toCtorIdx___boxed(lean_object*);
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
lean_dec_ref(v___x_623_);
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
lean_dec_ref(v___x_637_);
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
lean_dec_ref(v_x_674_);
return v_head_678_;
}
else
{
lean_object* v_head_679_; lean_object* v___x_680_; 
lean_inc(v_tail_677_);
v_head_679_ = lean_ctor_get(v_x_674_, 0);
lean_inc(v_head_679_);
lean_dec_ref(v_x_674_);
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
lean_dec_ref(v_x_710_);
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
lean_dec_ref(v___x_735_);
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
lean_dec_ref(v_x_749_);
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
lean_dec_ref(v___x_776_);
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
lean_dec_ref(v_x_749_);
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
lean_dec_ref(v_x_749_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_toCtorIdx(uint8_t v_x_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx(v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_toCtorIdx___boxed(lean_object* v_x_869_){
_start:
{
uint8_t v_x_4__boxed_870_; lean_object* v_res_871_; 
v_x_4__boxed_870_ = lean_unbox(v_x_869_);
v_res_871_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_toCtorIdx(v_x_4__boxed_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg(lean_object* v_k_872_){
_start:
{
lean_inc(v_k_872_);
return v_k_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg___boxed(lean_object* v_k_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg(v_k_873_);
lean_dec(v_k_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(lean_object* v_motive_875_, lean_object* v_ctorIdx_876_, uint8_t v_t_877_, lean_object* v_h_878_, lean_object* v_k_879_){
_start:
{
lean_inc(v_k_879_);
return v_k_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___boxed(lean_object* v_motive_880_, lean_object* v_ctorIdx_881_, lean_object* v_t_882_, lean_object* v_h_883_, lean_object* v_k_884_){
_start:
{
uint8_t v_t_boxed_885_; lean_object* v_res_886_; 
v_t_boxed_885_ = lean_unbox(v_t_882_);
v_res_886_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(v_motive_880_, v_ctorIdx_881_, v_t_boxed_885_, v_h_883_, v_k_884_);
lean_dec(v_k_884_);
lean_dec(v_ctorIdx_881_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(lean_object* v_json_887_){
_start:
{
lean_inc(v_json_887_);
return v_json_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg___boxed(lean_object* v_json_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(v_json_888_);
lean_dec(v_json_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(lean_object* v_motive_890_, uint8_t v_t_891_, lean_object* v_h_892_, lean_object* v_json_893_){
_start:
{
lean_inc(v_json_893_);
return v_json_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___boxed(lean_object* v_motive_894_, lean_object* v_t_895_, lean_object* v_h_896_, lean_object* v_json_897_){
_start:
{
uint8_t v_t_boxed_898_; lean_object* v_res_899_; 
v_t_boxed_898_ = lean_unbox(v_t_895_);
v_res_899_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(v_motive_894_, v_t_boxed_898_, v_h_896_, v_json_897_);
lean_dec(v_json_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(lean_object* v_arrayElem_900_){
_start:
{
lean_inc(v_arrayElem_900_);
return v_arrayElem_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg___boxed(lean_object* v_arrayElem_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(v_arrayElem_901_);
lean_dec(v_arrayElem_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(lean_object* v_motive_903_, uint8_t v_t_904_, lean_object* v_h_905_, lean_object* v_arrayElem_906_){
_start:
{
lean_inc(v_arrayElem_906_);
return v_arrayElem_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___boxed(lean_object* v_motive_907_, lean_object* v_t_908_, lean_object* v_h_909_, lean_object* v_arrayElem_910_){
_start:
{
uint8_t v_t_boxed_911_; lean_object* v_res_912_; 
v_t_boxed_911_ = lean_unbox(v_t_908_);
v_res_912_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(v_motive_907_, v_t_boxed_911_, v_h_909_, v_arrayElem_910_);
lean_dec(v_arrayElem_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(lean_object* v_arrayEnd_913_){
_start:
{
lean_inc(v_arrayEnd_913_);
return v_arrayEnd_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg___boxed(lean_object* v_arrayEnd_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(v_arrayEnd_914_);
lean_dec(v_arrayEnd_914_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(lean_object* v_motive_916_, uint8_t v_t_917_, lean_object* v_h_918_, lean_object* v_arrayEnd_919_){
_start:
{
lean_inc(v_arrayEnd_919_);
return v_arrayEnd_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___boxed(lean_object* v_motive_920_, lean_object* v_t_921_, lean_object* v_h_922_, lean_object* v_arrayEnd_923_){
_start:
{
uint8_t v_t_boxed_924_; lean_object* v_res_925_; 
v_t_boxed_924_ = lean_unbox(v_t_921_);
v_res_925_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(v_motive_920_, v_t_boxed_924_, v_h_922_, v_arrayEnd_923_);
lean_dec(v_arrayEnd_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(lean_object* v_objectField_926_){
_start:
{
lean_inc(v_objectField_926_);
return v_objectField_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg___boxed(lean_object* v_objectField_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(v_objectField_927_);
lean_dec(v_objectField_927_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(lean_object* v_motive_929_, uint8_t v_t_930_, lean_object* v_h_931_, lean_object* v_objectField_932_){
_start:
{
lean_inc(v_objectField_932_);
return v_objectField_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___boxed(lean_object* v_motive_933_, lean_object* v_t_934_, lean_object* v_h_935_, lean_object* v_objectField_936_){
_start:
{
uint8_t v_t_boxed_937_; lean_object* v_res_938_; 
v_t_boxed_937_ = lean_unbox(v_t_934_);
v_res_938_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(v_motive_933_, v_t_boxed_937_, v_h_935_, v_objectField_936_);
lean_dec(v_objectField_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(lean_object* v_objectEnd_939_){
_start:
{
lean_inc(v_objectEnd_939_);
return v_objectEnd_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg___boxed(lean_object* v_objectEnd_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(v_objectEnd_940_);
lean_dec(v_objectEnd_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(lean_object* v_motive_942_, uint8_t v_t_943_, lean_object* v_h_944_, lean_object* v_objectEnd_945_){
_start:
{
lean_inc(v_objectEnd_945_);
return v_objectEnd_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___boxed(lean_object* v_motive_946_, lean_object* v_t_947_, lean_object* v_h_948_, lean_object* v_objectEnd_949_){
_start:
{
uint8_t v_t_boxed_950_; lean_object* v_res_951_; 
v_t_boxed_950_ = lean_unbox(v_t_947_);
v_res_951_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(v_motive_946_, v_t_boxed_950_, v_h_948_, v_objectEnd_949_);
lean_dec(v_objectEnd_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(lean_object* v_comma_952_){
_start:
{
lean_inc(v_comma_952_);
return v_comma_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg___boxed(lean_object* v_comma_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(v_comma_953_);
lean_dec(v_comma_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(lean_object* v_motive_955_, uint8_t v_t_956_, lean_object* v_h_957_, lean_object* v_comma_958_){
_start:
{
lean_inc(v_comma_958_);
return v_comma_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___boxed(lean_object* v_motive_959_, lean_object* v_t_960_, lean_object* v_h_961_, lean_object* v_comma_962_){
_start:
{
uint8_t v_t_boxed_963_; lean_object* v_res_964_; 
v_t_boxed_963_ = lean_unbox(v_t_960_);
v_res_964_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(v_motive_959_, v_t_boxed_963_, v_h_961_, v_comma_962_);
lean_dec(v_comma_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(lean_object* v_q_965_, uint8_t v_kind_966_){
_start:
{
lean_object* v_kinds_967_; lean_object* v_values_968_; lean_object* v_objectFieldKeys_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_978_; 
v_kinds_967_ = lean_ctor_get(v_q_965_, 0);
v_values_968_ = lean_ctor_get(v_q_965_, 1);
v_objectFieldKeys_969_ = lean_ctor_get(v_q_965_, 2);
v_isSharedCheck_978_ = !lean_is_exclusive(v_q_965_);
if (v_isSharedCheck_978_ == 0)
{
v___x_971_ = v_q_965_;
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_objectFieldKeys_969_);
lean_inc(v_values_968_);
lean_inc(v_kinds_967_);
lean_dec(v_q_965_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_973_ = lean_box(v_kind_966_);
v___x_974_ = lean_array_push(v_kinds_967_, v___x_973_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_974_);
v___x_976_ = v___x_971_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_values_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_objectFieldKeys_969_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind___boxed(lean_object* v_q_979_, lean_object* v_kind_980_){
_start:
{
uint8_t v_kind_boxed_981_; lean_object* v_res_982_; 
v_kind_boxed_981_ = lean_unbox(v_kind_980_);
v_res_982_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(v_q_979_, v_kind_boxed_981_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushValue(lean_object* v_q_983_, lean_object* v_value_984_){
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
v___x_991_ = lean_array_push(v_values_986_, v_value_984_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_kinds_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_objectFieldKeys_987_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushObjectFieldKey(lean_object* v_q_996_, lean_object* v_objectFieldKey_997_){
_start:
{
lean_object* v_kinds_998_; lean_object* v_values_999_; lean_object* v_objectFieldKeys_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1008_; 
v_kinds_998_ = lean_ctor_get(v_q_996_, 0);
v_values_999_ = lean_ctor_get(v_q_996_, 1);
v_objectFieldKeys_1000_ = lean_ctor_get(v_q_996_, 2);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_q_996_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1002_ = v_q_996_;
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_objectFieldKeys_1000_);
lean_inc(v_values_999_);
lean_inc(v_kinds_998_);
lean_dec(v_q_996_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_array_push(v_objectFieldKeys_1000_, v_objectFieldKey_997_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 2, v___x_1004_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_kinds_998_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_values_999_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind___redArg(lean_object* v_q_1009_){
_start:
{
lean_object* v_kinds_1010_; lean_object* v_values_1011_; lean_object* v_objectFieldKeys_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1025_; 
v_kinds_1010_ = lean_ctor_get(v_q_1009_, 0);
v_values_1011_ = lean_ctor_get(v_q_1009_, 1);
v_objectFieldKeys_1012_ = lean_ctor_get(v_q_1009_, 2);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_q_1009_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1014_ = v_q_1009_;
v_isShared_1015_ = v_isSharedCheck_1025_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_objectFieldKeys_1012_);
lean_inc(v_values_1011_);
lean_inc(v_kinds_1010_);
lean_dec(v_q_1009_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind(lean_object* v_q_1026_, lean_object* v_h_1027_){
_start:
{
lean_object* v_kinds_1028_; lean_object* v_values_1029_; lean_object* v_objectFieldKeys_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1043_; 
v_kinds_1028_ = lean_ctor_get(v_q_1026_, 0);
v_values_1029_ = lean_ctor_get(v_q_1026_, 1);
v_objectFieldKeys_1030_ = lean_ctor_get(v_q_1026_, 2);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_q_1026_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1032_ = v_q_1026_;
v_isShared_1033_ = v_isSharedCheck_1043_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_objectFieldKeys_1030_);
lean_inc(v_values_1029_);
lean_inc(v_kinds_1028_);
lean_dec(v_q_1026_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1043_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_kind_1037_; lean_object* v___x_1038_; lean_object* v_q_1040_; 
v___x_1034_ = lean_array_get_size(v_kinds_1028_);
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_nat_sub(v___x_1034_, v___x_1035_);
v_kind_1037_ = lean_array_fget(v_kinds_1028_, v___x_1036_);
lean_dec(v___x_1036_);
v___x_1038_ = lean_array_pop(v_kinds_1028_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1038_);
v_q_1040_ = v___x_1032_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_values_1029_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_objectFieldKeys_1030_);
v_q_1040_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_kind_1037_);
lean_ctor_set(v___x_1041_, 1, v_q_1040_);
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popValue_x21(lean_object* v_q_1044_){
_start:
{
lean_object* v_kinds_1045_; lean_object* v_values_1046_; lean_object* v_objectFieldKeys_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1061_; 
v_kinds_1045_ = lean_ctor_get(v_q_1044_, 0);
v_values_1046_ = lean_ctor_get(v_q_1044_, 1);
v_objectFieldKeys_1047_ = lean_ctor_get(v_q_1044_, 2);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_q_1044_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1049_ = v_q_1044_;
v_isShared_1050_ = v_isSharedCheck_1061_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_objectFieldKeys_1047_);
lean_inc(v_values_1046_);
lean_inc(v_kinds_1045_);
lean_dec(v_q_1044_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1061_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_value_1055_; lean_object* v___x_1056_; lean_object* v_q_1058_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_array_get_size(v_values_1046_);
v___x_1053_ = lean_unsigned_to_nat(1u);
v___x_1054_ = lean_nat_sub(v___x_1052_, v___x_1053_);
v_value_1055_ = lean_array_get(v___x_1051_, v_values_1046_, v___x_1054_);
lean_dec(v___x_1054_);
v___x_1056_ = lean_array_pop(v_values_1046_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v___x_1056_);
v_q_1058_ = v___x_1049_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_kinds_1045_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_objectFieldKeys_1047_);
v_q_1058_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_value_1055_);
lean_ctor_set(v___x_1059_, 1, v_q_1058_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21(lean_object* v_q_1063_){
_start:
{
lean_object* v_kinds_1064_; lean_object* v_values_1065_; lean_object* v_objectFieldKeys_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1080_; 
v_kinds_1064_ = lean_ctor_get(v_q_1063_, 0);
v_values_1065_ = lean_ctor_get(v_q_1063_, 1);
v_objectFieldKeys_1066_ = lean_ctor_get(v_q_1063_, 2);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_q_1063_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1068_ = v_q_1063_;
v_isShared_1069_ = v_isSharedCheck_1080_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_objectFieldKeys_1066_);
lean_inc(v_values_1065_);
lean_inc(v_kinds_1064_);
lean_dec(v_q_1063_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1080_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v_objectFieldKey_1074_; lean_object* v___x_1075_; lean_object* v_q_1077_; 
v___x_1070_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1071_ = lean_array_get_size(v_objectFieldKeys_1066_);
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_nat_sub(v___x_1071_, v___x_1072_);
v_objectFieldKey_1074_ = lean_array_get(v___x_1070_, v_objectFieldKeys_1066_, v___x_1073_);
lean_dec(v___x_1073_);
v___x_1075_ = lean_array_pop(v_objectFieldKeys_1066_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 2, v___x_1075_);
v_q_1077_ = v___x_1068_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_kinds_1064_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_values_1065_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v___x_1075_);
v_q_1077_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_objectFieldKey_1074_);
lean_ctor_set(v___x_1078_, 1, v_q_1077_);
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(lean_object* v_as_1081_, size_t v_i_1082_, size_t v_stop_1083_, lean_object* v_b_1084_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_usize_dec_eq(v_i_1082_, v_stop_1083_);
if (v___x_1085_ == 0)
{
lean_object* v_kinds_1086_; lean_object* v_values_1087_; lean_object* v_objectFieldKeys_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1103_; 
v_kinds_1086_ = lean_ctor_get(v_b_1084_, 0);
v_values_1087_ = lean_ctor_get(v_b_1084_, 1);
v_objectFieldKeys_1088_ = lean_ctor_get(v_b_1084_, 2);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_b_1084_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1090_ = v_b_1084_;
v_isShared_1091_ = v_isSharedCheck_1103_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_objectFieldKeys_1088_);
lean_inc(v_values_1087_);
lean_inc(v_kinds_1086_);
lean_dec(v_b_1084_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1103_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
size_t v___x_1092_; size_t v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1092_ = ((size_t)1ULL);
v___x_1093_ = lean_usize_sub(v_i_1082_, v___x_1092_);
v___x_1094_ = lean_array_uget_borrowed(v_as_1081_, v___x_1093_);
v___x_1095_ = 1;
v___x_1096_ = lean_box(v___x_1095_);
v___x_1097_ = lean_array_push(v_kinds_1086_, v___x_1096_);
lean_inc(v___x_1094_);
v___x_1098_ = lean_array_push(v_values_1087_, v___x_1094_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v___x_1098_);
lean_ctor_set(v___x_1090_, 0, v___x_1097_);
v___x_1100_ = v___x_1090_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_objectFieldKeys_1088_);
v___x_1100_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
v_i_1082_ = v___x_1093_;
v_b_1084_ = v___x_1100_;
goto _start;
}
}
}
else
{
return v_b_1084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0___boxed(lean_object* v_as_1104_, lean_object* v_i_1105_, lean_object* v_stop_1106_, lean_object* v_b_1107_){
_start:
{
size_t v_i_boxed_1108_; size_t v_stop_boxed_1109_; lean_object* v_res_1110_; 
v_i_boxed_1108_ = lean_unbox_usize(v_i_1105_);
lean_dec(v_i_1105_);
v_stop_boxed_1109_ = lean_unbox_usize(v_stop_1106_);
lean_dec(v_stop_1106_);
v_res_1110_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_as_1104_, v_i_boxed_1108_, v_stop_boxed_1109_, v_b_1107_);
lean_dec_ref(v_as_1104_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(lean_object* v_init_1111_, lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v_k_1113_; lean_object* v_v_1114_; lean_object* v_l_1115_; lean_object* v_r_1116_; lean_object* v___x_1117_; lean_object* v_kinds_1118_; lean_object* v_values_1119_; lean_object* v_objectFieldKeys_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1133_; 
v_k_1113_ = lean_ctor_get(v_x_1112_, 1);
lean_inc(v_k_1113_);
v_v_1114_ = lean_ctor_get(v_x_1112_, 2);
lean_inc(v_v_1114_);
v_l_1115_ = lean_ctor_get(v_x_1112_, 3);
lean_inc(v_l_1115_);
v_r_1116_ = lean_ctor_get(v_x_1112_, 4);
lean_inc(v_r_1116_);
lean_dec_ref(v_x_1112_);
v___x_1117_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_init_1111_, v_r_1116_);
v_kinds_1118_ = lean_ctor_get(v___x_1117_, 0);
v_values_1119_ = lean_ctor_get(v___x_1117_, 1);
v_objectFieldKeys_1120_ = lean_ctor_get(v___x_1117_, 2);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1122_ = v___x_1117_;
v_isShared_1123_ = v_isSharedCheck_1133_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_objectFieldKeys_1120_);
lean_inc(v_values_1119_);
lean_inc(v_kinds_1118_);
lean_dec(v___x_1117_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1133_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1124_ = 3;
v___x_1125_ = lean_box(v___x_1124_);
v___x_1126_ = lean_array_push(v_kinds_1118_, v___x_1125_);
v___x_1127_ = lean_array_push(v_objectFieldKeys_1120_, v_k_1113_);
v___x_1128_ = lean_array_push(v_values_1119_, v_v_1114_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 2, v___x_1127_);
lean_ctor_set(v___x_1122_, 1, v___x_1128_);
lean_ctor_set(v___x_1122_, 0, v___x_1126_);
v___x_1130_ = v___x_1122_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v___x_1127_);
v___x_1130_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
v_init_1111_ = v___x_1130_;
v_x_1112_ = v_l_1115_;
goto _start;
}
}
}
else
{
return v_init_1111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(lean_object* v_acc_1144_, lean_object* v_q_1145_){
_start:
{
lean_object* v_kinds_1146_; lean_object* v_values_1147_; lean_object* v_objectFieldKeys_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1337_; 
v_kinds_1146_ = lean_ctor_get(v_q_1145_, 0);
v_values_1147_ = lean_ctor_get(v_q_1145_, 1);
v_objectFieldKeys_1148_ = lean_ctor_get(v_q_1145_, 2);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_q_1145_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1150_ = v_q_1145_;
v_isShared_1151_ = v_isSharedCheck_1337_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_objectFieldKeys_1148_);
lean_inc(v_values_1147_);
lean_inc(v_kinds_1146_);
lean_dec(v_q_1145_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1337_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1152_ = lean_array_get_size(v_kinds_1146_);
v___x_1153_ = lean_unsigned_to_nat(0u);
v___x_1154_ = lean_nat_dec_eq(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_kind_1157_; lean_object* v___x_1158_; lean_object* v_q_1160_; 
v___x_1155_ = lean_unsigned_to_nat(1u);
v___x_1156_ = lean_nat_sub(v___x_1152_, v___x_1155_);
v_kind_1157_ = lean_array_fget(v_kinds_1146_, v___x_1156_);
lean_dec(v___x_1156_);
v___x_1158_ = lean_array_pop(v_kinds_1146_);
lean_inc_ref(v_objectFieldKeys_1148_);
lean_inc_ref(v_values_1147_);
lean_inc_ref(v___x_1158_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1158_);
v_q_1160_ = v___x_1150_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_values_1147_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_objectFieldKeys_1148_);
v_q_1160_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_unbox(v_kind_1157_);
lean_dec(v_kind_1157_);
switch(v___x_1161_)
{
case 0:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_value_1165_; lean_object* v___x_1166_; lean_object* v_q_1167_; lean_object* v___y_1169_; 
lean_dec_ref(v_q_1160_);
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_array_get_size(v_values_1147_);
v___x_1164_ = lean_nat_sub(v___x_1163_, v___x_1155_);
v_value_1165_ = lean_array_get(v___x_1162_, v_values_1147_, v___x_1164_);
lean_dec(v___x_1164_);
v___x_1166_ = lean_array_pop(v_values_1147_);
lean_inc_ref(v_objectFieldKeys_1148_);
lean_inc_ref(v___x_1166_);
lean_inc_ref(v___x_1158_);
v_q_1167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1167_, 0, v___x_1158_);
lean_ctor_set(v_q_1167_, 1, v___x_1166_);
lean_ctor_set(v_q_1167_, 2, v_objectFieldKeys_1148_);
switch(lean_obj_tag(v_value_1165_))
{
case 0:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec_ref(v___x_1166_);
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_objectFieldKeys_1148_);
v___x_1172_ = ((lean_object*)(l_Lean_Json_render___closed__0));
v___x_1173_ = lean_string_append(v_acc_1144_, v___x_1172_);
v_acc_1144_ = v___x_1173_;
v_q_1145_ = v_q_1167_;
goto _start;
}
case 1:
{
uint8_t v_b_1175_; 
lean_dec_ref(v___x_1166_);
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_objectFieldKeys_1148_);
v_b_1175_ = lean_ctor_get_uint8(v_value_1165_, 0);
lean_dec_ref(v_value_1165_);
if (v_b_1175_ == 0)
{
lean_object* v___x_1176_; 
v___x_1176_ = ((lean_object*)(l_Lean_Json_render___closed__2));
v___y_1169_ = v___x_1176_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = ((lean_object*)(l_Lean_Json_render___closed__4));
v___y_1169_ = v___x_1177_;
goto v___jp_1168_;
}
}
case 2:
{
lean_object* v_n_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v___x_1166_);
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_objectFieldKeys_1148_);
v_n_1178_ = lean_ctor_get(v_value_1165_, 0);
lean_inc_ref(v_n_1178_);
lean_dec_ref(v_value_1165_);
v___x_1179_ = l_Lean_JsonNumber_toString(v_n_1178_);
v___x_1180_ = lean_string_append(v_acc_1144_, v___x_1179_);
lean_dec_ref(v___x_1179_);
v_acc_1144_ = v___x_1180_;
v_q_1145_ = v_q_1167_;
goto _start;
}
case 3:
{
lean_object* v_s_1182_; lean_object* v___x_1183_; lean_object* v_acc_1184_; uint8_t v___x_1185_; 
lean_dec_ref(v___x_1166_);
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_objectFieldKeys_1148_);
v_s_1182_ = lean_ctor_get(v_value_1165_, 0);
lean_inc_ref(v_s_1182_);
lean_dec_ref(v_value_1165_);
v___x_1183_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1184_ = lean_string_append(v_acc_1144_, v___x_1183_);
v___x_1185_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_1182_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_string_append(v_acc_1184_, v_s_1182_);
lean_dec_ref(v_s_1182_);
v___x_1187_ = lean_string_append(v___x_1186_, v___x_1183_);
v_acc_1144_ = v___x_1187_;
v_q_1145_ = v_q_1167_;
goto _start;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1189_ = lean_string_utf8_byte_size(v_s_1182_);
lean_inc_ref(v_s_1182_);
v___x_1190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1190_, 0, v_s_1182_);
lean_ctor_set(v___x_1190_, 1, v___x_1153_);
lean_ctor_set(v___x_1190_, 2, v___x_1189_);
v___x_1191_ = l_String_Slice_positions(v___x_1190_);
v___x_1192_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1190_, v_s_1182_, v___x_1191_, v_acc_1184_);
lean_dec_ref(v_s_1182_);
lean_dec_ref(v___x_1190_);
v___x_1193_ = lean_string_append(v___x_1192_, v___x_1183_);
v_acc_1144_ = v___x_1193_;
v_q_1145_ = v_q_1167_;
goto _start;
}
}
case 4:
{
lean_object* v_elems_1195_; uint8_t v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v_q_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
lean_dec_ref(v_q_1167_);
v_elems_1195_ = lean_ctor_get(v_value_1165_, 0);
lean_inc_ref(v_elems_1195_);
lean_dec_ref(v_value_1165_);
v___x_1196_ = 2;
v___x_1197_ = lean_box(v___x_1196_);
v___x_1198_ = lean_array_push(v___x_1158_, v___x_1197_);
v_q_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1199_, 0, v___x_1198_);
lean_ctor_set(v_q_1199_, 1, v___x_1166_);
lean_ctor_set(v_q_1199_, 2, v_objectFieldKeys_1148_);
v___x_1200_ = ((lean_object*)(l_Lean_Json_render___closed__9));
v___x_1201_ = lean_string_append(v_acc_1144_, v___x_1200_);
v___x_1202_ = lean_array_get_size(v_elems_1195_);
v___x_1203_ = lean_nat_dec_lt(v___x_1153_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_dec_ref(v_elems_1195_);
v_acc_1144_ = v___x_1201_;
v_q_1145_ = v_q_1199_;
goto _start;
}
else
{
size_t v___x_1205_; size_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = lean_usize_of_nat(v___x_1202_);
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_elems_1195_, v___x_1205_, v___x_1206_, v_q_1199_);
lean_dec_ref(v_elems_1195_);
v_acc_1144_ = v___x_1201_;
v_q_1145_ = v___x_1207_;
goto _start;
}
}
default: 
{
lean_object* v_kvPairs_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v_q_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec_ref(v_q_1167_);
v_kvPairs_1209_ = lean_ctor_get(v_value_1165_, 0);
lean_inc(v_kvPairs_1209_);
lean_dec_ref(v_value_1165_);
v___x_1210_ = 4;
v___x_1211_ = lean_box(v___x_1210_);
v___x_1212_ = lean_array_push(v___x_1158_, v___x_1211_);
v_q_1213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_q_1213_, 0, v___x_1212_);
lean_ctor_set(v_q_1213_, 1, v___x_1166_);
lean_ctor_set(v_q_1213_, 2, v_objectFieldKeys_1148_);
v___x_1214_ = ((lean_object*)(l_Lean_Json_render___closed__15));
v___x_1215_ = lean_string_append(v_acc_1144_, v___x_1214_);
v___x_1216_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_q_1213_, v_kvPairs_1209_);
v_acc_1144_ = v___x_1215_;
v_q_1145_ = v___x_1216_;
goto _start;
}
}
v___jp_1168_:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_string_append(v_acc_1144_, v___y_1169_);
lean_dec_ref(v___y_1169_);
v_acc_1144_ = v___x_1170_;
v_q_1145_ = v_q_1167_;
goto _start;
}
}
case 1:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_value_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
lean_dec_ref(v_q_1160_);
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_array_get_size(v_values_1147_);
v___x_1220_ = lean_nat_sub(v___x_1219_, v___x_1155_);
v_value_1221_ = lean_array_get(v___x_1218_, v_values_1147_, v___x_1220_);
lean_dec(v___x_1220_);
v___x_1222_ = lean_array_get_size(v___x_1158_);
v___x_1223_ = lean_nat_dec_eq(v___x_1222_, v___x_1153_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_kind_1226_; uint8_t v___x_1227_; 
v___x_1224_ = lean_array_pop(v_values_1147_);
v___x_1225_ = lean_nat_sub(v___x_1222_, v___x_1155_);
v_kind_1226_ = lean_array_fget(v___x_1158_, v___x_1225_);
lean_dec(v___x_1225_);
v___x_1227_ = lean_unbox(v_kind_1226_);
lean_dec(v_kind_1226_);
if (v___x_1227_ == 2)
{
uint8_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1228_ = 0;
v___x_1229_ = lean_box(v___x_1228_);
v___x_1230_ = lean_array_push(v___x_1158_, v___x_1229_);
v___x_1231_ = lean_array_push(v___x_1224_, v_value_1221_);
v___x_1232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
lean_ctor_set(v___x_1232_, 2, v_objectFieldKeys_1148_);
v_q_1145_ = v___x_1232_;
goto _start;
}
else
{
uint8_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1234_ = 5;
v___x_1235_ = lean_box(v___x_1234_);
v___x_1236_ = lean_array_push(v___x_1158_, v___x_1235_);
v___x_1237_ = 0;
v___x_1238_ = lean_box(v___x_1237_);
v___x_1239_ = lean_array_push(v___x_1236_, v___x_1238_);
v___x_1240_ = lean_array_push(v___x_1224_, v_value_1221_);
v___x_1241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
lean_ctor_set(v___x_1241_, 2, v_objectFieldKeys_1148_);
v_q_1145_ = v___x_1241_;
goto _start;
}
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_objectFieldKeys_1148_);
lean_dec_ref(v_values_1147_);
v___x_1243_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0));
v___x_1244_ = lean_mk_empty_array_with_capacity(v___x_1155_);
v___x_1245_ = lean_array_push(v___x_1244_, v_value_1221_);
v___x_1246_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1243_);
lean_ctor_set(v___x_1247_, 1, v___x_1245_);
lean_ctor_set(v___x_1247_, 2, v___x_1246_);
v_q_1145_ = v___x_1247_;
goto _start;
}
}
case 2:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_objectFieldKeys_1148_);
lean_dec_ref(v_values_1147_);
v___x_1249_ = ((lean_object*)(l_Lean_Json_render___closed__10));
v___x_1250_ = lean_string_append(v_acc_1144_, v___x_1249_);
v_acc_1144_ = v___x_1250_;
v_q_1145_ = v_q_1160_;
goto _start;
}
case 3:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_objectFieldKey_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v_value_1259_; lean_object* v___y_1261_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
lean_dec_ref(v_q_1160_);
v___x_1252_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1253_ = lean_array_get_size(v_objectFieldKeys_1148_);
v___x_1254_ = lean_nat_sub(v___x_1253_, v___x_1155_);
v_objectFieldKey_1255_ = lean_array_get(v___x_1252_, v_objectFieldKeys_1148_, v___x_1254_);
lean_dec(v___x_1254_);
v___x_1256_ = lean_box(0);
v___x_1257_ = lean_array_get_size(v_values_1147_);
v___x_1258_ = lean_nat_sub(v___x_1257_, v___x_1155_);
v_value_1259_ = lean_array_get(v___x_1256_, v_values_1147_, v___x_1258_);
lean_dec(v___x_1258_);
v___x_1270_ = lean_array_get_size(v___x_1158_);
v___x_1271_ = lean_nat_dec_eq(v___x_1270_, v___x_1153_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___y_1275_; lean_object* v___y_1288_; lean_object* v___x_1297_; lean_object* v_kind_1298_; uint8_t v___x_1299_; 
v___x_1272_ = lean_array_pop(v_objectFieldKeys_1148_);
v___x_1273_ = lean_array_pop(v_values_1147_);
v___x_1297_ = lean_nat_sub(v___x_1270_, v___x_1155_);
v_kind_1298_ = lean_array_fget(v___x_1158_, v___x_1297_);
lean_dec(v___x_1297_);
v___x_1299_ = lean_unbox(v_kind_1298_);
lean_dec(v_kind_1298_);
if (v___x_1299_ == 4)
{
lean_object* v___x_1300_; lean_object* v_acc_1301_; uint8_t v___x_1302_; 
v___x_1300_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1301_ = lean_string_append(v_acc_1144_, v___x_1300_);
v___x_1302_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1255_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_string_append(v_acc_1301_, v_objectFieldKey_1255_);
lean_dec(v_objectFieldKey_1255_);
v___x_1304_ = lean_string_append(v___x_1303_, v___x_1300_);
v___y_1288_ = v___x_1304_;
goto v___jp_1287_;
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1305_ = lean_string_utf8_byte_size(v_objectFieldKey_1255_);
lean_inc(v_objectFieldKey_1255_);
v___x_1306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1306_, 0, v_objectFieldKey_1255_);
lean_ctor_set(v___x_1306_, 1, v___x_1153_);
lean_ctor_set(v___x_1306_, 2, v___x_1305_);
v___x_1307_ = l_String_Slice_positions(v___x_1306_);
v___x_1308_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1306_, v_objectFieldKey_1255_, v___x_1307_, v_acc_1301_);
lean_dec(v_objectFieldKey_1255_);
lean_dec_ref(v___x_1306_);
v___x_1309_ = lean_string_append(v___x_1308_, v___x_1300_);
v___y_1288_ = v___x_1309_;
goto v___jp_1287_;
}
}
else
{
lean_object* v___x_1310_; lean_object* v_acc_1311_; uint8_t v___x_1312_; 
v___x_1310_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1311_ = lean_string_append(v_acc_1144_, v___x_1310_);
v___x_1312_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1255_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_string_append(v_acc_1311_, v_objectFieldKey_1255_);
lean_dec(v_objectFieldKey_1255_);
v___x_1314_ = lean_string_append(v___x_1313_, v___x_1310_);
v___y_1275_ = v___x_1314_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1315_ = lean_string_utf8_byte_size(v_objectFieldKey_1255_);
lean_inc(v_objectFieldKey_1255_);
v___x_1316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1316_, 0, v_objectFieldKey_1255_);
lean_ctor_set(v___x_1316_, 1, v___x_1153_);
lean_ctor_set(v___x_1316_, 2, v___x_1315_);
v___x_1317_ = l_String_Slice_positions(v___x_1316_);
v___x_1318_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1316_, v_objectFieldKey_1255_, v___x_1317_, v_acc_1311_);
lean_dec(v_objectFieldKey_1255_);
lean_dec_ref(v___x_1316_);
v___x_1319_ = lean_string_append(v___x_1318_, v___x_1310_);
v___y_1275_ = v___x_1319_;
goto v___jp_1274_;
}
}
v___jp_1274_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1276_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1277_ = lean_string_append(v___y_1275_, v___x_1276_);
v___x_1278_ = 5;
v___x_1279_ = lean_box(v___x_1278_);
v___x_1280_ = lean_array_push(v___x_1158_, v___x_1279_);
v___x_1281_ = 0;
v___x_1282_ = lean_box(v___x_1281_);
v___x_1283_ = lean_array_push(v___x_1280_, v___x_1282_);
v___x_1284_ = lean_array_push(v___x_1273_, v_value_1259_);
v___x_1285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
lean_ctor_set(v___x_1285_, 2, v___x_1272_);
v_acc_1144_ = v___x_1277_;
v_q_1145_ = v___x_1285_;
goto _start;
}
v___jp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1289_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1290_ = lean_string_append(v___y_1288_, v___x_1289_);
v___x_1291_ = 0;
v___x_1292_ = lean_box(v___x_1291_);
v___x_1293_ = lean_array_push(v___x_1158_, v___x_1292_);
v___x_1294_ = lean_array_push(v___x_1273_, v_value_1259_);
v___x_1295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
lean_ctor_set(v___x_1295_, 2, v___x_1272_);
v_acc_1144_ = v___x_1290_;
v_q_1145_ = v___x_1295_;
goto _start;
}
}
else
{
lean_object* v___x_1320_; lean_object* v_acc_1321_; uint8_t v___x_1322_; 
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_objectFieldKeys_1148_);
lean_dec_ref(v_values_1147_);
v___x_1320_ = ((lean_object*)(l_Lean_Json_renderString___closed__0));
v_acc_1321_ = lean_string_append(v_acc_1144_, v___x_1320_);
v___x_1322_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_objectFieldKey_1255_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_string_append(v_acc_1321_, v_objectFieldKey_1255_);
lean_dec(v_objectFieldKey_1255_);
v___x_1324_ = lean_string_append(v___x_1323_, v___x_1320_);
v___y_1261_ = v___x_1324_;
goto v___jp_1260_;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1325_ = lean_string_utf8_byte_size(v_objectFieldKey_1255_);
lean_inc(v_objectFieldKey_1255_);
v___x_1326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1326_, 0, v_objectFieldKey_1255_);
lean_ctor_set(v___x_1326_, 1, v___x_1153_);
lean_ctor_set(v___x_1326_, 2, v___x_1325_);
v___x_1327_ = l_String_Slice_positions(v___x_1326_);
v___x_1328_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_1326_, v_objectFieldKey_1255_, v___x_1327_, v_acc_1321_);
lean_dec(v_objectFieldKey_1255_);
lean_dec_ref(v___x_1326_);
v___x_1329_ = lean_string_append(v___x_1328_, v___x_1320_);
v___y_1261_ = v___x_1329_;
goto v___jp_1260_;
}
}
v___jp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1262_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0));
v___x_1263_ = lean_string_append(v___y_1261_, v___x_1262_);
v___x_1264_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0));
v___x_1265_ = lean_mk_empty_array_with_capacity(v___x_1155_);
v___x_1266_ = lean_array_push(v___x_1265_, v_value_1259_);
v___x_1267_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1264_);
lean_ctor_set(v___x_1268_, 1, v___x_1266_);
lean_ctor_set(v___x_1268_, 2, v___x_1267_);
v_acc_1144_ = v___x_1263_;
v_q_1145_ = v___x_1268_;
goto _start;
}
}
case 4:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_objectFieldKeys_1148_);
lean_dec_ref(v_values_1147_);
v___x_1330_ = ((lean_object*)(l_Lean_Json_render___closed__16));
v___x_1331_ = lean_string_append(v_acc_1144_, v___x_1330_);
v_acc_1144_ = v___x_1331_;
v_q_1145_ = v_q_1160_;
goto _start;
}
default: 
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_objectFieldKeys_1148_);
lean_dec_ref(v_values_1147_);
v___x_1333_ = ((lean_object*)(l_Lean_Json_render___closed__6));
v___x_1334_ = lean_string_append(v_acc_1144_, v___x_1333_);
v_acc_1144_ = v___x_1334_;
v_q_1145_ = v_q_1160_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_1150_);
lean_dec_ref(v_objectFieldKeys_1148_);
lean_dec_ref(v_values_1147_);
lean_dec_ref(v_kinds_1146_);
return v_acc_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_compress(lean_object* v_j_1343_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1344_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0));
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1346_ = lean_mk_empty_array_with_capacity(v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Lean_Json_compress___closed__0));
v___x_1348_ = lean_array_push(v___x_1346_, v_j_1343_);
v___x_1349_ = ((lean_object*)(l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1));
v___x_1350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1347_);
lean_ctor_set(v___x_1350_, 1, v___x_1348_);
lean_ctor_set(v___x_1350_, 2, v___x_1349_);
v___x_1351_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(v___x_1344_, v___x_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instToString___lam__0(lean_object* v_j_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_unsigned_to_nat(80u);
v___x_1356_ = l_Lean_Json_pretty(v_j_1354_, v___x_1355_);
return v___x_1356_;
}
}
lean_object* runtime_initialize_Lean_Data_Format(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_Printer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
