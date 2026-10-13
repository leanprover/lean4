// Lean compiler output
// Module: Lean.Data.Html.Basic
// Imports: public import Init.Data.Array.GetLit public import Init.Data.Array.Mem public import Init.Dynamic public import Lean.Data.Json.Elab
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_element_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_element_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_text_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_text_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_raw_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_raw_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_seq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_seq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__3_value;
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__4_value;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__5;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__6;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__7 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__7_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__4_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__8 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__1_value;
static lean_once_cell_t l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__2;
static lean_once_cell_t l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__3;
static const lean_ctor_object l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__5_value;
static const lean_string_object l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__6_value;
static const lean_ctor_object l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__6_value)}};
static const lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__7_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprHtml_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Html.element"};
static const lean_object* l_Lean_instReprHtml_repr___closed__0 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprHtml_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHtml_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprHtml_repr___closed__1 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__1_value;
static const lean_ctor_object l_Lean_instReprHtml_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprHtml_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprHtml_repr___closed__2 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__2_value;
static lean_once_cell_t l_Lean_instReprHtml_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprHtml_repr___closed__3;
static lean_once_cell_t l_Lean_instReprHtml_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprHtml_repr___closed__4;
static const lean_string_object l_Lean_instReprHtml_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Html.text"};
static const lean_object* l_Lean_instReprHtml_repr___closed__5 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__5_value;
static const lean_ctor_object l_Lean_instReprHtml_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHtml_repr___closed__5_value)}};
static const lean_object* l_Lean_instReprHtml_repr___closed__6 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprHtml_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprHtml_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprHtml_repr___closed__7 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__7_value;
static const lean_string_object l_Lean_instReprHtml_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.Html.raw"};
static const lean_object* l_Lean_instReprHtml_repr___closed__8 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__8_value;
static const lean_ctor_object l_Lean_instReprHtml_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHtml_repr___closed__8_value)}};
static const lean_object* l_Lean_instReprHtml_repr___closed__9 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__9_value;
static const lean_ctor_object l_Lean_instReprHtml_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprHtml_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprHtml_repr___closed__10 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__10_value;
static const lean_string_object l_Lean_instReprHtml_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.Html.seq"};
static const lean_object* l_Lean_instReprHtml_repr___closed__11 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__11_value;
static const lean_ctor_object l_Lean_instReprHtml_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHtml_repr___closed__11_value)}};
static const lean_object* l_Lean_instReprHtml_repr___closed__12 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__12_value;
static const lean_ctor_object l_Lean_instReprHtml_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprHtml_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprHtml_repr___closed__13 = (const lean_object*)&l_Lean_instReprHtml_repr___closed__13_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprHtml_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprHtml_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprHtml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprHtml_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprHtml___closed__0 = (const lean_object*)&l_Lean_instReprHtml___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprHtml = (const lean_object*)&l_Lean_instReprHtml___closed__0_value;
static const lean_string_object l_Lean_instInhabitedHtml_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedHtml_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedHtml_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedHtml_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedHtml_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedHtml_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedHtml_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedHtml_default = (const lean_object*)&l_Lean_instInhabitedHtml_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedHtml = (const lean_object*)&l_Lean_instInhabitedHtml_default___closed__1_value;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqHtml_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqHtml_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqHtml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqHtml_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqHtml___closed__0 = (const lean_object*)&l_Lean_instBEqHtml___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqHtml = (const lean_object*)&l_Lean_instBEqHtml___closed__0_value;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashableHtml_hash(lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableHtml_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableHtml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableHtml_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableHtml___closed__0 = (const lean_object*)&l_Lean_instHashableHtml___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableHtml = (const lean_object*)&l_Lean_instHashableHtml___closed__0_value;
static const lean_string_object l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140_ = (const lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value;
static const lean_string_object l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Html"};
static const lean_object* l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140_ = (const lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value;
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instImpl___closed__2_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_object* l_Lean_instImpl___closed__2_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value;
LEAN_EXPORT const lean_object* l_Lean_instImpl_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140_ = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value;
LEAN_EXPORT const lean_object* l_Lean_instTypeNameHtml = (const lean_object*)&l_Lean_instImpl___closed__2_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value;
static const lean_array_object l_Lean_Html_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Html_empty___closed__0 = (const lean_object*)&l_Lean_Html_empty___closed__0_value;
static const lean_ctor_object l_Lean_Html_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Html_empty___closed__0_value)}};
static const lean_object* l_Lean_Html_empty___closed__1 = (const lean_object*)&l_Lean_Html_empty___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Html_empty = (const lean_object*)&l_Lean_Html_empty___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Html_isEmpty(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofString(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_instCoeString___lam__0(lean_object*);
static const lean_closure_object l_Lean_Html_instCoeString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_instCoeString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_instCoeString___closed__0 = (const lean_object*)&l_Lean_Html_instCoeString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_instCoeString = (const lean_object*)&l_Lean_Html_instCoeString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_append(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_append, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_instAppend___closed__0 = (const lean_object*)&l_Lean_Html_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_instAppend = (const lean_object*)&l_Lean_Html_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_ofCollection___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_ofCollection___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_ofCollection___redArg___closed__0 = (const lean_object*)&l_Lean_Html_ofCollection___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ofOption___boxed(lean_object*);
static const lean_closure_object l_Lean_Html_instCoeArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_ofArray___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_instCoeArray___closed__0 = (const lean_object*)&l_Lean_Html_instCoeArray___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_instCoeArray = (const lean_object*)&l_Lean_Html_instCoeArray___closed__0_value;
static const lean_closure_object l_Lean_Html_instCoeList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_ofList___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_instCoeList___closed__0 = (const lean_object*)&l_Lean_Html_instCoeList___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_instCoeList = (const lean_object*)&l_Lean_Html_instCoeList___closed__0_value;
static const lean_closure_object l_Lean_Html_instCoeOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_ofOption___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_instCoeOption___closed__0 = (const lean_object*)&l_Lean_Html_instCoeOption___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_instCoeOption = (const lean_object*)&l_Lean_Html_instCoeOption___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1(lean_object*);
static const lean_string_object l_Lean_Html_instToJson_to___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "t"};
static const lean_object* l_Lean_Html_instToJson_to___closed__0 = (const lean_object*)&l_Lean_Html_instToJson_to___closed__0_value;
static const lean_string_object l_Lean_Html_instToJson_to___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Html_instToJson_to___closed__1 = (const lean_object*)&l_Lean_Html_instToJson_to___closed__1_value;
static const lean_string_object l_Lean_Html_instToJson_to___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lean_Html_instToJson_to___closed__2 = (const lean_object*)&l_Lean_Html_instToJson_to___closed__2_value;
static const lean_string_object l_Lean_Html_instToJson_to___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lean_Html_instToJson_to___closed__3 = (const lean_object*)&l_Lean_Html_instToJson_to___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Html_instToJson_to(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Array_map__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Array_map__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__1_splitter(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_instToJson_to, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_instToJson___closed__0 = (const lean_object*)&l_Lean_Html_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_instToJson = (const lean_object*)&l_Lean_Html_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Expected an array of two strings, got: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_instFromJson_from_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Expected a string, got: "};
static const lean_object* l_Lean_Html_instFromJson_from_x3f___closed__0 = (const lean_object*)&l_Lean_Html_instFromJson_from_x3f___closed__0_value;
static const lean_string_object l_Lean_Html_instFromJson_from_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Expected key \"t\" or key \"r\" in: "};
static const lean_object* l_Lean_Html_instFromJson_from_x3f___closed__1 = (const lean_object*)&l_Lean_Html_instFromJson_from_x3f___closed__1_value;
static const lean_string_object l_Lean_Html_instFromJson_from_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Expected a string, an object, or an array, got: "};
static const lean_object* l_Lean_Html_instFromJson_from_x3f___closed__2 = (const lean_object*)&l_Lean_Html_instFromJson_from_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Html_instFromJson_from_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_instFromJson___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to deserialize HTML from JSON "};
static const lean_object* l_Lean_Html_instFromJson___lam__0___closed__0 = (const lean_object*)&l_Lean_Html_instFromJson___lam__0___closed__0_value;
static const lean_string_object l_Lean_Html_instFromJson___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Html_instFromJson___lam__0___closed__1 = (const lean_object*)&l_Lean_Html_instFromJson___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Html_instFromJson___lam__0(lean_object*);
static const lean_closure_object l_Lean_Html_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_instFromJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_instFromJson___closed__0 = (const lean_object*)&l_Lean_Html_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_instFromJson = (const lean_object*)&l_Lean_Html_instFromJson___closed__0_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mkArray"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__2 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__3 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__3_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__4 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__3;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__4_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__5_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0(lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__1_value;
static const lean_array_object l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__2 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0(lean_object*);
static const lean_string_object l_Lean_Html_instQuoteMkStr1_q___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "element"};
static const lean_object* l_Lean_Html_instQuoteMkStr1_q___closed__0 = (const lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__0_value;
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__1_value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__1_value_aux_1),((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 132, 38, 126, 255, 196, 59, 29)}};
static const lean_object* l_Lean_Html_instQuoteMkStr1_q___closed__1 = (const lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__1_value;
static const lean_string_object l_Lean_Html_instQuoteMkStr1_q___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Html_instQuoteMkStr1_q___closed__2 = (const lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__2_value;
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__3_value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__3_value_aux_1),((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__2_value),LEAN_SCALAR_PTR_LITERAL(238, 210, 74, 251, 7, 54, 231, 214)}};
static const lean_object* l_Lean_Html_instQuoteMkStr1_q___closed__3 = (const lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__3_value;
static const lean_string_object l_Lean_Html_instQuoteMkStr1_q___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l_Lean_Html_instQuoteMkStr1_q___closed__4 = (const lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__4_value;
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__5_value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__5_value_aux_1),((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__4_value),LEAN_SCALAR_PTR_LITERAL(180, 158, 139, 217, 84, 192, 171, 23)}};
static const lean_object* l_Lean_Html_instQuoteMkStr1_q___closed__5 = (const lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__5_value;
static const lean_string_object l_Lean_Html_instQuoteMkStr1_q___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "seq"};
static const lean_object* l_Lean_Html_instQuoteMkStr1_q___closed__6 = (const lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__6_value;
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__7_value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_Html_instQuoteMkStr1_q___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__7_value_aux_1),((lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__6_value),LEAN_SCALAR_PTR_LITERAL(187, 159, 6, 14, 33, 55, 218, 203)}};
static const lean_object* l_Lean_Html_instQuoteMkStr1_q___closed__7 = (const lean_object*)&l_Lean_Html_instQuoteMkStr1_q___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_instQuoteMkStr1_q(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Html_instQuoteMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_instQuoteMkStr1_q, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_instQuoteMkStr1___closed__0 = (const lean_object*)&l_Lean_Html_instQuoteMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_instQuoteMkStr1 = (const lean_object*)&l_Lean_Html_instQuoteMkStr1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_rewritePost(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Html_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_tag_7_; lean_object* v_attrs_8_; lean_object* v_children_9_; lean_object* v___x_10_; 
v_tag_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_tag_7_);
v_attrs_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_attrs_8_);
v_children_9_ = lean_ctor_get(v_t_5_, 2);
lean_inc_ref(v_children_9_);
lean_dec_ref_known(v_t_5_, 3);
v___x_10_ = lean_apply_3(v_k_6_, v_tag_7_, v_attrs_8_, v_children_9_);
return v___x_10_;
}
else
{
lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_11_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_11_);
lean_dec_ref(v_t_5_);
v___x_12_ = lean_apply_1(v_k_6_, v_a_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ctorElim(lean_object* v_motive__1_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Html_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ctorElim___boxed(lean_object* v_motive__1_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Html_ctorElim(v_motive__1_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_element_elim___redArg(lean_object* v_t_25_, lean_object* v_element_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Html_ctorElim___redArg(v_t_25_, v_element_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_element_elim(lean_object* v_motive__1_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_element_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Html_ctorElim___redArg(v_t_29_, v_element_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_text_elim___redArg(lean_object* v_t_33_, lean_object* v_text_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Html_ctorElim___redArg(v_t_33_, v_text_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_text_elim(lean_object* v_motive__1_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_text_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Html_ctorElim___redArg(v_t_37_, v_text_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_raw_elim___redArg(lean_object* v_t_41_, lean_object* v_raw_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Html_ctorElim___redArg(v_t_41_, v_raw_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_raw_elim(lean_object* v_motive__1_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_raw_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_Html_ctorElim___redArg(v_t_45_, v_raw_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_seq_elim___redArg(lean_object* v_t_49_, lean_object* v_seq_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Html_ctorElim___redArg(v_t_49_, v_seq_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_seq_elim(lean_object* v_motive__1_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_seq_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Html_ctorElim___redArg(v_t_53_, v_seq_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0_spec__1_spec__4(lean_object* v_x_57_, lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_dec(v_x_57_);
return v_x_58_;
}
else
{
lean_object* v_head_60_; lean_object* v_tail_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_70_; 
v_head_60_ = lean_ctor_get(v_x_59_, 0);
v_tail_61_ = lean_ctor_get(v_x_59_, 1);
v_isSharedCheck_70_ = !lean_is_exclusive(v_x_59_);
if (v_isSharedCheck_70_ == 0)
{
v___x_63_ = v_x_59_;
v_isShared_64_ = v_isSharedCheck_70_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_tail_61_);
lean_inc(v_head_60_);
lean_dec(v_x_59_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_70_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
lean_inc(v_x_57_);
if (v_isShared_64_ == 0)
{
lean_ctor_set_tag(v___x_63_, 5);
lean_ctor_set(v___x_63_, 1, v_x_57_);
lean_ctor_set(v___x_63_, 0, v_x_58_);
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_x_58_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_x_57_);
v___x_66_ = v_reuseFailAlloc_69_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; 
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v_head_60_);
v_x_58_ = v___x_67_;
v_x_59_ = v_tail_61_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0_spec__1(lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_71_) == 0)
{
lean_object* v___x_73_; 
lean_dec(v_x_72_);
v___x_73_ = lean_box(0);
return v___x_73_;
}
else
{
lean_object* v_tail_74_; 
v_tail_74_ = lean_ctor_get(v_x_71_, 1);
if (lean_obj_tag(v_tail_74_) == 0)
{
lean_object* v_head_75_; 
lean_dec(v_x_72_);
v_head_75_ = lean_ctor_get(v_x_71_, 0);
lean_inc(v_head_75_);
lean_dec_ref_known(v_x_71_, 2);
return v_head_75_;
}
else
{
lean_object* v_head_76_; lean_object* v___x_77_; 
lean_inc(v_tail_74_);
v_head_76_ = lean_ctor_get(v_x_71_, 0);
lean_inc(v_head_76_);
lean_dec_ref_known(v_x_71_, 2);
v___x_77_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0_spec__1_spec__4(v_x_72_, v_head_76_, v_tail_74_);
return v___x_77_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__0));
v___x_87_ = lean_string_length(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__5, &l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__5_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__5);
v___x_89_ = lean_nat_to_int(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg(lean_object* v_x_94_){
_start:
{
lean_object* v_fst_95_; lean_object* v_snd_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_120_; 
v_fst_95_ = lean_ctor_get(v_x_94_, 0);
v_snd_96_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_120_ == 0)
{
v___x_98_ = v_x_94_;
v_isShared_99_ = v_isSharedCheck_120_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_snd_96_);
lean_inc(v_fst_95_);
lean_dec(v_x_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_120_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_100_ = l_String_quote(v_fst_95_);
v___x_101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___x_102_ = lean_box(0);
if (v_isShared_99_ == 0)
{
lean_ctor_set_tag(v___x_98_, 1);
lean_ctor_set(v___x_98_, 1, v___x_102_);
lean_ctor_set(v___x_98_, 0, v___x_101_);
v___x_104_ = v___x_98_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_102_);
v___x_104_ = v_reuseFailAlloc_119_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; 
v___x_105_ = l_String_quote(v_snd_96_);
v___x_106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
v___x_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_104_);
v___x_108_ = l_List_reverse___redArg(v___x_107_);
v___x_109_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__3));
v___x_110_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0_spec__1(v___x_108_, v___x_109_);
v___x_111_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__6, &l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__6_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__6);
v___x_112_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__7));
v___x_113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_110_);
v___x_114_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__8));
v___x_115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_111_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_117_);
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__1_spec__3_spec__7(lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_x_123_){
_start:
{
if (lean_obj_tag(v_x_123_) == 0)
{
lean_dec(v_x_121_);
return v_x_122_;
}
else
{
lean_object* v_head_124_; lean_object* v_tail_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_135_; 
v_head_124_ = lean_ctor_get(v_x_123_, 0);
v_tail_125_ = lean_ctor_get(v_x_123_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_x_123_);
if (v_isSharedCheck_135_ == 0)
{
v___x_127_ = v_x_123_;
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_tail_125_);
lean_inc(v_head_124_);
lean_dec(v_x_123_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
lean_inc(v_x_121_);
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 5);
lean_ctor_set(v___x_127_, 1, v_x_121_);
lean_ctor_set(v___x_127_, 0, v_x_122_);
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_x_122_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_x_121_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg(v_head_124_);
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v_x_122_ = v___x_132_;
v_x_123_ = v_tail_125_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__1_spec__3(lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_dec(v_x_136_);
return v_x_137_;
}
else
{
lean_object* v_head_139_; lean_object* v_tail_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_150_; 
v_head_139_ = lean_ctor_get(v_x_138_, 0);
v_tail_140_ = lean_ctor_get(v_x_138_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_150_ == 0)
{
v___x_142_ = v_x_138_;
v_isShared_143_ = v_isSharedCheck_150_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_tail_140_);
lean_inc(v_head_139_);
lean_dec(v_x_138_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_150_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
lean_inc(v_x_136_);
if (v_isShared_143_ == 0)
{
lean_ctor_set_tag(v___x_142_, 5);
lean_ctor_set(v___x_142_, 1, v_x_136_);
lean_ctor_set(v___x_142_, 0, v_x_137_);
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_x_137_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_x_136_);
v___x_145_ = v_reuseFailAlloc_149_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg(v_head_139_);
v___x_147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__1_spec__3_spec__7(v_x_136_, v___x_147_, v_tail_140_);
return v___x_148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__1(lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v___x_153_; 
lean_dec(v_x_152_);
v___x_153_ = lean_box(0);
return v___x_153_;
}
else
{
lean_object* v_tail_154_; 
v_tail_154_ = lean_ctor_get(v_x_151_, 1);
if (lean_obj_tag(v_tail_154_) == 0)
{
lean_object* v_head_155_; lean_object* v___x_156_; 
lean_dec(v_x_152_);
v_head_155_ = lean_ctor_get(v_x_151_, 0);
lean_inc(v_head_155_);
lean_dec_ref_known(v_x_151_, 2);
v___x_156_ = l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg(v_head_155_);
return v___x_156_;
}
else
{
lean_object* v_head_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
lean_inc(v_tail_154_);
v_head_157_ = lean_ctor_get(v_x_151_, 0);
lean_inc(v_head_157_);
lean_dec_ref_known(v_x_151_, 2);
v___x_158_ = l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg(v_head_157_);
v___x_159_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__1_spec__3(v_x_152_, v___x_158_, v_tail_154_);
return v___x_159_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__0));
v___x_163_ = lean_string_length(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__2);
v___x_165_ = lean_nat_to_int(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__0(lean_object* v_xs_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_174_ = lean_array_get_size(v_xs_173_);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_nat_dec_eq(v___x_174_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_177_ = lean_array_to_list(v_xs_173_);
v___x_178_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__3));
v___x_179_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__1(v___x_177_, v___x_178_);
v___x_180_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__3);
v___x_181_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__4));
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_179_);
v___x_183_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__5));
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_180_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = l_Std_Format_fill(v___x_185_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; 
lean_dec_ref(v_xs_173_);
v___x_187_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__7));
return v___x_187_;
}
}
}
static lean_object* _init_l_Lean_instReprHtml_repr___closed__3(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(2u);
v___x_195_ = lean_nat_to_int(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_instReprHtml_repr___closed__4(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_to_int(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4_spec__7_spec__10(lean_object* v_x_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_dec(v_x_216_);
return v_x_217_;
}
else
{
lean_object* v_head_219_; lean_object* v_tail_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_231_; 
v_head_219_ = lean_ctor_get(v_x_218_, 0);
v_tail_220_ = lean_ctor_get(v_x_218_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_231_ == 0)
{
v___x_222_ = v_x_218_;
v_isShared_223_ = v_isSharedCheck_231_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_tail_220_);
lean_inc(v_head_219_);
lean_dec(v_x_218_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_231_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
lean_inc(v_x_216_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 5);
lean_ctor_set(v___x_222_, 1, v_x_216_);
lean_ctor_set(v___x_222_, 0, v_x_217_);
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_x_217_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_x_216_);
v___x_225_ = v_reuseFailAlloc_230_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = l_Lean_instReprHtml_repr(v_head_219_, v___x_226_);
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_225_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v_x_217_ = v___x_228_;
v_x_218_ = v_tail_220_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4_spec__7(lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_dec(v_x_232_);
return v_x_233_;
}
else
{
lean_object* v_head_235_; lean_object* v_tail_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_247_; 
v_head_235_ = lean_ctor_get(v_x_234_, 0);
v_tail_236_ = lean_ctor_get(v_x_234_, 1);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_234_);
if (v_isSharedCheck_247_ == 0)
{
v___x_238_ = v_x_234_;
v_isShared_239_ = v_isSharedCheck_247_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_tail_236_);
lean_inc(v_head_235_);
lean_dec(v_x_234_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_247_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
lean_inc(v_x_232_);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 5);
lean_ctor_set(v___x_238_, 1, v_x_232_);
lean_ctor_set(v___x_238_, 0, v_x_233_);
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_x_233_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_x_232_);
v___x_241_ = v_reuseFailAlloc_246_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = l_Lean_instReprHtml_repr(v_head_235_, v___x_242_);
v___x_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_241_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4_spec__7_spec__10(v_x_232_, v___x_244_, v_tail_236_);
return v___x_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4(lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v___x_250_; 
lean_dec(v_x_249_);
v___x_250_ = lean_box(0);
return v___x_250_;
}
else
{
lean_object* v_tail_251_; 
v_tail_251_ = lean_ctor_get(v_x_248_, 1);
if (lean_obj_tag(v_tail_251_) == 0)
{
lean_object* v_head_252_; lean_object* v___x_253_; 
lean_dec(v_x_249_);
v_head_252_ = lean_ctor_get(v_x_248_, 0);
lean_inc(v_head_252_);
lean_dec_ref_known(v_x_248_, 2);
v___x_253_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4___lam__0(v_head_252_);
return v___x_253_;
}
else
{
lean_object* v_head_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_inc(v_tail_251_);
v_head_254_ = lean_ctor_get(v_x_248_, 0);
lean_inc(v_head_254_);
lean_dec_ref_known(v_x_248_, 2);
v___x_255_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4___lam__0(v_head_254_);
v___x_256_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4_spec__7(v_x_249_, v___x_255_, v_tail_251_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprHtml_repr_spec__1(lean_object* v_xs_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_258_ = lean_array_get_size(v_xs_257_);
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_nat_dec_eq(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_261_ = lean_array_to_list(v_xs_257_);
v___x_262_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg___closed__3));
v___x_263_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4(v___x_261_, v___x_262_);
v___x_264_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__3);
v___x_265_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__4));
v___x_266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_263_);
v___x_267_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__5));
v___x_268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_264_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = l_Std_Format_fill(v___x_269_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; 
lean_dec_ref(v_xs_257_);
v___x_271_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprHtml_repr_spec__0___closed__7));
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprHtml_repr(lean_object* v_x_272_, lean_object* v_prec_273_){
_start:
{
switch(lean_obj_tag(v_x_272_))
{
case 0:
{
lean_object* v_tag_274_; lean_object* v_attrs_275_; lean_object* v_children_276_; lean_object* v___x_277_; lean_object* v___y_279_; uint8_t v___x_295_; 
v_tag_274_ = lean_ctor_get(v_x_272_, 0);
lean_inc_ref(v_tag_274_);
v_attrs_275_ = lean_ctor_get(v_x_272_, 1);
lean_inc_ref(v_attrs_275_);
v_children_276_ = lean_ctor_get(v_x_272_, 2);
lean_inc_ref(v_children_276_);
lean_dec_ref_known(v_x_272_, 3);
v___x_277_ = lean_unsigned_to_nat(1024u);
v___x_295_ = lean_nat_dec_le(v___x_277_, v_prec_273_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l_Lean_instReprHtml_repr___closed__3, &l_Lean_instReprHtml_repr___closed__3_once, _init_l_Lean_instReprHtml_repr___closed__3);
v___y_279_ = v___x_296_;
goto v___jp_278_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Lean_instReprHtml_repr___closed__4, &l_Lean_instReprHtml_repr___closed__4_once, _init_l_Lean_instReprHtml_repr___closed__4);
v___y_279_ = v___x_297_;
goto v___jp_278_;
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_280_ = lean_box(1);
v___x_281_ = ((lean_object*)(l_Lean_instReprHtml_repr___closed__2));
v___x_282_ = l_String_quote(v_tag_274_);
v___x_283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_281_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_280_);
v___x_286_ = l_Array_repr___at___00Lean_instReprHtml_repr_spec__0(v_attrs_275_);
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_280_);
v___x_289_ = l_Lean_instReprHtml_repr(v_children_276_, v___x_277_);
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
lean_inc(v___y_279_);
v___x_291_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_291_, 0, v___y_279_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = 0;
v___x_293_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*1, v___x_292_);
v___x_294_ = l_Repr_addAppParen(v___x_293_, v_prec_273_);
return v___x_294_;
}
}
case 1:
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_318_; 
v_a_298_ = lean_ctor_get(v_x_272_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v_x_272_);
if (v_isSharedCheck_318_ == 0)
{
v___x_300_ = v_x_272_;
v_isShared_301_ = v_isSharedCheck_318_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v_x_272_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_318_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___y_303_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(1024u);
v___x_315_ = lean_nat_dec_le(v___x_314_, v_prec_273_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
v___x_316_ = lean_obj_once(&l_Lean_instReprHtml_repr___closed__3, &l_Lean_instReprHtml_repr___closed__3_once, _init_l_Lean_instReprHtml_repr___closed__3);
v___y_303_ = v___x_316_;
goto v___jp_302_;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Lean_instReprHtml_repr___closed__4, &l_Lean_instReprHtml_repr___closed__4_once, _init_l_Lean_instReprHtml_repr___closed__4);
v___y_303_ = v___x_317_;
goto v___jp_302_;
}
v___jp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = ((lean_object*)(l_Lean_instReprHtml_repr___closed__7));
v___x_305_ = l_String_quote(v_a_298_);
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 3);
lean_ctor_set(v___x_300_, 0, v___x_305_);
v___x_307_ = v___x_300_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_313_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_304_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
lean_inc(v___y_303_);
v___x_309_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_309_, 0, v___y_303_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = 0;
v___x_311_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set_uint8(v___x_311_, sizeof(void*)*1, v___x_310_);
v___x_312_ = l_Repr_addAppParen(v___x_311_, v_prec_273_);
return v___x_312_;
}
}
}
}
case 2:
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_339_; 
v_a_319_ = lean_ctor_get(v_x_272_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_x_272_);
if (v_isSharedCheck_339_ == 0)
{
v___x_321_ = v_x_272_;
v_isShared_322_ = v_isSharedCheck_339_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v_x_272_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_339_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___y_324_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(1024u);
v___x_336_ = lean_nat_dec_le(v___x_335_, v_prec_273_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
v___x_337_ = lean_obj_once(&l_Lean_instReprHtml_repr___closed__3, &l_Lean_instReprHtml_repr___closed__3_once, _init_l_Lean_instReprHtml_repr___closed__3);
v___y_324_ = v___x_337_;
goto v___jp_323_;
}
else
{
lean_object* v___x_338_; 
v___x_338_ = lean_obj_once(&l_Lean_instReprHtml_repr___closed__4, &l_Lean_instReprHtml_repr___closed__4_once, _init_l_Lean_instReprHtml_repr___closed__4);
v___y_324_ = v___x_338_;
goto v___jp_323_;
}
v___jp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = ((lean_object*)(l_Lean_instReprHtml_repr___closed__10));
v___x_326_ = l_String_quote(v_a_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 3);
lean_ctor_set(v___x_321_, 0, v___x_326_);
v___x_328_ = v___x_321_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_334_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_325_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
lean_inc(v___y_324_);
v___x_330_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_330_, 0, v___y_324_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = 0;
v___x_332_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*1, v___x_331_);
v___x_333_ = l_Repr_addAppParen(v___x_332_, v_prec_273_);
return v___x_333_;
}
}
}
}
default: 
{
lean_object* v_a_340_; lean_object* v___y_342_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_a_340_ = lean_ctor_get(v_x_272_, 0);
lean_inc_ref(v_a_340_);
lean_dec_ref_known(v_x_272_, 1);
v___x_350_ = lean_unsigned_to_nat(1024u);
v___x_351_ = lean_nat_dec_le(v___x_350_, v_prec_273_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_obj_once(&l_Lean_instReprHtml_repr___closed__3, &l_Lean_instReprHtml_repr___closed__3_once, _init_l_Lean_instReprHtml_repr___closed__3);
v___y_342_ = v___x_352_;
goto v___jp_341_;
}
else
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Lean_instReprHtml_repr___closed__4, &l_Lean_instReprHtml_repr___closed__4_once, _init_l_Lean_instReprHtml_repr___closed__4);
v___y_342_ = v___x_353_;
goto v___jp_341_;
}
v___jp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_343_ = ((lean_object*)(l_Lean_instReprHtml_repr___closed__13));
v___x_344_ = l_Array_repr___at___00Lean_instReprHtml_repr_spec__1(v_a_340_);
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
lean_inc(v___y_342_);
v___x_346_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_346_, 0, v___y_342_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = 0;
v___x_348_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*1, v___x_347_);
v___x_349_ = l_Repr_addAppParen(v___x_348_, v_prec_273_);
return v___x_349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__1_spec__4___lam__0(lean_object* v___y_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = l_Lean_instReprHtml_repr(v___y_354_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprHtml_repr___boxed(lean_object* v_x_357_, lean_object* v_prec_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_instReprHtml_repr(v_x_357_, v_prec_358_);
lean_dec(v_prec_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__2(lean_object* v_a_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_nat_to_int(v_a_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0(lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___redArg(v_x_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0___boxed(lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Prod_repr___at___00Array_repr___at___00Lean_instReprHtml_repr_spec__0_spec__0(v_x_365_, v_x_366_);
lean_dec(v_x_366_);
return v_res_367_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg(lean_object* v_xs_375_, lean_object* v_ys_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_zero_378_; uint8_t v_isZero_379_; 
v_zero_378_ = lean_unsigned_to_nat(0u);
v_isZero_379_ = lean_nat_dec_eq(v_x_377_, v_zero_378_);
if (v_isZero_379_ == 1)
{
lean_dec(v_x_377_);
return v_isZero_379_;
}
else
{
lean_object* v_one_380_; lean_object* v_n_381_; lean_object* v___x_382_; lean_object* v_fst_383_; lean_object* v_snd_384_; lean_object* v___x_385_; lean_object* v_fst_386_; lean_object* v_snd_387_; uint8_t v___x_388_; 
v_one_380_ = lean_unsigned_to_nat(1u);
v_n_381_ = lean_nat_sub(v_x_377_, v_one_380_);
lean_dec(v_x_377_);
v___x_382_ = lean_array_fget_borrowed(v_xs_375_, v_n_381_);
v_fst_383_ = lean_ctor_get(v___x_382_, 0);
v_snd_384_ = lean_ctor_get(v___x_382_, 1);
v___x_385_ = lean_array_fget_borrowed(v_ys_376_, v_n_381_);
v_fst_386_ = lean_ctor_get(v___x_385_, 0);
v_snd_387_ = lean_ctor_get(v___x_385_, 1);
v___x_388_ = lean_string_dec_eq(v_fst_383_, v_fst_386_);
if (v___x_388_ == 0)
{
lean_dec(v_n_381_);
return v___x_388_;
}
else
{
uint8_t v___x_389_; 
v___x_389_ = lean_string_dec_eq(v_snd_384_, v_snd_387_);
if (v___x_389_ == 0)
{
lean_dec(v_n_381_);
return v___x_389_;
}
else
{
v_x_377_ = v_n_381_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg___boxed(lean_object* v_xs_391_, lean_object* v_ys_392_, lean_object* v_x_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg(v_xs_391_, v_ys_392_, v_x_393_);
lean_dec_ref(v_ys_392_);
lean_dec_ref(v_xs_391_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqHtml_beq(lean_object* v_x_396_, lean_object* v_x_397_){
_start:
{
switch(lean_obj_tag(v_x_396_))
{
case 0:
{
if (lean_obj_tag(v_x_397_) == 0)
{
lean_object* v_tag_398_; lean_object* v_attrs_399_; lean_object* v_children_400_; lean_object* v_tag_401_; lean_object* v_attrs_402_; lean_object* v_children_403_; uint8_t v___x_404_; 
v_tag_398_ = lean_ctor_get(v_x_396_, 0);
v_attrs_399_ = lean_ctor_get(v_x_396_, 1);
v_children_400_ = lean_ctor_get(v_x_396_, 2);
v_tag_401_ = lean_ctor_get(v_x_397_, 0);
v_attrs_402_ = lean_ctor_get(v_x_397_, 1);
v_children_403_ = lean_ctor_get(v_x_397_, 2);
v___x_404_ = lean_string_dec_eq(v_tag_398_, v_tag_401_);
if (v___x_404_ == 0)
{
return v___x_404_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_405_ = lean_array_get_size(v_attrs_399_);
v___x_406_ = lean_array_get_size(v_attrs_402_);
v___x_407_ = lean_nat_dec_eq(v___x_405_, v___x_406_);
if (v___x_407_ == 0)
{
return v___x_407_;
}
else
{
uint8_t v___x_408_; 
v___x_408_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg(v_attrs_399_, v_attrs_402_, v___x_405_);
if (v___x_408_ == 0)
{
return v___x_408_;
}
else
{
v_x_396_ = v_children_400_;
v_x_397_ = v_children_403_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_410_; 
v___x_410_ = 0;
return v___x_410_;
}
}
case 1:
{
if (lean_obj_tag(v_x_397_) == 1)
{
lean_object* v_a_411_; lean_object* v_a_412_; uint8_t v___x_413_; 
v_a_411_ = lean_ctor_get(v_x_396_, 0);
v_a_412_ = lean_ctor_get(v_x_397_, 0);
v___x_413_ = lean_string_dec_eq(v_a_411_, v_a_412_);
return v___x_413_;
}
else
{
uint8_t v___x_414_; 
v___x_414_ = 0;
return v___x_414_;
}
}
case 2:
{
if (lean_obj_tag(v_x_397_) == 2)
{
lean_object* v_a_415_; lean_object* v_a_416_; uint8_t v___x_417_; 
v_a_415_ = lean_ctor_get(v_x_396_, 0);
v_a_416_ = lean_ctor_get(v_x_397_, 0);
v___x_417_ = lean_string_dec_eq(v_a_415_, v_a_416_);
return v___x_417_;
}
else
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
}
default: 
{
if (lean_obj_tag(v_x_397_) == 3)
{
lean_object* v_a_419_; lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_a_419_ = lean_ctor_get(v_x_396_, 0);
v_a_420_ = lean_ctor_get(v_x_397_, 0);
v___x_421_ = lean_array_get_size(v_a_419_);
v___x_422_ = lean_array_get_size(v_a_420_);
v___x_423_ = lean_nat_dec_eq(v___x_421_, v___x_422_);
if (v___x_423_ == 0)
{
return v___x_423_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg(v_a_419_, v_a_420_, v___x_421_);
return v___x_424_;
}
}
else
{
uint8_t v___x_425_; 
v___x_425_ = 0;
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg(lean_object* v_xs_426_, lean_object* v_ys_427_, lean_object* v_x_428_){
_start:
{
lean_object* v_zero_429_; uint8_t v_isZero_430_; 
v_zero_429_ = lean_unsigned_to_nat(0u);
v_isZero_430_ = lean_nat_dec_eq(v_x_428_, v_zero_429_);
if (v_isZero_430_ == 1)
{
lean_dec(v_x_428_);
return v_isZero_430_;
}
else
{
lean_object* v_one_431_; lean_object* v_n_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_one_431_ = lean_unsigned_to_nat(1u);
v_n_432_ = lean_nat_sub(v_x_428_, v_one_431_);
lean_dec(v_x_428_);
v___x_433_ = lean_array_fget_borrowed(v_xs_426_, v_n_432_);
v___x_434_ = lean_array_fget_borrowed(v_ys_427_, v_n_432_);
v___x_435_ = l_Lean_instBEqHtml_beq(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_dec(v_n_432_);
return v___x_435_;
}
else
{
v_x_428_ = v_n_432_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg___boxed(lean_object* v_xs_437_, lean_object* v_ys_438_, lean_object* v_x_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg(v_xs_437_, v_ys_438_, v_x_439_);
lean_dec_ref(v_ys_438_);
lean_dec_ref(v_xs_437_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqHtml_beq___boxed(lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Lean_instBEqHtml_beq(v_x_442_, v_x_443_);
lean_dec_ref(v_x_443_);
lean_dec_ref(v_x_442_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0(lean_object* v_xs_446_, lean_object* v_ys_447_, lean_object* v_hsz_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg(v_xs_446_, v_ys_447_, v_x_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___boxed(lean_object* v_xs_452_, lean_object* v_ys_453_, lean_object* v_hsz_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0(v_xs_452_, v_ys_453_, v_hsz_454_, v_x_455_, v_x_456_);
lean_dec_ref(v_ys_453_);
lean_dec_ref(v_xs_452_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1(lean_object* v_xs_459_, lean_object* v_ys_460_, lean_object* v_hsz_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg(v_xs_459_, v_ys_460_, v_x_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___boxed(lean_object* v_xs_465_, lean_object* v_ys_466_, lean_object* v_hsz_467_, lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1(v_xs_465_, v_ys_466_, v_hsz_467_, v_x_468_, v_x_469_);
lean_dec_ref(v_ys_466_);
lean_dec_ref(v_xs_465_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0(lean_object* v_as_474_, size_t v_i_475_, size_t v_stop_476_, uint64_t v_b_477_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = lean_usize_dec_eq(v_i_475_, v_stop_476_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v_fst_480_; lean_object* v_snd_481_; uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; size_t v___x_486_; size_t v___x_487_; 
v___x_479_ = lean_array_uget_borrowed(v_as_474_, v_i_475_);
v_fst_480_ = lean_ctor_get(v___x_479_, 0);
v_snd_481_ = lean_ctor_get(v___x_479_, 1);
v___x_482_ = lean_string_hash(v_fst_480_);
v___x_483_ = lean_string_hash(v_snd_481_);
v___x_484_ = lean_uint64_mix_hash(v___x_482_, v___x_483_);
v___x_485_ = lean_uint64_mix_hash(v_b_477_, v___x_484_);
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_i_475_, v___x_486_);
v_i_475_ = v___x_487_;
v_b_477_ = v___x_485_;
goto _start;
}
else
{
return v_b_477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0___boxed(lean_object* v_as_489_, lean_object* v_i_490_, lean_object* v_stop_491_, lean_object* v_b_492_){
_start:
{
size_t v_i_boxed_493_; size_t v_stop_boxed_494_; uint64_t v_b_boxed_495_; uint64_t v_res_496_; lean_object* v_r_497_; 
v_i_boxed_493_ = lean_unbox_usize(v_i_490_);
lean_dec(v_i_490_);
v_stop_boxed_494_ = lean_unbox_usize(v_stop_491_);
lean_dec(v_stop_491_);
v_b_boxed_495_ = lean_unbox_uint64(v_b_492_);
lean_dec_ref(v_b_492_);
v_res_496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0(v_as_489_, v_i_boxed_493_, v_stop_boxed_494_, v_b_boxed_495_);
lean_dec_ref(v_as_489_);
v_r_497_ = lean_box_uint64(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableHtml_hash(lean_object* v_x_498_){
_start:
{
switch(lean_obj_tag(v_x_498_))
{
case 0:
{
lean_object* v_tag_499_; lean_object* v_attrs_500_; lean_object* v_children_501_; uint64_t v___x_502_; uint64_t v___x_503_; uint64_t v___x_504_; uint64_t v___y_506_; uint64_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_tag_499_ = lean_ctor_get(v_x_498_, 0);
v_attrs_500_ = lean_ctor_get(v_x_498_, 1);
v_children_501_ = lean_ctor_get(v_x_498_, 2);
v___x_502_ = 0ULL;
v___x_503_ = lean_string_hash(v_tag_499_);
v___x_504_ = lean_uint64_mix_hash(v___x_502_, v___x_503_);
v___x_510_ = 7ULL;
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_array_get_size(v_attrs_500_);
v___x_513_ = lean_nat_dec_lt(v___x_511_, v___x_512_);
if (v___x_513_ == 0)
{
v___y_506_ = v___x_510_;
goto v___jp_505_;
}
else
{
size_t v___x_514_; size_t v___x_515_; uint64_t v___x_516_; 
v___x_514_ = ((size_t)0ULL);
v___x_515_ = lean_usize_of_nat(v___x_512_);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0(v_attrs_500_, v___x_514_, v___x_515_, v___x_510_);
v___y_506_ = v___x_516_;
goto v___jp_505_;
}
v___jp_505_:
{
uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v___x_509_; 
v___x_507_ = lean_uint64_mix_hash(v___x_504_, v___y_506_);
v___x_508_ = l_Lean_instHashableHtml_hash(v_children_501_);
v___x_509_ = lean_uint64_mix_hash(v___x_507_, v___x_508_);
return v___x_509_;
}
}
case 1:
{
lean_object* v_a_517_; uint64_t v___x_518_; uint64_t v___x_519_; uint64_t v___x_520_; 
v_a_517_ = lean_ctor_get(v_x_498_, 0);
v___x_518_ = 1ULL;
v___x_519_ = lean_string_hash(v_a_517_);
v___x_520_ = lean_uint64_mix_hash(v___x_518_, v___x_519_);
return v___x_520_;
}
case 2:
{
lean_object* v_a_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; 
v_a_521_ = lean_ctor_get(v_x_498_, 0);
v___x_522_ = 2ULL;
v___x_523_ = lean_string_hash(v_a_521_);
v___x_524_ = lean_uint64_mix_hash(v___x_522_, v___x_523_);
return v___x_524_;
}
default: 
{
lean_object* v_a_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_a_525_ = lean_ctor_get(v_x_498_, 0);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = lean_array_get_size(v_a_525_);
v___x_528_ = lean_nat_dec_lt(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
uint64_t v___x_529_; 
v___x_529_ = 12882348691112465364ULL;
return v___x_529_;
}
else
{
uint64_t v___x_530_; uint64_t v___x_531_; size_t v___x_532_; size_t v___x_533_; uint64_t v___x_534_; uint64_t v___x_535_; 
v___x_530_ = 3ULL;
v___x_531_ = 7ULL;
v___x_532_ = ((size_t)0ULL);
v___x_533_ = lean_usize_of_nat(v___x_527_);
v___x_534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1(v_a_525_, v___x_532_, v___x_533_, v___x_531_);
v___x_535_ = lean_uint64_mix_hash(v___x_530_, v___x_534_);
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1(lean_object* v_as_536_, size_t v_i_537_, size_t v_stop_538_, uint64_t v_b_539_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = lean_usize_dec_eq(v_i_537_, v_stop_538_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; uint64_t v___x_542_; uint64_t v___x_543_; size_t v___x_544_; size_t v___x_545_; 
v___x_541_ = lean_array_uget_borrowed(v_as_536_, v_i_537_);
v___x_542_ = l_Lean_instHashableHtml_hash(v___x_541_);
v___x_543_ = lean_uint64_mix_hash(v_b_539_, v___x_542_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_537_, v___x_544_);
v_i_537_ = v___x_545_;
v_b_539_ = v___x_543_;
goto _start;
}
else
{
return v_b_539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1___boxed(lean_object* v_as_547_, lean_object* v_i_548_, lean_object* v_stop_549_, lean_object* v_b_550_){
_start:
{
size_t v_i_boxed_551_; size_t v_stop_boxed_552_; uint64_t v_b_boxed_553_; uint64_t v_res_554_; lean_object* v_r_555_; 
v_i_boxed_551_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_stop_boxed_552_ = lean_unbox_usize(v_stop_549_);
lean_dec(v_stop_549_);
v_b_boxed_553_ = lean_unbox_uint64(v_b_550_);
lean_dec_ref(v_b_550_);
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1(v_as_547_, v_i_boxed_551_, v_stop_boxed_552_, v_b_boxed_553_);
lean_dec_ref(v_as_547_);
v_r_555_ = lean_box_uint64(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableHtml_hash___boxed(lean_object* v_x_556_){
_start:
{
uint64_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Lean_instHashableHtml_hash(v_x_556_);
lean_dec_ref(v_x_556_);
v_r_558_ = lean_box_uint64(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_isEmpty(lean_object* v_x_573_){
_start:
{
lean_object* v_s_575_; 
switch(lean_obj_tag(v_x_573_))
{
case 0:
{
uint8_t v___x_579_; 
v___x_579_ = 0;
return v___x_579_;
}
case 3:
{
lean_object* v_a_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_a_580_ = lean_ctor_get(v_x_573_, 0);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_array_get_size(v_a_580_);
v___x_583_ = lean_nat_dec_lt(v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
uint8_t v___x_584_; 
v___x_584_ = 1;
return v___x_584_;
}
else
{
if (v___x_583_ == 0)
{
return v___x_583_;
}
else
{
size_t v___x_585_; size_t v___x_586_; uint8_t v___x_587_; 
v___x_585_ = ((size_t)0ULL);
v___x_586_ = lean_usize_of_nat(v___x_582_);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0(v_a_580_, v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
return v___x_583_;
}
else
{
uint8_t v___x_588_; 
v___x_588_ = 0;
return v___x_588_;
}
}
}
}
default: 
{
lean_object* v_a_589_; 
v_a_589_ = lean_ctor_get(v_x_573_, 0);
v_s_575_ = v_a_589_;
goto v___jp_574_;
}
}
v___jp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_576_ = lean_string_utf8_byte_size(v_s_575_);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_nat_dec_eq(v___x_576_, v___x_577_);
return v___x_578_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0(lean_object* v_as_590_, size_t v_i_591_, size_t v_stop_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = lean_usize_dec_eq(v_i_591_, v_stop_592_);
if (v___x_593_ == 0)
{
lean_object* v_val_594_; uint8_t v___x_595_; 
v_val_594_ = lean_array_uget_borrowed(v_as_590_, v_i_591_);
v___x_595_ = l_Lean_Html_isEmpty(v_val_594_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; 
v___x_596_ = 1;
return v___x_596_;
}
else
{
size_t v___x_597_; size_t v___x_598_; 
v___x_597_ = ((size_t)1ULL);
v___x_598_ = lean_usize_add(v_i_591_, v___x_597_);
v_i_591_ = v___x_598_;
goto _start;
}
}
else
{
uint8_t v___x_600_; 
v___x_600_ = 0;
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0___boxed(lean_object* v_as_601_, lean_object* v_i_602_, lean_object* v_stop_603_){
_start:
{
size_t v_i_boxed_604_; size_t v_stop_boxed_605_; uint8_t v_res_606_; lean_object* v_r_607_; 
v_i_boxed_604_ = lean_unbox_usize(v_i_602_);
lean_dec(v_i_602_);
v_stop_boxed_605_ = lean_unbox_usize(v_stop_603_);
lean_dec(v_stop_603_);
v_res_606_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0(v_as_601_, v_i_boxed_604_, v_stop_boxed_605_);
lean_dec_ref(v_as_601_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_isEmpty___boxed(lean_object* v_x_608_){
_start:
{
uint8_t v_res_609_; lean_object* v_r_610_; 
v_res_609_ = l_Lean_Html_isEmpty(v_x_608_);
lean_dec_ref(v_x_608_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__3_splitter___redArg(lean_object* v_x_611_, lean_object* v_h__1_612_, lean_object* v_h__2_613_, lean_object* v_h__3_614_, lean_object* v_h__4_615_){
_start:
{
switch(lean_obj_tag(v_x_611_))
{
case 0:
{
lean_object* v_tag_616_; lean_object* v_attrs_617_; lean_object* v_children_618_; lean_object* v___x_619_; 
lean_dec(v_h__3_614_);
lean_dec(v_h__2_613_);
lean_dec(v_h__1_612_);
v_tag_616_ = lean_ctor_get(v_x_611_, 0);
lean_inc_ref(v_tag_616_);
v_attrs_617_ = lean_ctor_get(v_x_611_, 1);
lean_inc_ref(v_attrs_617_);
v_children_618_ = lean_ctor_get(v_x_611_, 2);
lean_inc_ref(v_children_618_);
lean_dec_ref_known(v_x_611_, 3);
v___x_619_ = lean_apply_3(v_h__4_615_, v_tag_616_, v_attrs_617_, v_children_618_);
return v___x_619_;
}
case 1:
{
lean_object* v_a_620_; lean_object* v___x_621_; 
lean_dec(v_h__4_615_);
lean_dec(v_h__3_614_);
lean_dec(v_h__1_612_);
v_a_620_ = lean_ctor_get(v_x_611_, 0);
lean_inc_ref(v_a_620_);
lean_dec_ref_known(v_x_611_, 1);
v___x_621_ = lean_apply_1(v_h__2_613_, v_a_620_);
return v___x_621_;
}
case 2:
{
lean_object* v_a_622_; lean_object* v___x_623_; 
lean_dec(v_h__4_615_);
lean_dec(v_h__2_613_);
lean_dec(v_h__1_612_);
v_a_622_ = lean_ctor_get(v_x_611_, 0);
lean_inc_ref(v_a_622_);
lean_dec_ref_known(v_x_611_, 1);
v___x_623_ = lean_apply_1(v_h__3_614_, v_a_622_);
return v___x_623_;
}
default: 
{
lean_object* v_a_624_; lean_object* v___x_625_; 
lean_dec(v_h__4_615_);
lean_dec(v_h__3_614_);
lean_dec(v_h__2_613_);
v_a_624_ = lean_ctor_get(v_x_611_, 0);
lean_inc_ref(v_a_624_);
lean_dec_ref_known(v_x_611_, 1);
v___x_625_ = lean_apply_1(v_h__1_612_, v_a_624_);
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__3_splitter(lean_object* v_motive_626_, lean_object* v_x_627_, lean_object* v_h__1_628_, lean_object* v_h__2_629_, lean_object* v_h__3_630_, lean_object* v_h__4_631_){
_start:
{
switch(lean_obj_tag(v_x_627_))
{
case 0:
{
lean_object* v_tag_632_; lean_object* v_attrs_633_; lean_object* v_children_634_; lean_object* v___x_635_; 
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_tag_632_ = lean_ctor_get(v_x_627_, 0);
lean_inc_ref(v_tag_632_);
v_attrs_633_ = lean_ctor_get(v_x_627_, 1);
lean_inc_ref(v_attrs_633_);
v_children_634_ = lean_ctor_get(v_x_627_, 2);
lean_inc_ref(v_children_634_);
lean_dec_ref_known(v_x_627_, 3);
v___x_635_ = lean_apply_3(v_h__4_631_, v_tag_632_, v_attrs_633_, v_children_634_);
return v___x_635_;
}
case 1:
{
lean_object* v_a_636_; lean_object* v___x_637_; 
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__1_628_);
v_a_636_ = lean_ctor_get(v_x_627_, 0);
lean_inc_ref(v_a_636_);
lean_dec_ref_known(v_x_627_, 1);
v___x_637_ = lean_apply_1(v_h__2_629_, v_a_636_);
return v___x_637_;
}
case 2:
{
lean_object* v_a_638_; lean_object* v___x_639_; 
lean_dec(v_h__4_631_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_a_638_ = lean_ctor_get(v_x_627_, 0);
lean_inc_ref(v_a_638_);
lean_dec_ref_known(v_x_627_, 1);
v___x_639_ = lean_apply_1(v_h__3_630_, v_a_638_);
return v___x_639_;
}
default: 
{
lean_object* v_a_640_; lean_object* v___x_641_; 
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
v_a_640_ = lean_ctor_get(v_x_627_, 0);
lean_inc_ref(v_a_640_);
lean_dec_ref_known(v_x_627_, 1);
v___x_641_ = lean_apply_1(v_h__1_628_, v_a_640_);
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter___redArg(lean_object* v_x_642_, lean_object* v_h__1_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = lean_apply_2(v_h__1_643_, v_x_642_, lean_box(0));
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter(lean_object* v_a_645_, lean_object* v_motive_646_, lean_object* v_x_647_, lean_object* v_h__1_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = lean_apply_2(v_h__1_648_, v_x_647_, lean_box(0));
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter___boxed(lean_object* v_a_650_, lean_object* v_motive_651_, lean_object* v_x_652_, lean_object* v_h__1_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter(v_a_650_, v_motive_651_, v_x_652_, v_h__1_653_);
lean_dec_ref(v_a_650_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofString(uint8_t v_escape_655_, lean_object* v_a_656_){
_start:
{
if (v_escape_655_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_657_, 0, v_a_656_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; 
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v_a_656_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofString___boxed(lean_object* v_escape_659_, lean_object* v_a_660_){
_start:
{
uint8_t v_escape_boxed_661_; lean_object* v_res_662_; 
v_escape_boxed_661_ = lean_unbox(v_escape_659_);
v_res_662_ = l_Lean_Html_ofString(v_escape_boxed_661_, v_a_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instCoeString___lam__0(lean_object* v_a_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v_a_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_append(lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_667_) == 3)
{
if (lean_obj_tag(v_x_668_) == 3)
{
lean_object* v_a_669_; lean_object* v_a_670_; uint8_t v___x_671_; 
v_a_669_ = lean_ctor_get(v_x_667_, 0);
v_a_670_ = lean_ctor_get(v_x_668_, 0);
v___x_671_ = l_Lean_Html_isEmpty(v_x_667_);
if (v___x_671_ == 0)
{
uint8_t v___x_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
lean_inc_ref(v_a_670_);
v___x_672_ = l_Lean_Html_isEmpty(v_x_668_);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_668_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v_x_668_, 0);
lean_dec(v_unused_681_);
v___x_674_ = v_x_668_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_dec(v_x_668_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
if (v___x_672_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_678_; 
lean_inc_ref(v_a_669_);
lean_dec_ref_known(v_x_667_, 1);
v___x_676_ = l_Array_append___redArg(v_a_669_, v_a_670_);
lean_dec_ref(v_a_670_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
else
{
lean_del_object(v___x_674_);
lean_dec_ref(v_a_670_);
return v_x_667_;
}
}
}
else
{
lean_dec_ref_known(v_x_667_, 1);
return v_x_668_;
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_693_; 
v_a_682_ = lean_ctor_get(v_x_667_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v_x_667_);
if (v_isSharedCheck_693_ == 0)
{
v___x_684_ = v_x_667_;
v_isShared_685_ = v_isSharedCheck_693_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v_x_667_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_693_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_array_get_size(v_a_682_);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = lean_nat_dec_eq(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_array_push(v_a_682_, v_x_668_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_689_);
v___x_691_ = v___x_684_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
else
{
lean_del_object(v___x_684_);
lean_dec_ref(v_a_682_);
return v_x_668_;
}
}
}
}
else
{
if (lean_obj_tag(v_x_668_) == 3)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_708_; 
v_a_694_ = lean_ctor_get(v_x_668_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v_x_668_);
if (v_isSharedCheck_708_ == 0)
{
v___x_696_ = v_x_668_;
v_isShared_697_ = v_isSharedCheck_708_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v_x_668_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_708_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_698_ = lean_array_get_size(v_a_694_);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_nat_dec_eq(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_mk_empty_array_with_capacity(v___x_701_);
v___x_703_ = lean_array_push(v___x_702_, v_x_667_);
v___x_704_ = l_Array_append___redArg(v___x_703_, v_a_694_);
lean_dec_ref(v_a_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_704_);
v___x_706_ = v___x_696_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
else
{
lean_del_object(v___x_696_);
lean_dec_ref(v_a_694_);
return v_x_667_;
}
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_709_ = lean_unsigned_to_nat(2u);
v___x_710_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___x_711_ = lean_array_push(v___x_710_, v_x_667_);
v___x_712_ = lean_array_push(v___x_711_, v_x_668_);
v___x_713_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___redArg___lam__0(lean_object* v_h_716_, lean_object* v_____s_717_){
_start:
{
lean_object* v_out_718_; lean_object* v___x_719_; 
v_out_718_ = l_Lean_Html_append(v_____s_717_, v_h_716_);
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v_out_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___redArg(lean_object* v_inst_721_, lean_object* v_hs_722_){
_start:
{
lean_object* v___f_723_; lean_object* v_out_724_; lean_object* v___x_725_; 
v___f_723_ = ((lean_object*)(l_Lean_Html_ofCollection___redArg___closed__0));
v_out_724_ = ((lean_object*)(l_Lean_Html_empty));
v___x_725_ = lean_apply_4(v_inst_721_, lean_box(0), v_hs_722_, v_out_724_, v___f_723_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection(lean_object* v_00_u03c1_726_, lean_object* v_inst_727_, lean_object* v_hs_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Html_ofCollection___redArg(v_inst_727_, v_hs_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0(lean_object* v_as_730_, size_t v_sz_731_, size_t v_i_732_, lean_object* v_b_733_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = lean_usize_dec_lt(v_i_732_, v_sz_731_);
if (v___x_734_ == 0)
{
return v_b_733_;
}
else
{
lean_object* v_a_735_; lean_object* v_out_736_; size_t v___x_737_; size_t v___x_738_; 
v_a_735_ = lean_array_uget_borrowed(v_as_730_, v_i_732_);
lean_inc(v_a_735_);
v_out_736_ = l_Lean_Html_append(v_b_733_, v_a_735_);
v___x_737_ = ((size_t)1ULL);
v___x_738_ = lean_usize_add(v_i_732_, v___x_737_);
v_i_732_ = v___x_738_;
v_b_733_ = v_out_736_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0___boxed(lean_object* v_as_740_, lean_object* v_sz_741_, lean_object* v_i_742_, lean_object* v_b_743_){
_start:
{
size_t v_sz_boxed_744_; size_t v_i_boxed_745_; lean_object* v_res_746_; 
v_sz_boxed_744_ = lean_unbox_usize(v_sz_741_);
lean_dec(v_sz_741_);
v_i_boxed_745_ = lean_unbox_usize(v_i_742_);
lean_dec(v_i_742_);
v_res_746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0(v_as_740_, v_sz_boxed_744_, v_i_boxed_745_, v_b_743_);
lean_dec_ref(v_as_740_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0(lean_object* v_hs_747_){
_start:
{
lean_object* v_out_748_; size_t v_sz_749_; size_t v___x_750_; lean_object* v___x_751_; 
v_out_748_ = ((lean_object*)(l_Lean_Html_empty));
v_sz_749_ = lean_array_size(v_hs_747_);
v___x_750_ = ((size_t)0ULL);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0(v_hs_747_, v_sz_749_, v___x_750_, v_out_748_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0___boxed(lean_object* v_hs_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0(v_hs_752_);
lean_dec_ref(v_hs_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofArray(lean_object* v_hs_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0(v_hs_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofArray___boxed(lean_object* v_hs_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Html_ofArray(v_hs_756_);
lean_dec_ref(v_hs_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(lean_object* v_as_x27_758_, lean_object* v_b_759_){
_start:
{
if (lean_obj_tag(v_as_x27_758_) == 0)
{
return v_b_759_;
}
else
{
lean_object* v_head_760_; lean_object* v_tail_761_; lean_object* v_out_762_; 
v_head_760_ = lean_ctor_get(v_as_x27_758_, 0);
v_tail_761_ = lean_ctor_get(v_as_x27_758_, 1);
lean_inc(v_head_760_);
v_out_762_ = l_Lean_Html_append(v_b_759_, v_head_760_);
v_as_x27_758_ = v_tail_761_;
v_b_759_ = v_out_762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg___boxed(lean_object* v_as_x27_764_, lean_object* v_b_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(v_as_x27_764_, v_b_765_);
lean_dec(v_as_x27_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0(lean_object* v_hs_767_){
_start:
{
lean_object* v_out_768_; lean_object* v___x_769_; 
v_out_768_ = ((lean_object*)(l_Lean_Html_empty));
v___x_769_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(v_hs_767_, v_out_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0___boxed(lean_object* v_hs_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0(v_hs_770_);
lean_dec(v_hs_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofList(lean_object* v_hs_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0(v_hs_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofList___boxed(lean_object* v_hs_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Html_ofList(v_hs_774_);
lean_dec(v_hs_774_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0(lean_object* v_as_776_, lean_object* v_as_x27_777_, lean_object* v_b_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(v_as_x27_777_, v_b_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___boxed(lean_object* v_as_781_, lean_object* v_as_x27_782_, lean_object* v_b_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0(v_as_781_, v_as_x27_782_, v_b_783_, v_a_784_);
lean_dec(v_as_x27_782_);
lean_dec(v_as_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofOption(lean_object* v_h_x3f_786_){
_start:
{
if (lean_obj_tag(v_h_x3f_786_) == 0)
{
lean_object* v___x_787_; 
v___x_787_ = ((lean_object*)(l_Lean_Html_empty));
return v___x_787_;
}
else
{
lean_object* v_val_788_; 
v_val_788_ = lean_ctor_get(v_h_x3f_786_, 0);
lean_inc(v_val_788_);
return v_val_788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofOption___boxed(lean_object* v_h_x3f_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Html_ofOption(v_h_x3f_789_);
lean_dec(v_h_x3f_789_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0(size_t v_sz_797_, size_t v_i_798_, lean_object* v_bs_799_){
_start:
{
uint8_t v___x_800_; 
v___x_800_ = lean_usize_dec_lt(v_i_798_, v_sz_797_);
if (v___x_800_ == 0)
{
return v_bs_799_;
}
else
{
lean_object* v_v_801_; lean_object* v_fst_802_; lean_object* v_snd_803_; lean_object* v___x_804_; lean_object* v_bs_x27_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; 
v_v_801_ = lean_array_uget_borrowed(v_bs_799_, v_i_798_);
v_fst_802_ = lean_ctor_get(v_v_801_, 0);
lean_inc(v_fst_802_);
v_snd_803_ = lean_ctor_get(v_v_801_, 1);
lean_inc(v_snd_803_);
v___x_804_ = lean_unsigned_to_nat(0u);
v_bs_x27_805_ = lean_array_uset(v_bs_799_, v_i_798_, v___x_804_);
v___x_806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_806_, 0, v_fst_802_);
v___x_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_807_, 0, v_snd_803_);
v___x_808_ = lean_unsigned_to_nat(2u);
v___x_809_ = lean_mk_empty_array_with_capacity(v___x_808_);
v___x_810_ = lean_array_push(v___x_809_, v___x_806_);
v___x_811_ = lean_array_push(v___x_810_, v___x_807_);
v___x_812_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = ((size_t)1ULL);
v___x_814_ = lean_usize_add(v_i_798_, v___x_813_);
v___x_815_ = lean_array_uset(v_bs_x27_805_, v_i_798_, v___x_812_);
v_i_798_ = v___x_814_;
v_bs_799_ = v___x_815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0___boxed(lean_object* v_sz_817_, lean_object* v_i_818_, lean_object* v_bs_819_){
_start:
{
size_t v_sz_boxed_820_; size_t v_i_boxed_821_; lean_object* v_res_822_; 
v_sz_boxed_820_ = lean_unbox_usize(v_sz_817_);
lean_dec(v_sz_817_);
v_i_boxed_821_ = lean_unbox_usize(v_i_818_);
lean_dec(v_i_818_);
v_res_822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0(v_sz_boxed_820_, v_i_boxed_821_, v_bs_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1(size_t v_sz_823_, size_t v_i_824_, lean_object* v_bs_825_){
_start:
{
uint8_t v___x_826_; 
v___x_826_ = lean_usize_dec_lt(v_i_824_, v_sz_823_);
if (v___x_826_ == 0)
{
return v_bs_825_;
}
else
{
lean_object* v_v_827_; lean_object* v___x_828_; lean_object* v_bs_x27_829_; size_t v___x_830_; size_t v___x_831_; lean_object* v___x_832_; 
v_v_827_ = lean_array_uget(v_bs_825_, v_i_824_);
v___x_828_ = lean_unsigned_to_nat(0u);
v_bs_x27_829_ = lean_array_uset(v_bs_825_, v_i_824_, v___x_828_);
v___x_830_ = ((size_t)1ULL);
v___x_831_ = lean_usize_add(v_i_824_, v___x_830_);
v___x_832_ = lean_array_uset(v_bs_x27_829_, v_i_824_, v_v_827_);
v_i_824_ = v___x_831_;
v_bs_825_ = v___x_832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1___boxed(lean_object* v_sz_834_, lean_object* v_i_835_, lean_object* v_bs_836_){
_start:
{
size_t v_sz_boxed_837_; size_t v_i_boxed_838_; lean_object* v_res_839_; 
v_sz_boxed_837_ = lean_unbox_usize(v_sz_834_);
lean_dec(v_sz_834_);
v_i_boxed_838_ = lean_unbox_usize(v_i_835_);
lean_dec(v_i_835_);
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1(v_sz_boxed_837_, v_i_boxed_838_, v_bs_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1(lean_object* v_a_840_){
_start:
{
size_t v_sz_841_; size_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_sz_841_ = lean_array_size(v_a_840_);
v___x_842_ = ((size_t)0ULL);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1(v_sz_841_, v___x_842_, v_a_840_);
v___x_844_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instToJson_to(lean_object* v_x_849_){
_start:
{
switch(lean_obj_tag(v_x_849_))
{
case 0:
{
lean_object* v_tag_850_; lean_object* v_attrs_851_; lean_object* v_children_852_; size_t v_sz_853_; size_t v___x_854_; lean_object* v_attrs_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_tag_850_ = lean_ctor_get(v_x_849_, 0);
lean_inc_ref(v_tag_850_);
v_attrs_851_ = lean_ctor_get(v_x_849_, 1);
lean_inc_ref(v_attrs_851_);
v_children_852_ = lean_ctor_get(v_x_849_, 2);
lean_inc_ref(v_children_852_);
lean_dec_ref_known(v_x_849_, 3);
v_sz_853_ = lean_array_size(v_attrs_851_);
v___x_854_ = ((size_t)0ULL);
v_attrs_855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0(v_sz_853_, v___x_854_, v_attrs_851_);
v___x_856_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__0));
v___x_857_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_857_, 0, v_tag_850_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__1));
v___x_860_ = l_Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1(v_attrs_855_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__2));
v___x_863_ = l_Lean_Html_instToJson_to(v_children_852_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_box(0);
v___x_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_861_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_858_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_Json_mkObj(v___x_868_);
lean_dec_ref_known(v___x_868_, 2);
return v___x_869_;
}
case 1:
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_870_ = lean_ctor_get(v_x_849_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v_x_849_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v_x_849_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set_tag(v___x_872_, 3);
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
case 2:
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_890_; 
v_a_878_ = lean_ctor_get(v_x_849_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_890_ == 0)
{
v___x_880_ = v_x_849_;
v_isShared_881_ = v_isSharedCheck_890_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v_x_849_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_890_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__3));
if (v_isShared_881_ == 0)
{
lean_ctor_set_tag(v___x_880_, 3);
v___x_884_ = v___x_880_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_878_);
v___x_884_ = v_reuseFailAlloc_889_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_882_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = lean_box(0);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_Json_mkObj(v___x_887_);
lean_dec_ref_known(v___x_887_, 2);
return v___x_888_;
}
}
}
default: 
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_901_; 
v_a_891_ = lean_ctor_get(v_x_849_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_901_ == 0)
{
v___x_893_ = v_x_849_;
v_isShared_894_ = v_isSharedCheck_901_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v_x_849_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_901_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
size_t v_sz_895_; size_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v_sz_895_ = lean_array_size(v_a_891_);
v___x_896_ = ((size_t)0ULL);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2(v_sz_895_, v___x_896_, v_a_891_);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 4);
lean_ctor_set(v___x_893_, 0, v___x_897_);
v___x_899_ = v___x_893_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2(size_t v_sz_902_, size_t v_i_903_, lean_object* v_bs_904_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = lean_usize_dec_lt(v_i_903_, v_sz_902_);
if (v___x_905_ == 0)
{
return v_bs_904_;
}
else
{
lean_object* v_v_906_; lean_object* v___x_907_; lean_object* v_bs_x27_908_; lean_object* v___x_909_; size_t v___x_910_; size_t v___x_911_; lean_object* v___x_912_; 
v_v_906_ = lean_array_uget(v_bs_904_, v_i_903_);
v___x_907_ = lean_unsigned_to_nat(0u);
v_bs_x27_908_ = lean_array_uset(v_bs_904_, v_i_903_, v___x_907_);
v___x_909_ = l_Lean_Html_instToJson_to(v_v_906_);
v___x_910_ = ((size_t)1ULL);
v___x_911_ = lean_usize_add(v_i_903_, v___x_910_);
v___x_912_ = lean_array_uset(v_bs_x27_908_, v_i_903_, v___x_909_);
v_i_903_ = v___x_911_;
v_bs_904_ = v___x_912_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2___boxed(lean_object* v_sz_914_, lean_object* v_i_915_, lean_object* v_bs_916_){
_start:
{
size_t v_sz_boxed_917_; size_t v_i_boxed_918_; lean_object* v_res_919_; 
v_sz_boxed_917_ = lean_unbox_usize(v_sz_914_);
lean_dec(v_sz_914_);
v_i_boxed_918_ = lean_unbox_usize(v_i_915_);
lean_dec(v_i_915_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2(v_sz_boxed_917_, v_i_boxed_918_, v_bs_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__3_splitter___redArg(lean_object* v_x_920_, lean_object* v_h__1_921_, lean_object* v_h__2_922_, lean_object* v_h__3_923_, lean_object* v_h__4_924_){
_start:
{
switch(lean_obj_tag(v_x_920_))
{
case 0:
{
lean_object* v_tag_925_; lean_object* v_attrs_926_; lean_object* v_children_927_; lean_object* v___x_928_; 
lean_dec(v_h__4_924_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_tag_925_ = lean_ctor_get(v_x_920_, 0);
lean_inc_ref(v_tag_925_);
v_attrs_926_ = lean_ctor_get(v_x_920_, 1);
lean_inc_ref(v_attrs_926_);
v_children_927_ = lean_ctor_get(v_x_920_, 2);
lean_inc_ref(v_children_927_);
lean_dec_ref_known(v_x_920_, 3);
v___x_928_ = lean_apply_3(v_h__3_923_, v_tag_925_, v_attrs_926_, v_children_927_);
return v___x_928_;
}
case 1:
{
lean_object* v_a_929_; lean_object* v___x_930_; 
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
v_a_929_ = lean_ctor_get(v_x_920_, 0);
lean_inc_ref(v_a_929_);
lean_dec_ref_known(v_x_920_, 1);
v___x_930_ = lean_apply_1(v_h__1_921_, v_a_929_);
return v___x_930_;
}
case 2:
{
lean_object* v_a_931_; lean_object* v___x_932_; 
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__1_921_);
v_a_931_ = lean_ctor_get(v_x_920_, 0);
lean_inc_ref(v_a_931_);
lean_dec_ref_known(v_x_920_, 1);
v___x_932_ = lean_apply_1(v_h__2_922_, v_a_931_);
return v___x_932_;
}
default: 
{
lean_object* v_a_933_; lean_object* v___x_934_; 
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_a_933_ = lean_ctor_get(v_x_920_, 0);
lean_inc_ref(v_a_933_);
lean_dec_ref_known(v_x_920_, 1);
v___x_934_ = lean_apply_1(v_h__4_924_, v_a_933_);
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__3_splitter(lean_object* v_motive_935_, lean_object* v_x_936_, lean_object* v_h__1_937_, lean_object* v_h__2_938_, lean_object* v_h__3_939_, lean_object* v_h__4_940_){
_start:
{
switch(lean_obj_tag(v_x_936_))
{
case 0:
{
lean_object* v_tag_941_; lean_object* v_attrs_942_; lean_object* v_children_943_; lean_object* v___x_944_; 
lean_dec(v_h__4_940_);
lean_dec(v_h__2_938_);
lean_dec(v_h__1_937_);
v_tag_941_ = lean_ctor_get(v_x_936_, 0);
lean_inc_ref(v_tag_941_);
v_attrs_942_ = lean_ctor_get(v_x_936_, 1);
lean_inc_ref(v_attrs_942_);
v_children_943_ = lean_ctor_get(v_x_936_, 2);
lean_inc_ref(v_children_943_);
lean_dec_ref_known(v_x_936_, 3);
v___x_944_ = lean_apply_3(v_h__3_939_, v_tag_941_, v_attrs_942_, v_children_943_);
return v___x_944_;
}
case 1:
{
lean_object* v_a_945_; lean_object* v___x_946_; 
lean_dec(v_h__4_940_);
lean_dec(v_h__3_939_);
lean_dec(v_h__2_938_);
v_a_945_ = lean_ctor_get(v_x_936_, 0);
lean_inc_ref(v_a_945_);
lean_dec_ref_known(v_x_936_, 1);
v___x_946_ = lean_apply_1(v_h__1_937_, v_a_945_);
return v___x_946_;
}
case 2:
{
lean_object* v_a_947_; lean_object* v___x_948_; 
lean_dec(v_h__4_940_);
lean_dec(v_h__3_939_);
lean_dec(v_h__1_937_);
v_a_947_ = lean_ctor_get(v_x_936_, 0);
lean_inc_ref(v_a_947_);
lean_dec_ref_known(v_x_936_, 1);
v___x_948_ = lean_apply_1(v_h__2_938_, v_a_947_);
return v___x_948_;
}
default: 
{
lean_object* v_a_949_; lean_object* v___x_950_; 
lean_dec(v_h__3_939_);
lean_dec(v_h__2_938_);
lean_dec(v_h__1_937_);
v_a_949_ = lean_ctor_get(v_x_936_, 0);
lean_inc_ref(v_a_949_);
lean_dec_ref_known(v_x_936_, 1);
v___x_950_ = lean_apply_1(v_h__4_940_, v_a_949_);
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_951_, lean_object* v_h__1_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = lean_apply_2(v_h__1_952_, v_x_951_, lean_box(0));
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_954_, lean_object* v_P_955_, lean_object* v_motive_956_, lean_object* v_x_957_, lean_object* v_h__1_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = lean_apply_2(v_h__1_958_, v_x_957_, lean_box(0));
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__1_splitter___redArg(lean_object* v_x_960_, lean_object* v_h__1_961_){
_start:
{
lean_object* v_fst_962_; lean_object* v_snd_963_; lean_object* v___x_964_; 
v_fst_962_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_fst_962_);
v_snd_963_ = lean_ctor_get(v_x_960_, 1);
lean_inc(v_snd_963_);
lean_dec_ref(v_x_960_);
v___x_964_ = lean_apply_2(v_h__1_961_, v_fst_962_, v_snd_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__1_splitter(lean_object* v_motive_965_, lean_object* v_x_966_, lean_object* v_h__1_967_){
_start:
{
lean_object* v_fst_968_; lean_object* v_snd_969_; lean_object* v___x_970_; 
v_fst_968_ = lean_ctor_get(v_x_966_, 0);
lean_inc(v_fst_968_);
v_snd_969_ = lean_ctor_get(v_x_966_, 1);
lean_inc(v_snd_969_);
lean_dec_ref(v_x_966_);
v___x_970_ = lean_apply_2(v_h__1_967_, v_fst_968_, v_snd_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(lean_object* v_t_973_, lean_object* v_k_974_){
_start:
{
if (lean_obj_tag(v_t_973_) == 0)
{
lean_object* v_k_975_; lean_object* v_v_976_; lean_object* v_l_977_; lean_object* v_r_978_; uint8_t v___x_979_; 
v_k_975_ = lean_ctor_get(v_t_973_, 1);
v_v_976_ = lean_ctor_get(v_t_973_, 2);
v_l_977_ = lean_ctor_get(v_t_973_, 3);
v_r_978_ = lean_ctor_get(v_t_973_, 4);
v___x_979_ = lean_string_compare(v_k_974_, v_k_975_);
switch(v___x_979_)
{
case 0:
{
v_t_973_ = v_l_977_;
goto _start;
}
case 1:
{
lean_object* v___x_981_; 
lean_inc(v_v_976_);
v___x_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_981_, 0, v_v_976_);
return v___x_981_;
}
default: 
{
v_t_973_ = v_r_978_;
goto _start;
}
}
}
else
{
lean_object* v___x_983_; 
v___x_983_ = lean_box(0);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg___boxed(lean_object* v_t_984_, lean_object* v_k_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_t_984_, v_k_985_);
lean_dec_ref(v_k_985_);
lean_dec(v_t_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3(size_t v_sz_987_, size_t v_i_988_, lean_object* v_bs_989_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = lean_usize_dec_lt(v_i_988_, v_sz_987_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_991_, 0, v_bs_989_);
return v___x_991_;
}
else
{
lean_object* v_v_992_; lean_object* v___x_993_; lean_object* v_bs_x27_994_; size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v_v_992_ = lean_array_uget(v_bs_989_, v_i_988_);
v___x_993_ = lean_unsigned_to_nat(0u);
v_bs_x27_994_ = lean_array_uset(v_bs_989_, v_i_988_, v___x_993_);
v___x_995_ = ((size_t)1ULL);
v___x_996_ = lean_usize_add(v_i_988_, v___x_995_);
v___x_997_ = lean_array_uset(v_bs_x27_994_, v_i_988_, v_v_992_);
v_i_988_ = v___x_996_;
v_bs_989_ = v___x_997_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_999_, lean_object* v_i_1000_, lean_object* v_bs_1001_){
_start:
{
size_t v_sz_boxed_1002_; size_t v_i_boxed_1003_; lean_object* v_res_1004_; 
v_sz_boxed_1002_ = lean_unbox_usize(v_sz_999_);
lean_dec(v_sz_999_);
v_i_boxed_1003_ = lean_unbox_usize(v_i_1000_);
lean_dec(v_i_1000_);
v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3(v_sz_boxed_1002_, v_i_boxed_1003_, v_bs_1001_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2(lean_object* v_x_1007_){
_start:
{
if (lean_obj_tag(v_x_1007_) == 4)
{
lean_object* v_elems_1008_; size_t v_sz_1009_; size_t v___x_1010_; lean_object* v___x_1011_; 
v_elems_1008_ = lean_ctor_get(v_x_1007_, 0);
lean_inc_ref(v_elems_1008_);
lean_dec_ref_known(v_x_1007_, 1);
v_sz_1009_ = lean_array_size(v_elems_1008_);
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3(v_sz_1009_, v___x_1010_, v_elems_1008_);
return v___x_1011_;
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1012_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__0));
v___x_1013_ = lean_unsigned_to_nat(80u);
v___x_1014_ = l_Lean_Json_pretty(v_x_1007_, v___x_1013_);
v___x_1015_ = lean_string_append(v___x_1012_, v___x_1014_);
lean_dec_ref(v___x_1014_);
v___x_1016_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__1));
v___x_1017_ = lean_string_append(v___x_1015_, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2(lean_object* v_j_1019_, lean_object* v_k_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = l_Lean_Json_getObjValD(v_j_1019_, v_k_1020_);
v___x_1022_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2(v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2___boxed(lean_object* v_j_1023_, lean_object* v_k_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2(v_j_1023_, v_k_1024_);
lean_dec_ref(v_k_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3(size_t v_sz_1027_, size_t v_i_1028_, lean_object* v_bs_1029_){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = lean_usize_dec_lt(v_i_1028_, v_sz_1027_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_bs_1029_);
return v___x_1031_;
}
else
{
lean_object* v_v_1032_; 
v_v_1032_ = lean_array_uget_borrowed(v_bs_1029_, v_i_1028_);
if (lean_obj_tag(v_v_1032_) == 4)
{
lean_object* v_elems_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_elems_1038_ = lean_ctor_get(v_v_1032_, 0);
v___x_1039_ = lean_array_get_size(v_elems_1038_);
v___x_1040_ = lean_unsigned_to_nat(2u);
v___x_1041_ = lean_nat_dec_eq(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_inc_ref(v_v_1032_);
lean_dec_ref(v_bs_1029_);
goto v___jp_1033_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = lean_array_fget_borrowed(v_elems_1038_, v___x_1042_);
if (lean_obj_tag(v___x_1043_) == 3)
{
lean_object* v_s_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_s_1044_ = lean_ctor_get(v___x_1043_, 0);
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_array_fget_borrowed(v_elems_1038_, v___x_1045_);
if (lean_obj_tag(v___x_1046_) == 3)
{
lean_object* v_s_1047_; lean_object* v_bs_x27_1048_; lean_object* v___x_1049_; size_t v___x_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
lean_inc_ref(v_s_1044_);
v_s_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc_ref(v_s_1047_);
v_bs_x27_1048_ = lean_array_uset(v_bs_1029_, v_i_1028_, v___x_1042_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_s_1044_);
lean_ctor_set(v___x_1049_, 1, v_s_1047_);
v___x_1050_ = ((size_t)1ULL);
v___x_1051_ = lean_usize_add(v_i_1028_, v___x_1050_);
v___x_1052_ = lean_array_uset(v_bs_x27_1048_, v_i_1028_, v___x_1049_);
v_i_1028_ = v___x_1051_;
v_bs_1029_ = v___x_1052_;
goto _start;
}
else
{
lean_inc_ref(v_v_1032_);
lean_dec_ref(v_bs_1029_);
goto v___jp_1033_;
}
}
else
{
lean_inc_ref(v_v_1032_);
lean_dec_ref(v_bs_1029_);
goto v___jp_1033_;
}
}
}
else
{
lean_inc(v_v_1032_);
lean_dec_ref(v_bs_1029_);
goto v___jp_1033_;
}
v___jp_1033_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3___closed__0));
v___x_1035_ = l_Lean_Json_compress(v_v_1032_);
v___x_1036_ = lean_string_append(v___x_1034_, v___x_1035_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3___boxed(lean_object* v_sz_1054_, lean_object* v_i_1055_, lean_object* v_bs_1056_){
_start:
{
size_t v_sz_boxed_1057_; size_t v_i_boxed_1058_; lean_object* v_res_1059_; 
v_sz_boxed_1057_ = lean_unbox_usize(v_sz_1054_);
lean_dec(v_sz_1054_);
v_i_boxed_1058_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_res_1059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3(v_sz_boxed_1057_, v_i_boxed_1058_, v_bs_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instFromJson_from_x3f(lean_object* v_x_1063_){
_start:
{
switch(lean_obj_tag(v_x_1063_))
{
case 3:
{
lean_object* v_s_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1072_; 
v_s_1064_ = lean_ctor_get(v_x_1063_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_x_1063_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1066_ = v_x_1063_;
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_s_1064_);
lean_dec(v_x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 1);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_s_1064_);
v___x_1069_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
}
case 4:
{
lean_object* v_elems_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1099_; 
v_elems_1073_ = lean_ctor_get(v_x_1063_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_x_1063_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1075_ = v_x_1063_;
v_isShared_1076_ = v_isSharedCheck_1099_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_elems_1073_);
lean_dec(v_x_1063_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1099_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
size_t v_sz_1077_; size_t v___x_1078_; lean_object* v___x_1079_; 
v_sz_1077_ = lean_array_size(v_elems_1073_);
v___x_1078_ = ((size_t)0ULL);
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0(v_sz_1077_, v___x_1078_, v_elems_1073_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_del_object(v___x_1075_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1098_; 
v_a_1088_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1090_ = v___x_1079_;
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1079_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 3);
lean_ctor_set(v___x_1075_, 0, v_a_1088_);
v___x_1093_ = v___x_1075_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1093_);
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
}
case 5:
{
lean_object* v_kvPairs_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_kvPairs_1100_ = lean_ctor_get(v_x_1063_, 0);
v___x_1101_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__0));
v___x_1102_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_kvPairs_1100_, v___x_1101_);
if (lean_obj_tag(v___x_1102_) == 1)
{
lean_object* v_val_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1158_; 
v_val_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1158_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_val_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1158_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
if (lean_obj_tag(v_val_1103_) == 3)
{
lean_object* v_s_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_del_object(v___x_1105_);
v_s_1107_ = lean_ctor_get(v_val_1103_, 0);
lean_inc_ref(v_s_1107_);
lean_dec_ref_known(v_val_1103_, 1);
v___x_1108_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__1));
lean_inc_ref(v_x_1063_);
v___x_1109_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2(v_x_1063_, v___x_1108_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec_ref(v_s_1107_);
lean_dec_ref_known(v_x_1063_, 1);
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v_a_1118_; size_t v_sz_1119_; size_t v___x_1120_; lean_object* v___x_1121_; 
v_a_1118_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1109_, 1);
v_sz_1119_ = lean_array_size(v_a_1118_);
v___x_1120_ = ((size_t)0ULL);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3(v_sz_1119_, v___x_1120_, v_a_1118_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v_s_1107_);
lean_dec_ref_known(v_x_1063_, 1);
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_a_1130_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1131_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__2));
v___x_1132_ = l_Lean_Json_getObjVal_x3f(v_x_1063_, v___x_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_a_1130_);
lean_dec_ref(v_s_1107_);
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1142_ = l_Lean_Html_instFromJson_from_x3f(v_a_1141_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_dec(v_a_1130_);
lean_dec_ref(v_s_1107_);
return v___x_1142_;
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1147_, 0, v_s_1107_);
lean_ctor_set(v___x_1147_, 1, v_a_1130_);
lean_ctor_set(v___x_1147_, 2, v_a_1143_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
lean_dec_ref_known(v_x_1063_, 1);
v___x_1152_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__0));
v___x_1153_ = l_Lean_Json_compress(v_val_1103_);
v___x_1154_ = lean_string_append(v___x_1152_, v___x_1153_);
lean_dec_ref(v___x_1153_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1154_);
v___x_1156_ = v___x_1105_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec(v___x_1102_);
v___x_1159_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__3));
v___x_1160_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_kvPairs_1100_, v___x_1159_);
if (lean_obj_tag(v___x_1160_) == 1)
{
lean_object* v_val_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref_known(v_x_1063_, 1);
v_val_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1182_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_val_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1182_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
if (lean_obj_tag(v_val_1161_) == 3)
{
lean_object* v_s_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1175_; 
v_s_1165_ = lean_ctor_get(v_val_1161_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_val_1161_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1167_ = v_val_1161_;
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_s_1165_);
lean_dec(v_val_1161_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 2);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_s_1165_);
v___x_1170_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1170_);
v___x_1172_ = v___x_1163_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1176_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__0));
v___x_1177_ = l_Lean_Json_compress(v_val_1161_);
v___x_1178_ = lean_string_append(v___x_1176_, v___x_1177_);
lean_dec_ref(v___x_1177_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set_tag(v___x_1163_, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1178_);
v___x_1180_ = v___x_1163_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v___x_1160_);
v___x_1183_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__1));
v___x_1184_ = l_Lean_Json_compress(v_x_1063_);
v___x_1185_ = lean_string_append(v___x_1183_, v___x_1184_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
}
default: 
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1187_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__2));
v___x_1188_ = l_Lean_Json_compress(v_x_1063_);
v___x_1189_ = lean_string_append(v___x_1187_, v___x_1188_);
lean_dec_ref(v___x_1188_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0(size_t v_sz_1191_, size_t v_i_1192_, lean_object* v_bs_1193_){
_start:
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_usize_dec_lt(v_i_1192_, v_sz_1191_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_bs_1193_);
return v___x_1195_;
}
else
{
lean_object* v_v_1196_; lean_object* v___x_1197_; 
v_v_1196_ = lean_array_uget_borrowed(v_bs_1193_, v_i_1192_);
lean_inc(v_v_1196_);
v___x_1197_ = l_Lean_Html_instFromJson_from_x3f(v_v_1196_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v_bs_1193_);
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1207_; lean_object* v_bs_x27_1208_; size_t v___x_1209_; size_t v___x_1210_; lean_object* v___x_1211_; 
v_a_1206_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1207_ = lean_unsigned_to_nat(0u);
v_bs_x27_1208_ = lean_array_uset(v_bs_1193_, v_i_1192_, v___x_1207_);
v___x_1209_ = ((size_t)1ULL);
v___x_1210_ = lean_usize_add(v_i_1192_, v___x_1209_);
v___x_1211_ = lean_array_uset(v_bs_x27_1208_, v_i_1192_, v_a_1206_);
v_i_1192_ = v___x_1210_;
v_bs_1193_ = v___x_1211_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0___boxed(lean_object* v_sz_1213_, lean_object* v_i_1214_, lean_object* v_bs_1215_){
_start:
{
size_t v_sz_boxed_1216_; size_t v_i_boxed_1217_; lean_object* v_res_1218_; 
v_sz_boxed_1216_ = lean_unbox_usize(v_sz_1213_);
lean_dec(v_sz_1213_);
v_i_boxed_1217_ = lean_unbox_usize(v_i_1214_);
lean_dec(v_i_1214_);
v_res_1218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0(v_sz_boxed_1216_, v_i_boxed_1217_, v_bs_1215_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1(lean_object* v_00_u03b4_1219_, lean_object* v_t_1220_, lean_object* v_k_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_t_1220_, v_k_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___boxed(lean_object* v_00_u03b4_1223_, lean_object* v_t_1224_, lean_object* v_k_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1(v_00_u03b4_1223_, v_t_1224_, v_k_1225_);
lean_dec_ref(v_k_1225_);
lean_dec(v_t_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instFromJson___lam__0(lean_object* v_j_1229_){
_start:
{
lean_object* v___x_1230_; 
lean_inc(v_j_1229_);
v___x_1230_ = l_Lean_Html_instFromJson_from_x3f(v_j_1229_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1244_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1244_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1244_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1235_ = ((lean_object*)(l_Lean_Html_instFromJson___lam__0___closed__0));
v___x_1236_ = l_Lean_Json_compress(v_j_1229_);
v___x_1237_ = lean_string_append(v___x_1235_, v___x_1236_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = ((lean_object*)(l_Lean_Html_instFromJson___lam__0___closed__1));
v___x_1239_ = lean_string_append(v___x_1237_, v___x_1238_);
v___x_1240_ = lean_string_append(v___x_1239_, v_a_1231_);
lean_dec(v_a_1231_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1240_);
v___x_1242_ = v___x_1233_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
else
{
lean_dec(v_j_1229_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1(lean_object* v_xs_1254_, lean_object* v_i_1255_, lean_object* v_args_1256_){
_start:
{
lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = lean_array_get_size(v_xs_1254_);
v___x_1258_ = lean_nat_dec_lt(v_i_1255_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec(v_i_1255_);
v___x_1259_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__0));
v___x_1260_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__1));
v___x_1261_ = l_Nat_reprFast(v___x_1257_);
v___x_1262_ = lean_string_append(v___x_1260_, v___x_1261_);
lean_dec_ref(v___x_1261_);
v___x_1263_ = l_Lean_Name_mkStr2(v___x_1259_, v___x_1262_);
v___x_1264_ = l_Lean_Syntax_mkCApp(v___x_1263_, v_args_1256_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v_fst_1266_; lean_object* v_snd_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1265_ = lean_array_fget_borrowed(v_xs_1254_, v_i_1255_);
v_fst_1266_ = lean_ctor_get(v___x_1265_, 0);
v_snd_1267_ = lean_ctor_get(v___x_1265_, 1);
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = lean_nat_add(v_i_1255_, v___x_1268_);
lean_dec(v_i_1255_);
v___x_1270_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__4));
v___x_1271_ = lean_box(2);
lean_inc(v_fst_1266_);
v___x_1272_ = l_Lean_Syntax_mkStrLit(v_fst_1266_, v___x_1271_);
lean_inc(v_snd_1267_);
v___x_1273_ = l_Lean_Syntax_mkStrLit(v_snd_1267_, v___x_1271_);
v___x_1274_ = lean_unsigned_to_nat(2u);
v___x_1275_ = lean_mk_empty_array_with_capacity(v___x_1274_);
v___x_1276_ = lean_array_push(v___x_1275_, v___x_1272_);
v___x_1277_ = lean_array_push(v___x_1276_, v___x_1273_);
v___x_1278_ = l_Lean_Syntax_mkCApp(v___x_1270_, v___x_1277_);
v___x_1279_ = lean_array_push(v_args_1256_, v___x_1278_);
v_i_1255_ = v___x_1269_;
v_args_1256_ = v___x_1279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___boxed(lean_object* v_xs_1281_, lean_object* v_i_1282_, lean_object* v_args_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1(v_xs_1281_, v_i_1282_, v_args_1283_);
lean_dec_ref(v_xs_1281_);
return v_res_1284_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__2));
v___x_1291_ = l_Lean_mkCIdent(v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0(lean_object* v_x_1296_){
_start:
{
if (lean_obj_tag(v_x_1296_) == 0)
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__3);
return v___x_1297_;
}
else
{
lean_object* v_head_1298_; lean_object* v_tail_1299_; lean_object* v_fst_1300_; lean_object* v_snd_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_head_1298_ = lean_ctor_get(v_x_1296_, 0);
lean_inc(v_head_1298_);
v_tail_1299_ = lean_ctor_get(v_x_1296_, 1);
lean_inc(v_tail_1299_);
lean_dec_ref_known(v_x_1296_, 2);
v_fst_1300_ = lean_ctor_get(v_head_1298_, 0);
lean_inc(v_fst_1300_);
v_snd_1301_ = lean_ctor_get(v_head_1298_, 1);
lean_inc(v_snd_1301_);
lean_dec(v_head_1298_);
v___x_1302_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__5));
v___x_1303_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__4));
v___x_1304_ = lean_box(2);
v___x_1305_ = l_Lean_Syntax_mkStrLit(v_fst_1300_, v___x_1304_);
v___x_1306_ = l_Lean_Syntax_mkStrLit(v_snd_1301_, v___x_1304_);
v___x_1307_ = lean_unsigned_to_nat(2u);
v___x_1308_ = lean_mk_empty_array_with_capacity(v___x_1307_);
lean_inc_ref(v___x_1308_);
v___x_1309_ = lean_array_push(v___x_1308_, v___x_1305_);
v___x_1310_ = lean_array_push(v___x_1309_, v___x_1306_);
v___x_1311_ = l_Lean_Syntax_mkCApp(v___x_1303_, v___x_1310_);
v___x_1312_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0(v_tail_1299_);
v___x_1313_ = lean_array_push(v___x_1308_, v___x_1311_);
v___x_1314_ = lean_array_push(v___x_1313_, v___x_1312_);
v___x_1315_ = l_Lean_Syntax_mkCApp(v___x_1302_, v___x_1314_);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0(lean_object* v_xs_1322_){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1323_ = lean_array_get_size(v_xs_1322_);
v___x_1324_ = lean_unsigned_to_nat(8u);
v___x_1325_ = lean_nat_dec_le(v___x_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1326_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__1));
v___x_1327_ = lean_array_to_list(v_xs_1322_);
v___x_1328_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0(v___x_1327_);
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_mk_empty_array_with_capacity(v___x_1329_);
v___x_1331_ = lean_array_push(v___x_1330_, v___x_1328_);
v___x_1332_ = l_Lean_Syntax_mkCApp(v___x_1326_, v___x_1331_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__2));
v___x_1335_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1(v_xs_1322_, v___x_1333_, v___x_1334_);
lean_dec_ref(v_xs_1322_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__3(lean_object* v_x_1356_){
_start:
{
if (lean_obj_tag(v_x_1356_) == 0)
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__3);
return v___x_1357_;
}
else
{
lean_object* v_head_1358_; lean_object* v_tail_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_head_1358_ = lean_ctor_get(v_x_1356_, 0);
lean_inc(v_head_1358_);
v_tail_1359_ = lean_ctor_get(v_x_1356_, 1);
lean_inc(v_tail_1359_);
lean_dec_ref_known(v_x_1356_, 2);
v___x_1360_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__5));
v___x_1361_ = l_Lean_Html_instQuoteMkStr1_q(v_head_1358_);
v___x_1362_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__3(v_tail_1359_);
v___x_1363_ = lean_unsigned_to_nat(2u);
v___x_1364_ = lean_mk_empty_array_with_capacity(v___x_1363_);
v___x_1365_ = lean_array_push(v___x_1364_, v___x_1361_);
v___x_1366_ = lean_array_push(v___x_1365_, v___x_1362_);
v___x_1367_ = l_Lean_Syntax_mkCApp(v___x_1360_, v___x_1366_);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1(lean_object* v_xs_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1369_ = lean_array_get_size(v_xs_1368_);
v___x_1370_ = lean_unsigned_to_nat(8u);
v___x_1371_ = lean_nat_dec_le(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1372_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__1));
v___x_1373_ = lean_array_to_list(v_xs_1368_);
v___x_1374_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__3(v___x_1373_);
v___x_1375_ = lean_unsigned_to_nat(1u);
v___x_1376_ = lean_mk_empty_array_with_capacity(v___x_1375_);
v___x_1377_ = lean_array_push(v___x_1376_, v___x_1374_);
v___x_1378_ = l_Lean_Syntax_mkCApp(v___x_1372_, v___x_1377_);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__2));
v___x_1381_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4(v_xs_1368_, v___x_1379_, v___x_1380_);
lean_dec_ref(v_xs_1368_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instQuoteMkStr1_q(lean_object* v_x_1382_){
_start:
{
switch(lean_obj_tag(v_x_1382_))
{
case 0:
{
lean_object* v_tag_1383_; lean_object* v_attrs_1384_; lean_object* v_children_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_tag_1383_ = lean_ctor_get(v_x_1382_, 0);
lean_inc_ref(v_tag_1383_);
v_attrs_1384_ = lean_ctor_get(v_x_1382_, 1);
lean_inc_ref(v_attrs_1384_);
v_children_1385_ = lean_ctor_get(v_x_1382_, 2);
lean_inc_ref(v_children_1385_);
lean_dec_ref_known(v_x_1382_, 3);
v___x_1386_ = ((lean_object*)(l_Lean_Html_instQuoteMkStr1_q___closed__1));
v___x_1387_ = lean_box(2);
v___x_1388_ = l_Lean_Syntax_mkStrLit(v_tag_1383_, v___x_1387_);
v___x_1389_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0(v_attrs_1384_);
v___x_1390_ = l_Lean_Html_instQuoteMkStr1_q(v_children_1385_);
v___x_1391_ = lean_unsigned_to_nat(3u);
v___x_1392_ = lean_mk_empty_array_with_capacity(v___x_1391_);
v___x_1393_ = lean_array_push(v___x_1392_, v___x_1388_);
v___x_1394_ = lean_array_push(v___x_1393_, v___x_1389_);
v___x_1395_ = lean_array_push(v___x_1394_, v___x_1390_);
v___x_1396_ = l_Lean_Syntax_mkCApp(v___x_1386_, v___x_1395_);
return v___x_1396_;
}
case 1:
{
lean_object* v_a_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_a_1397_ = lean_ctor_get(v_x_1382_, 0);
lean_inc_ref(v_a_1397_);
lean_dec_ref_known(v_x_1382_, 1);
v___x_1398_ = ((lean_object*)(l_Lean_Html_instQuoteMkStr1_q___closed__3));
v___x_1399_ = lean_box(2);
v___x_1400_ = l_Lean_Syntax_mkStrLit(v_a_1397_, v___x_1399_);
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = lean_mk_empty_array_with_capacity(v___x_1401_);
v___x_1403_ = lean_array_push(v___x_1402_, v___x_1400_);
v___x_1404_ = l_Lean_Syntax_mkCApp(v___x_1398_, v___x_1403_);
return v___x_1404_;
}
case 2:
{
lean_object* v_a_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v_a_1405_ = lean_ctor_get(v_x_1382_, 0);
lean_inc_ref(v_a_1405_);
lean_dec_ref_known(v_x_1382_, 1);
v___x_1406_ = ((lean_object*)(l_Lean_Html_instQuoteMkStr1_q___closed__5));
v___x_1407_ = lean_box(2);
v___x_1408_ = l_Lean_Syntax_mkStrLit(v_a_1405_, v___x_1407_);
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1410_ = lean_mk_empty_array_with_capacity(v___x_1409_);
v___x_1411_ = lean_array_push(v___x_1410_, v___x_1408_);
v___x_1412_ = l_Lean_Syntax_mkCApp(v___x_1406_, v___x_1411_);
return v___x_1412_;
}
default: 
{
lean_object* v_a_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_a_1413_ = lean_ctor_get(v_x_1382_, 0);
lean_inc_ref(v_a_1413_);
lean_dec_ref_known(v_x_1382_, 1);
v___x_1414_ = ((lean_object*)(l_Lean_Html_instQuoteMkStr1_q___closed__7));
v___x_1415_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1(v_a_1413_);
v___x_1416_ = lean_unsigned_to_nat(1u);
v___x_1417_ = lean_mk_empty_array_with_capacity(v___x_1416_);
v___x_1418_ = lean_array_push(v___x_1417_, v___x_1415_);
v___x_1419_ = l_Lean_Syntax_mkCApp(v___x_1414_, v___x_1418_);
return v___x_1419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4(lean_object* v_xs_1420_, lean_object* v_i_1421_, lean_object* v_args_1422_){
_start:
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = lean_array_get_size(v_xs_1420_);
v___x_1424_ = lean_nat_dec_lt(v_i_1421_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec(v_i_1421_);
v___x_1425_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__0));
v___x_1426_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__1));
v___x_1427_ = l_Nat_reprFast(v___x_1423_);
v___x_1428_ = lean_string_append(v___x_1426_, v___x_1427_);
lean_dec_ref(v___x_1427_);
v___x_1429_ = l_Lean_Name_mkStr2(v___x_1425_, v___x_1428_);
v___x_1430_ = l_Lean_Syntax_mkCApp(v___x_1429_, v_args_1422_);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_nat_add(v_i_1421_, v___x_1431_);
v___x_1433_ = lean_array_fget_borrowed(v_xs_1420_, v_i_1421_);
lean_dec(v_i_1421_);
lean_inc(v___x_1433_);
v___x_1434_ = l_Lean_Html_instQuoteMkStr1_q(v___x_1433_);
v___x_1435_ = lean_array_push(v_args_1422_, v___x_1434_);
v_i_1421_ = v___x_1432_;
v_args_1422_ = v___x_1435_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4___boxed(lean_object* v_xs_1437_, lean_object* v_i_1438_, lean_object* v_args_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4(v_xs_1437_, v_i_1438_, v_args_1439_);
lean_dec_ref(v_xs_1437_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg___lam__0(lean_object* v_tag_1443_, lean_object* v_attrs_1444_, lean_object* v_fn_1445_, lean_object* v_children_x27_1446_){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1447_, 0, v_tag_1443_);
lean_ctor_set(v___x_1447_, 1, v_attrs_1444_);
lean_ctor_set(v___x_1447_, 2, v_children_x27_1446_);
v___x_1448_ = lean_apply_1(v_fn_1445_, v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg___lam__1(lean_object* v_fn_1449_, lean_object* v_s_x27_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_s_x27_1450_);
v___x_1452_ = lean_apply_1(v_fn_1449_, v___x_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg(lean_object* v_inst_1453_, lean_object* v_fn_1454_, lean_object* v_x_1455_){
_start:
{
switch(lean_obj_tag(v_x_1455_))
{
case 0:
{
lean_object* v_toBind_1456_; lean_object* v_tag_1457_; lean_object* v_attrs_1458_; lean_object* v_children_1459_; lean_object* v___f_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_toBind_1456_ = lean_ctor_get(v_inst_1453_, 1);
lean_inc(v_toBind_1456_);
v_tag_1457_ = lean_ctor_get(v_x_1455_, 0);
lean_inc_ref(v_tag_1457_);
v_attrs_1458_ = lean_ctor_get(v_x_1455_, 1);
lean_inc_ref(v_attrs_1458_);
v_children_1459_ = lean_ctor_get(v_x_1455_, 2);
lean_inc_ref(v_children_1459_);
lean_dec_ref_known(v_x_1455_, 3);
lean_inc(v_fn_1454_);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_Html_rewritePostM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1460_, 0, v_tag_1457_);
lean_closure_set(v___f_1460_, 1, v_attrs_1458_);
lean_closure_set(v___f_1460_, 2, v_fn_1454_);
v___x_1461_ = l_Lean_Html_rewritePostM___redArg(v_inst_1453_, v_fn_1454_, v_children_1459_);
v___x_1462_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1461_, v___f_1460_);
return v___x_1462_;
}
case 3:
{
lean_object* v_toBind_1463_; lean_object* v_a_1464_; lean_object* v___f_1465_; lean_object* v___x_1466_; size_t v_sz_1467_; size_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_toBind_1463_ = lean_ctor_get(v_inst_1453_, 1);
lean_inc(v_toBind_1463_);
v_a_1464_ = lean_ctor_get(v_x_1455_, 0);
lean_inc_ref(v_a_1464_);
lean_dec_ref_known(v_x_1455_, 1);
lean_inc(v_fn_1454_);
v___f_1465_ = lean_alloc_closure((void*)(l_Lean_Html_rewritePostM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1465_, 0, v_fn_1454_);
lean_inc_ref(v_inst_1453_);
v___x_1466_ = lean_alloc_closure((void*)(l_Lean_Html_rewritePostM___redArg), 3, 2);
lean_closure_set(v___x_1466_, 0, v_inst_1453_);
lean_closure_set(v___x_1466_, 1, v_fn_1454_);
v_sz_1467_ = lean_array_size(v_a_1464_);
v___x_1468_ = ((size_t)0ULL);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1453_, v___x_1466_, v_sz_1467_, v___x_1468_, v_a_1464_);
v___x_1470_ = lean_apply_4(v_toBind_1463_, lean_box(0), lean_box(0), v___x_1469_, v___f_1465_);
return v___x_1470_;
}
default: 
{
lean_object* v___x_1471_; 
lean_dec_ref(v_inst_1453_);
v___x_1471_ = lean_apply_1(v_fn_1454_, v_x_1455_);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM(lean_object* v_m_1472_, lean_object* v_inst_1473_, lean_object* v_fn_1474_, lean_object* v_x_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Html_rewritePostM___redArg(v_inst_1473_, v_fn_1474_, v_x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(lean_object* v_fn_1477_, lean_object* v_x_1478_){
_start:
{
switch(lean_obj_tag(v_x_1478_))
{
case 0:
{
lean_object* v_tag_1479_; lean_object* v_attrs_1480_; lean_object* v_children_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1490_; 
v_tag_1479_ = lean_ctor_get(v_x_1478_, 0);
v_attrs_1480_ = lean_ctor_get(v_x_1478_, 1);
v_children_1481_ = lean_ctor_get(v_x_1478_, 2);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_x_1478_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1483_ = v_x_1478_;
v_isShared_1484_ = v_isSharedCheck_1490_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_children_1481_);
lean_inc(v_attrs_1480_);
lean_inc(v_tag_1479_);
lean_dec(v_x_1478_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1490_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
lean_inc_ref(v_fn_1477_);
v___x_1485_ = l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(v_fn_1477_, v_children_1481_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 2, v___x_1485_);
v___x_1487_ = v___x_1483_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_tag_1479_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_attrs_1480_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_apply_1(v_fn_1477_, v___x_1487_);
return v___x_1488_;
}
}
}
case 3:
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1502_; 
v_a_1491_ = lean_ctor_get(v_x_1478_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_x_1478_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1493_ = v_x_1478_;
v_isShared_1494_ = v_isSharedCheck_1502_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v_x_1478_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1502_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
size_t v_sz_1495_; size_t v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v_sz_1495_ = lean_array_size(v_a_1491_);
v___x_1496_ = ((size_t)0ULL);
lean_inc_ref(v_fn_1477_);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0(v_fn_1477_, v_sz_1495_, v___x_1496_, v_a_1491_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1497_);
v___x_1499_ = v___x_1493_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_apply_1(v_fn_1477_, v___x_1499_);
return v___x_1500_;
}
}
}
default: 
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_apply_1(v_fn_1477_, v_x_1478_);
return v___x_1503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0(lean_object* v_fn_1504_, size_t v_sz_1505_, size_t v_i_1506_, lean_object* v_bs_1507_){
_start:
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_usize_dec_lt(v_i_1506_, v_sz_1505_);
if (v___x_1508_ == 0)
{
lean_dec_ref(v_fn_1504_);
return v_bs_1507_;
}
else
{
lean_object* v_v_1509_; lean_object* v___x_1510_; lean_object* v_bs_x27_1511_; lean_object* v___x_1512_; size_t v___x_1513_; size_t v___x_1514_; lean_object* v___x_1515_; 
v_v_1509_ = lean_array_uget(v_bs_1507_, v_i_1506_);
v___x_1510_ = lean_unsigned_to_nat(0u);
v_bs_x27_1511_ = lean_array_uset(v_bs_1507_, v_i_1506_, v___x_1510_);
lean_inc_ref(v_fn_1504_);
v___x_1512_ = l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(v_fn_1504_, v_v_1509_);
v___x_1513_ = ((size_t)1ULL);
v___x_1514_ = lean_usize_add(v_i_1506_, v___x_1513_);
v___x_1515_ = lean_array_uset(v_bs_x27_1511_, v_i_1506_, v___x_1512_);
v_i_1506_ = v___x_1514_;
v_bs_1507_ = v___x_1515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0___boxed(lean_object* v_fn_1517_, lean_object* v_sz_1518_, lean_object* v_i_1519_, lean_object* v_bs_1520_){
_start:
{
size_t v_sz_boxed_1521_; size_t v_i_boxed_1522_; lean_object* v_res_1523_; 
v_sz_boxed_1521_ = lean_unbox_usize(v_sz_1518_);
lean_dec(v_sz_1518_);
v_i_boxed_1522_ = lean_unbox_usize(v_i_1519_);
lean_dec(v_i_1519_);
v_res_1523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0(v_fn_1517_, v_sz_boxed_1521_, v_i_boxed_1522_, v_bs_1520_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePost(lean_object* v_fn_1524_, lean_object* v_h_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(v_fn_1524_, v_h_1525_);
return v___x_1526_;
}
}
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Mem(uint8_t builtin);
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_Elab(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Html_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Html_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Mem(uint8_t builtin);
lean_object* initialize_Init_Dynamic(uint8_t builtin);
lean_object* initialize_Lean_Data_Json_Elab(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Html_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Html_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Html_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
