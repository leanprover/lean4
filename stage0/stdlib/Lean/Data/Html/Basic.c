// Lean compiler output
// Module: Lean.Data.Html.Basic
// Imports: public import Init.Data.Array.GetLit import Init.Data.Array.Mem public import Init.Dynamic public import Lean.Data.Json.Elab public import Lean.ToExpr
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__3 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__3_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__4 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__4_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__5 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__5_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__6 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__6_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__6_value)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__7_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instToExprHtml_toExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "element"};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__0 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__0_value;
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 132, 38, 126, 255, 196, 59, 29)}};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__1 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__1_value;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__2;
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__3 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__3_value;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__4;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__5;
static const lean_string_object l_Lean_instToExprHtml_toExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__7 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__7_value;
static const lean_string_object l_Lean_instToExprHtml_toExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__6 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__6_value;
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__8_value_aux_0),((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__8 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__8_value;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__9;
static const lean_string_object l_Lean_instToExprHtml_toExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__10 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__10_value;
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__11_value_aux_0),((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__11 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__11_value;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__12;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__13;
static const lean_string_object l_Lean_instToExprHtml_toExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__14 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__14_value;
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__15_value_aux_0),((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__14_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__15 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__15_value;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__16;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__17;
static const lean_string_object l_Lean_instToExprHtml_toExpr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__18 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__18_value;
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__19_value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__19_value_aux_1),((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__18_value),LEAN_SCALAR_PTR_LITERAL(238, 210, 74, 251, 7, 54, 231, 214)}};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__19 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__19_value;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__20;
static const lean_string_object l_Lean_instToExprHtml_toExpr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__21 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__21_value;
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__22_value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__22_value_aux_1),((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__21_value),LEAN_SCALAR_PTR_LITERAL(180, 158, 139, 217, 84, 192, 171, 23)}};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__22 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__22_value;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__23;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__24;
static const lean_string_object l_Lean_instToExprHtml_toExpr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "seq"};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__25 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__25_value;
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instImpl___closed__0_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__26_value_aux_0),((lean_object*)&l_Lean_instImpl___closed__1_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140__value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l_Lean_instToExprHtml_toExpr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__26_value_aux_1),((lean_object*)&l_Lean_instToExprHtml_toExpr___closed__25_value),LEAN_SCALAR_PTR_LITERAL(187, 159, 6, 14, 33, 55, 218, 203)}};
static const lean_object* l_Lean_instToExprHtml_toExpr___closed__26 = (const lean_object*)&l_Lean_instToExprHtml_toExpr___closed__26_value;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__27;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__28;
static lean_once_cell_t l_Lean_instToExprHtml_toExpr___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml_toExpr___closed__29;
LEAN_EXPORT lean_object* l_Lean_instToExprHtml_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instToExprHtml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprHtml_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprHtml___closed__0 = (const lean_object*)&l_Lean_instToExprHtml___closed__0_value;
static lean_once_cell_t l_Lean_instToExprHtml___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprHtml___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprHtml;
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
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0(lean_object*);
static const lean_array_object l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0(lean_object*);
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
uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg(lean_object* v_xs_375_, lean_object* v_ys_376_, lean_object* v_x_377_){
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
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_375_ = stack[0].m_obj;
lean_object* v_ys_376_ = stack[1].m_obj;
lean_object* v_x_377_ = stack[2].m_obj;
uint8_t v_res_391_;
v_res_391_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg(v_xs_375_, v_ys_376_, v_x_377_);
stack->m_num = v_res_391_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg___boxed(lean_object* v_xs_392_, lean_object* v_ys_393_, lean_object* v_x_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg(v_xs_392_, v_ys_393_, v_x_394_);
lean_dec_ref(v_ys_393_);
lean_dec_ref(v_xs_392_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
uint8_t l_Lean_instBEqHtml_beq(lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
switch(lean_obj_tag(v_x_397_))
{
case 0:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v_tag_399_; lean_object* v_attrs_400_; lean_object* v_children_401_; lean_object* v_tag_402_; lean_object* v_attrs_403_; lean_object* v_children_404_; uint8_t v___x_405_; 
v_tag_399_ = lean_ctor_get(v_x_397_, 0);
v_attrs_400_ = lean_ctor_get(v_x_397_, 1);
v_children_401_ = lean_ctor_get(v_x_397_, 2);
v_tag_402_ = lean_ctor_get(v_x_398_, 0);
v_attrs_403_ = lean_ctor_get(v_x_398_, 1);
v_children_404_ = lean_ctor_get(v_x_398_, 2);
v___x_405_ = lean_string_dec_eq(v_tag_399_, v_tag_402_);
if (v___x_405_ == 0)
{
return v___x_405_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_406_ = lean_array_get_size(v_attrs_400_);
v___x_407_ = lean_array_get_size(v_attrs_403_);
v___x_408_ = lean_nat_dec_eq(v___x_406_, v___x_407_);
if (v___x_408_ == 0)
{
return v___x_408_;
}
else
{
uint8_t v___x_409_; 
v___x_409_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg(v_attrs_400_, v_attrs_403_, v___x_406_);
if (v___x_409_ == 0)
{
return v___x_409_;
}
else
{
v_x_397_ = v_children_401_;
v_x_398_ = v_children_404_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_411_; 
v___x_411_ = 0;
return v___x_411_;
}
}
case 1:
{
if (lean_obj_tag(v_x_398_) == 1)
{
lean_object* v_a_412_; lean_object* v_a_413_; uint8_t v___x_414_; 
v_a_412_ = lean_ctor_get(v_x_397_, 0);
v_a_413_ = lean_ctor_get(v_x_398_, 0);
v___x_414_ = lean_string_dec_eq(v_a_412_, v_a_413_);
return v___x_414_;
}
else
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
}
case 2:
{
if (lean_obj_tag(v_x_398_) == 2)
{
lean_object* v_a_416_; lean_object* v_a_417_; uint8_t v___x_418_; 
v_a_416_ = lean_ctor_get(v_x_397_, 0);
v_a_417_ = lean_ctor_get(v_x_398_, 0);
v___x_418_ = lean_string_dec_eq(v_a_416_, v_a_417_);
return v___x_418_;
}
else
{
uint8_t v___x_419_; 
v___x_419_ = 0;
return v___x_419_;
}
}
default: 
{
if (lean_obj_tag(v_x_398_) == 3)
{
lean_object* v_a_420_; lean_object* v_a_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v_a_420_ = lean_ctor_get(v_x_397_, 0);
v_a_421_ = lean_ctor_get(v_x_398_, 0);
v___x_422_ = lean_array_get_size(v_a_420_);
v___x_423_ = lean_array_get_size(v_a_421_);
v___x_424_ = lean_nat_dec_eq(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
return v___x_424_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg(v_a_420_, v_a_421_, v___x_422_);
return v___x_425_;
}
}
else
{
uint8_t v___x_426_; 
v___x_426_ = 0;
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqHtml_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_397_ = stack[0].m_obj;
lean_object* v_x_398_ = stack[1].m_obj;
uint8_t v_res_427_;
v_res_427_ = l_Lean_instBEqHtml_beq(v_x_397_, v_x_398_);
stack->m_num = v_res_427_;
}
uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg(lean_object* v_xs_428_, lean_object* v_ys_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_zero_431_; uint8_t v_isZero_432_; 
v_zero_431_ = lean_unsigned_to_nat(0u);
v_isZero_432_ = lean_nat_dec_eq(v_x_430_, v_zero_431_);
if (v_isZero_432_ == 1)
{
lean_dec(v_x_430_);
return v_isZero_432_;
}
else
{
lean_object* v_one_433_; lean_object* v_n_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_one_433_ = lean_unsigned_to_nat(1u);
v_n_434_ = lean_nat_sub(v_x_430_, v_one_433_);
lean_dec(v_x_430_);
v___x_435_ = lean_array_fget_borrowed(v_xs_428_, v_n_434_);
v___x_436_ = lean_array_fget_borrowed(v_ys_429_, v_n_434_);
v___x_437_ = l_Lean_instBEqHtml_beq(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_dec(v_n_434_);
return v___x_437_;
}
else
{
v_x_430_ = v_n_434_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_428_ = stack[0].m_obj;
lean_object* v_ys_429_ = stack[1].m_obj;
lean_object* v_x_430_ = stack[2].m_obj;
uint8_t v_res_439_;
v_res_439_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg(v_xs_428_, v_ys_429_, v_x_430_);
stack->m_num = v_res_439_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg___boxed(lean_object* v_xs_440_, lean_object* v_ys_441_, lean_object* v_x_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg(v_xs_440_, v_ys_441_, v_x_442_);
lean_dec_ref(v_ys_441_);
lean_dec_ref(v_xs_440_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqHtml_beq___boxed(lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Lean_instBEqHtml_beq(v_x_445_, v_x_446_);
lean_dec_ref(v_x_446_);
lean_dec_ref(v_x_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0(lean_object* v_xs_449_, lean_object* v_ys_450_, lean_object* v_hsz_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___redArg(v_xs_449_, v_ys_450_, v_x_452_);
return v___x_454_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_449_ = stack[0].m_obj;
lean_object* v_ys_450_ = stack[1].m_obj;
lean_object* v_x_452_ = stack[3].m_obj;
uint8_t v_res_455_;
v_res_455_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0(v_xs_449_, v_ys_450_, lean_box(0), v_x_452_, lean_box(0));
stack->m_num = v_res_455_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0___boxed(lean_object* v_xs_456_, lean_object* v_ys_457_, lean_object* v_hsz_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__0(v_xs_456_, v_ys_457_, v_hsz_458_, v_x_459_, v_x_460_);
lean_dec_ref(v_ys_457_);
lean_dec_ref(v_xs_456_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1(lean_object* v_xs_463_, lean_object* v_ys_464_, lean_object* v_hsz_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___redArg(v_xs_463_, v_ys_464_, v_x_466_);
return v___x_468_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_463_ = stack[0].m_obj;
lean_object* v_ys_464_ = stack[1].m_obj;
lean_object* v_x_466_ = stack[3].m_obj;
uint8_t v_res_469_;
v_res_469_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1(v_xs_463_, v_ys_464_, lean_box(0), v_x_466_, lean_box(0));
stack->m_num = v_res_469_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1___boxed(lean_object* v_xs_470_, lean_object* v_ys_471_, lean_object* v_hsz_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_Array_isEqvAux___at___00Lean_instBEqHtml_beq_spec__1(v_xs_470_, v_ys_471_, v_hsz_472_, v_x_473_, v_x_474_);
lean_dec_ref(v_ys_471_);
lean_dec_ref(v_xs_470_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0(lean_object* v_as_479_, size_t v_i_480_, size_t v_stop_481_, uint64_t v_b_482_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_eq(v_i_480_, v_stop_481_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v_fst_485_; lean_object* v_snd_486_; uint64_t v___x_487_; uint64_t v___x_488_; uint64_t v___x_489_; uint64_t v___x_490_; size_t v___x_491_; size_t v___x_492_; 
v___x_484_ = lean_array_uget_borrowed(v_as_479_, v_i_480_);
v_fst_485_ = lean_ctor_get(v___x_484_, 0);
v_snd_486_ = lean_ctor_get(v___x_484_, 1);
v___x_487_ = lean_string_hash(v_fst_485_);
v___x_488_ = lean_string_hash(v_snd_486_);
v___x_489_ = lean_uint64_mix_hash(v___x_487_, v___x_488_);
v___x_490_ = lean_uint64_mix_hash(v_b_482_, v___x_489_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_480_, v___x_491_);
v_i_480_ = v___x_492_;
v_b_482_ = v___x_490_;
goto _start;
}
else
{
return v_b_482_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_479_ = stack[0].m_obj;
size_t v_i_480_ = stack[1].m_num;
size_t v_stop_481_ = stack[2].m_num;
uint64_t v_b_482_ = stack[3].m_num;
uint64_t v_res_494_;
v_res_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0(v_as_479_, v_i_480_, v_stop_481_, v_b_482_);
stack->m_num = v_res_494_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0___boxed(lean_object* v_as_495_, lean_object* v_i_496_, lean_object* v_stop_497_, lean_object* v_b_498_){
_start:
{
size_t v_i_boxed_499_; size_t v_stop_boxed_500_; uint64_t v_b_boxed_501_; uint64_t v_res_502_; lean_object* v_r_503_; 
v_i_boxed_499_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_stop_boxed_500_ = lean_unbox_usize(v_stop_497_);
lean_dec(v_stop_497_);
v_b_boxed_501_ = lean_unbox_uint64(v_b_498_);
lean_dec_ref(v_b_498_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0(v_as_495_, v_i_boxed_499_, v_stop_boxed_500_, v_b_boxed_501_);
lean_dec_ref(v_as_495_);
v_r_503_ = lean_box_uint64(v_res_502_);
return v_r_503_;
}
}
uint64_t l_Lean_instHashableHtml_hash(lean_object* v_x_504_){
_start:
{
switch(lean_obj_tag(v_x_504_))
{
case 0:
{
lean_object* v_tag_505_; lean_object* v_attrs_506_; lean_object* v_children_507_; uint64_t v___x_508_; uint64_t v___x_509_; uint64_t v___x_510_; uint64_t v___y_512_; uint64_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_tag_505_ = lean_ctor_get(v_x_504_, 0);
v_attrs_506_ = lean_ctor_get(v_x_504_, 1);
v_children_507_ = lean_ctor_get(v_x_504_, 2);
v___x_508_ = 0ULL;
v___x_509_ = lean_string_hash(v_tag_505_);
v___x_510_ = lean_uint64_mix_hash(v___x_508_, v___x_509_);
v___x_516_ = 7ULL;
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = lean_array_get_size(v_attrs_506_);
v___x_519_ = lean_nat_dec_lt(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
v___y_512_ = v___x_516_;
goto v___jp_511_;
}
else
{
size_t v___x_520_; size_t v___x_521_; uint64_t v___x_522_; 
v___x_520_ = ((size_t)0ULL);
v___x_521_ = lean_usize_of_nat(v___x_518_);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__0(v_attrs_506_, v___x_520_, v___x_521_, v___x_516_);
v___y_512_ = v___x_522_;
goto v___jp_511_;
}
v___jp_511_:
{
uint64_t v___x_513_; uint64_t v___x_514_; uint64_t v___x_515_; 
v___x_513_ = lean_uint64_mix_hash(v___x_510_, v___y_512_);
v___x_514_ = l_Lean_instHashableHtml_hash(v_children_507_);
v___x_515_ = lean_uint64_mix_hash(v___x_513_, v___x_514_);
return v___x_515_;
}
}
case 1:
{
lean_object* v_a_523_; uint64_t v___x_524_; uint64_t v___x_525_; uint64_t v___x_526_; 
v_a_523_ = lean_ctor_get(v_x_504_, 0);
v___x_524_ = 1ULL;
v___x_525_ = lean_string_hash(v_a_523_);
v___x_526_ = lean_uint64_mix_hash(v___x_524_, v___x_525_);
return v___x_526_;
}
case 2:
{
lean_object* v_a_527_; uint64_t v___x_528_; uint64_t v___x_529_; uint64_t v___x_530_; 
v_a_527_ = lean_ctor_get(v_x_504_, 0);
v___x_528_ = 2ULL;
v___x_529_ = lean_string_hash(v_a_527_);
v___x_530_ = lean_uint64_mix_hash(v___x_528_, v___x_529_);
return v___x_530_;
}
default: 
{
lean_object* v_a_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_a_531_ = lean_ctor_get(v_x_504_, 0);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_array_get_size(v_a_531_);
v___x_534_ = lean_nat_dec_lt(v___x_532_, v___x_533_);
if (v___x_534_ == 0)
{
uint64_t v___x_535_; 
v___x_535_ = 12882348691112465364ULL;
return v___x_535_;
}
else
{
uint64_t v___x_536_; uint64_t v___x_537_; size_t v___x_538_; size_t v___x_539_; uint64_t v___x_540_; uint64_t v___x_541_; 
v___x_536_ = 3ULL;
v___x_537_ = 7ULL;
v___x_538_ = ((size_t)0ULL);
v___x_539_ = lean_usize_of_nat(v___x_533_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1(v_a_531_, v___x_538_, v___x_539_, v___x_537_);
v___x_541_ = lean_uint64_mix_hash(v___x_536_, v___x_540_);
return v___x_541_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instHashableHtml_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_504_ = stack[0].m_obj;
uint64_t v_res_542_;
v_res_542_ = l_Lean_instHashableHtml_hash(v_x_504_);
stack->m_num = v_res_542_;
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1(lean_object* v_as_543_, size_t v_i_544_, size_t v_stop_545_, uint64_t v_b_546_){
_start:
{
uint8_t v___x_547_; 
v___x_547_ = lean_usize_dec_eq(v_i_544_, v_stop_545_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; uint64_t v___x_549_; uint64_t v___x_550_; size_t v___x_551_; size_t v___x_552_; 
v___x_548_ = lean_array_uget_borrowed(v_as_543_, v_i_544_);
v___x_549_ = l_Lean_instHashableHtml_hash(v___x_548_);
v___x_550_ = lean_uint64_mix_hash(v_b_546_, v___x_549_);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_add(v_i_544_, v___x_551_);
v_i_544_ = v___x_552_;
v_b_546_ = v___x_550_;
goto _start;
}
else
{
return v_b_546_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_543_ = stack[0].m_obj;
size_t v_i_544_ = stack[1].m_num;
size_t v_stop_545_ = stack[2].m_num;
uint64_t v_b_546_ = stack[3].m_num;
uint64_t v_res_554_;
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1(v_as_543_, v_i_544_, v_stop_545_, v_b_546_);
stack->m_num = v_res_554_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1___boxed(lean_object* v_as_555_, lean_object* v_i_556_, lean_object* v_stop_557_, lean_object* v_b_558_){
_start:
{
size_t v_i_boxed_559_; size_t v_stop_boxed_560_; uint64_t v_b_boxed_561_; uint64_t v_res_562_; lean_object* v_r_563_; 
v_i_boxed_559_ = lean_unbox_usize(v_i_556_);
lean_dec(v_i_556_);
v_stop_boxed_560_ = lean_unbox_usize(v_stop_557_);
lean_dec(v_stop_557_);
v_b_boxed_561_ = lean_unbox_uint64(v_b_558_);
lean_dec_ref(v_b_558_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_instHashableHtml_hash_spec__1(v_as_555_, v_i_boxed_559_, v_stop_boxed_560_, v_b_boxed_561_);
lean_dec_ref(v_as_555_);
v_r_563_ = lean_box_uint64(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableHtml_hash___boxed(lean_object* v_x_564_){
_start:
{
uint64_t v_res_565_; lean_object* v_r_566_; 
v_res_565_ = l_Lean_instHashableHtml_hash(v_x_564_);
lean_dec_ref(v_x_564_);
v_r_566_ = lean_box_uint64(v_res_565_);
return v_r_566_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_00_u03b1Type_581_; 
v___x_579_ = lean_box(0);
v___x_580_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__1));
v_00_u03b1Type_581_ = l_Lean_mkConst(v___x_580_, v___x_579_);
return v_00_u03b1Type_581_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__8(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__7));
v___x_594_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__5));
v___x_595_ = l_Lean_mkConst(v___x_594_, v___x_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0(lean_object* v_nilFn_596_, lean_object* v_consFn_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
lean_dec_ref(v_consFn_597_);
lean_inc_ref(v_nilFn_596_);
return v_nilFn_596_;
}
else
{
lean_object* v_head_599_; lean_object* v_tail_600_; lean_object* v_fst_601_; lean_object* v_snd_602_; lean_object* v_00_u03b1Type_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_head_599_ = lean_ctor_get(v_x_598_, 0);
lean_inc(v_head_599_);
v_tail_600_ = lean_ctor_get(v_x_598_, 1);
lean_inc(v_tail_600_);
lean_dec_ref_known(v_x_598_, 2);
v_fst_601_ = lean_ctor_get(v_head_599_, 0);
lean_inc(v_fst_601_);
v_snd_602_ = lean_ctor_get(v_head_599_, 1);
lean_inc(v_snd_602_);
lean_dec(v_head_599_);
v_00_u03b1Type_603_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2);
v___x_604_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__8, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__8_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__8);
v___x_605_ = l_Lean_mkStrLit(v_fst_601_);
v___x_606_ = l_Lean_mkStrLit(v_snd_602_);
v___x_607_ = l_Lean_mkApp4(v___x_604_, v_00_u03b1Type_603_, v_00_u03b1Type_603_, v___x_605_, v___x_606_);
lean_inc_ref(v_consFn_597_);
v___x_608_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0(v_nilFn_596_, v_consFn_597_, v_tail_600_);
v___x_609_ = l_Lean_mkAppB(v_consFn_597_, v___x_607_, v___x_608_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___boxed(lean_object* v_nilFn_610_, lean_object* v_consFn_611_, lean_object* v_x_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0(v_nilFn_610_, v_consFn_611_, v_x_612_);
lean_dec_ref(v_nilFn_610_);
return v_res_613_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__2(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_box(0);
v___x_620_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__1));
v___x_621_ = l_Lean_Expr_const___override(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__4(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__7));
v___x_625_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__3));
v___x_626_ = l_Lean_mkConst(v___x_625_, v___x_624_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__5(void){
_start:
{
lean_object* v_00_u03b1Type_627_; lean_object* v___x_628_; lean_object* v_type_629_; 
v_00_u03b1Type_627_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2);
v___x_628_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__4, &l_Lean_instToExprHtml_toExpr___closed__4_once, _init_l_Lean_instToExprHtml_toExpr___closed__4);
v_type_629_ = l_Lean_mkAppB(v___x_628_, v_00_u03b1Type_627_, v_00_u03b1Type_627_);
return v_type_629_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__9(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__6));
v___x_636_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__8));
v___x_637_ = l_Lean_mkConst(v___x_636_, v___x_635_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__12(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__6));
v___x_643_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__11));
v___x_644_ = l_Lean_mkConst(v___x_643_, v___x_642_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__13(void){
_start:
{
lean_object* v_type_645_; lean_object* v___x_646_; lean_object* v_nil_647_; 
v_type_645_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__5, &l_Lean_instToExprHtml_toExpr___closed__5_once, _init_l_Lean_instToExprHtml_toExpr___closed__5);
v___x_646_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__12, &l_Lean_instToExprHtml_toExpr___closed__12_once, _init_l_Lean_instToExprHtml_toExpr___closed__12);
v_nil_647_ = l_Lean_Expr_app___override(v___x_646_, v_type_645_);
return v_nil_647_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__16(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__6));
v___x_653_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__15));
v___x_654_ = l_Lean_mkConst(v___x_653_, v___x_652_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__17(void){
_start:
{
lean_object* v_type_655_; lean_object* v___x_656_; lean_object* v_cons_657_; 
v_type_655_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__5, &l_Lean_instToExprHtml_toExpr___closed__5_once, _init_l_Lean_instToExprHtml_toExpr___closed__5);
v___x_656_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__16, &l_Lean_instToExprHtml_toExpr___closed__16_once, _init_l_Lean_instToExprHtml_toExpr___closed__16);
v_cons_657_ = l_Lean_Expr_app___override(v___x_656_, v_type_655_);
return v_cons_657_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__20(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_box(0);
v___x_664_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__19));
v___x_665_ = l_Lean_Expr_const___override(v___x_664_, v___x_663_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__23(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_box(0);
v___x_672_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__22));
v___x_673_ = l_Lean_Expr_const___override(v___x_672_, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__24(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v_type_676_; 
v___x_674_ = lean_box(0);
v___x_675_ = ((lean_object*)(l_Lean_instImpl___closed__2_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140_));
v_type_676_ = l_Lean_Expr_const___override(v___x_675_, v___x_674_);
return v_type_676_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__27(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_box(0);
v___x_683_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__26));
v___x_684_ = l_Lean_Expr_const___override(v___x_683_, v___x_682_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__28(void){
_start:
{
lean_object* v_type_685_; lean_object* v___x_686_; lean_object* v_nil_687_; 
v_type_685_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__24, &l_Lean_instToExprHtml_toExpr___closed__24_once, _init_l_Lean_instToExprHtml_toExpr___closed__24);
v___x_686_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__12, &l_Lean_instToExprHtml_toExpr___closed__12_once, _init_l_Lean_instToExprHtml_toExpr___closed__12);
v_nil_687_ = l_Lean_Expr_app___override(v___x_686_, v_type_685_);
return v_nil_687_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__29(void){
_start:
{
lean_object* v_type_688_; lean_object* v___x_689_; lean_object* v_cons_690_; 
v_type_688_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__24, &l_Lean_instToExprHtml_toExpr___closed__24_once, _init_l_Lean_instToExprHtml_toExpr___closed__24);
v___x_689_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__16, &l_Lean_instToExprHtml_toExpr___closed__16_once, _init_l_Lean_instToExprHtml_toExpr___closed__16);
v_cons_690_ = l_Lean_Expr_app___override(v___x_689_, v_type_688_);
return v_cons_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprHtml_toExpr(lean_object* v_x_691_){
_start:
{
switch(lean_obj_tag(v_x_691_))
{
case 0:
{
lean_object* v_tag_692_; lean_object* v_attrs_693_; lean_object* v_children_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_type_698_; lean_object* v___x_699_; lean_object* v_nil_700_; lean_object* v_cons_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_tag_692_ = lean_ctor_get(v_x_691_, 0);
lean_inc_ref(v_tag_692_);
v_attrs_693_ = lean_ctor_get(v_x_691_, 1);
lean_inc_ref(v_attrs_693_);
v_children_694_ = lean_ctor_get(v_x_691_, 2);
lean_inc_ref(v_children_694_);
lean_dec_ref_known(v_x_691_, 3);
v___x_695_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__2, &l_Lean_instToExprHtml_toExpr___closed__2_once, _init_l_Lean_instToExprHtml_toExpr___closed__2);
v___x_696_ = l_Lean_mkStrLit(v_tag_692_);
v___x_697_ = l_Lean_Expr_app___override(v___x_695_, v___x_696_);
v_type_698_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__5, &l_Lean_instToExprHtml_toExpr___closed__5_once, _init_l_Lean_instToExprHtml_toExpr___closed__5);
v___x_699_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__9, &l_Lean_instToExprHtml_toExpr___closed__9_once, _init_l_Lean_instToExprHtml_toExpr___closed__9);
v_nil_700_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__13, &l_Lean_instToExprHtml_toExpr___closed__13_once, _init_l_Lean_instToExprHtml_toExpr___closed__13);
v_cons_701_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__17, &l_Lean_instToExprHtml_toExpr___closed__17_once, _init_l_Lean_instToExprHtml_toExpr___closed__17);
v___x_702_ = lean_array_to_list(v_attrs_693_);
v___x_703_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0(v_nil_700_, v_cons_701_, v___x_702_);
v___x_704_ = l_Lean_mkAppB(v___x_699_, v_type_698_, v___x_703_);
v___x_705_ = l_Lean_Expr_app___override(v___x_697_, v___x_704_);
v___x_706_ = l_Lean_instToExprHtml_toExpr(v_children_694_);
v___x_707_ = l_Lean_Expr_app___override(v___x_705_, v___x_706_);
return v___x_707_;
}
case 1:
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_a_708_ = lean_ctor_get(v_x_691_, 0);
lean_inc_ref(v_a_708_);
lean_dec_ref_known(v_x_691_, 1);
v___x_709_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__20, &l_Lean_instToExprHtml_toExpr___closed__20_once, _init_l_Lean_instToExprHtml_toExpr___closed__20);
v___x_710_ = l_Lean_mkStrLit(v_a_708_);
v___x_711_ = l_Lean_Expr_app___override(v___x_709_, v___x_710_);
return v___x_711_;
}
case 2:
{
lean_object* v_a_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_a_712_ = lean_ctor_get(v_x_691_, 0);
lean_inc_ref(v_a_712_);
lean_dec_ref_known(v_x_691_, 1);
v___x_713_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__23, &l_Lean_instToExprHtml_toExpr___closed__23_once, _init_l_Lean_instToExprHtml_toExpr___closed__23);
v___x_714_ = l_Lean_mkStrLit(v_a_712_);
v___x_715_ = l_Lean_Expr_app___override(v___x_713_, v___x_714_);
return v___x_715_;
}
default: 
{
lean_object* v_a_716_; lean_object* v_type_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_nil_720_; lean_object* v_cons_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_a_716_ = lean_ctor_get(v_x_691_, 0);
lean_inc_ref(v_a_716_);
lean_dec_ref_known(v_x_691_, 1);
v_type_717_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__24, &l_Lean_instToExprHtml_toExpr___closed__24_once, _init_l_Lean_instToExprHtml_toExpr___closed__24);
v___x_718_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__27, &l_Lean_instToExprHtml_toExpr___closed__27_once, _init_l_Lean_instToExprHtml_toExpr___closed__27);
v___x_719_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__9, &l_Lean_instToExprHtml_toExpr___closed__9_once, _init_l_Lean_instToExprHtml_toExpr___closed__9);
v_nil_720_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__28, &l_Lean_instToExprHtml_toExpr___closed__28_once, _init_l_Lean_instToExprHtml_toExpr___closed__28);
v_cons_721_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__29, &l_Lean_instToExprHtml_toExpr___closed__29_once, _init_l_Lean_instToExprHtml_toExpr___closed__29);
v___x_722_ = lean_array_to_list(v_a_716_);
v___x_723_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1(v_nil_720_, v_cons_721_, v___x_722_);
v___x_724_ = l_Lean_mkAppB(v___x_719_, v_type_717_, v___x_723_);
v___x_725_ = l_Lean_Expr_app___override(v___x_718_, v___x_724_);
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1(lean_object* v_nilFn_726_, lean_object* v_consFn_727_, lean_object* v_x_728_){
_start:
{
if (lean_obj_tag(v_x_728_) == 0)
{
lean_dec_ref(v_consFn_727_);
lean_inc_ref(v_nilFn_726_);
return v_nilFn_726_;
}
else
{
lean_object* v_head_729_; lean_object* v_tail_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_head_729_ = lean_ctor_get(v_x_728_, 0);
lean_inc(v_head_729_);
v_tail_730_ = lean_ctor_get(v_x_728_, 1);
lean_inc(v_tail_730_);
lean_dec_ref_known(v_x_728_, 2);
v___x_731_ = l_Lean_instToExprHtml_toExpr(v_head_729_);
lean_inc_ref(v_consFn_727_);
v___x_732_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1(v_nilFn_726_, v_consFn_727_, v_tail_730_);
v___x_733_ = l_Lean_mkAppB(v_consFn_727_, v___x_731_, v___x_732_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1___boxed(lean_object* v_nilFn_734_, lean_object* v_consFn_735_, lean_object* v_x_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1(v_nilFn_734_, v_consFn_735_, v_x_736_);
lean_dec_ref(v_nilFn_734_);
return v_res_737_;
}
}
static lean_object* _init_l_Lean_instToExprHtml___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__24, &l_Lean_instToExprHtml_toExpr___closed__24_once, _init_l_Lean_instToExprHtml_toExpr___closed__24);
v___x_740_ = ((lean_object*)(l_Lean_instToExprHtml___closed__0));
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_instToExprHtml(void){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_obj_once(&l_Lean_instToExprHtml___closed__1, &l_Lean_instToExprHtml___closed__1_once, _init_l_Lean_instToExprHtml___closed__1);
return v___x_742_;
}
}
uint8_t l_Lean_Html_isEmpty(lean_object* v_x_748_){
_start:
{
lean_object* v_s_750_; 
switch(lean_obj_tag(v_x_748_))
{
case 0:
{
uint8_t v___x_754_; 
v___x_754_ = 0;
return v___x_754_;
}
case 3:
{
lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_a_755_ = lean_ctor_get(v_x_748_, 0);
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = lean_array_get_size(v_a_755_);
v___x_758_ = lean_nat_dec_lt(v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
uint8_t v___x_759_; 
v___x_759_ = 1;
return v___x_759_;
}
else
{
if (v___x_758_ == 0)
{
return v___x_758_;
}
else
{
size_t v___x_760_; size_t v___x_761_; uint8_t v___x_762_; 
v___x_760_ = ((size_t)0ULL);
v___x_761_ = lean_usize_of_nat(v___x_757_);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0(v_a_755_, v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
return v___x_758_;
}
else
{
uint8_t v___x_763_; 
v___x_763_ = 0;
return v___x_763_;
}
}
}
}
default: 
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v_x_748_, 0);
v_s_750_ = v_a_764_;
goto v___jp_749_;
}
}
v___jp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_751_ = lean_string_utf8_byte_size(v_s_750_);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_nat_dec_eq(v___x_751_, v___x_752_);
return v___x_753_;
}
}
}
LEAN_EXPORT void l_Lean_Html_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_748_ = stack[0].m_obj;
uint8_t v_res_765_;
v_res_765_ = l_Lean_Html_isEmpty(v_x_748_);
stack->m_num = v_res_765_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0(lean_object* v_as_766_, size_t v_i_767_, size_t v_stop_768_){
_start:
{
uint8_t v___x_769_; 
v___x_769_ = lean_usize_dec_eq(v_i_767_, v_stop_768_);
if (v___x_769_ == 0)
{
lean_object* v_val_770_; uint8_t v___x_771_; 
v_val_770_ = lean_array_uget_borrowed(v_as_766_, v_i_767_);
v___x_771_ = l_Lean_Html_isEmpty(v_val_770_);
if (v___x_771_ == 0)
{
uint8_t v___x_772_; 
v___x_772_ = 1;
return v___x_772_;
}
else
{
size_t v___x_773_; size_t v___x_774_; 
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_add(v_i_767_, v___x_773_);
v_i_767_ = v___x_774_;
goto _start;
}
}
else
{
uint8_t v___x_776_; 
v___x_776_ = 0;
return v___x_776_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_766_ = stack[0].m_obj;
size_t v_i_767_ = stack[1].m_num;
size_t v_stop_768_ = stack[2].m_num;
uint8_t v_res_777_;
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0(v_as_766_, v_i_767_, v_stop_768_);
stack->m_num = v_res_777_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0___boxed(lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_){
_start:
{
size_t v_i_boxed_781_; size_t v_stop_boxed_782_; uint8_t v_res_783_; lean_object* v_r_784_; 
v_i_boxed_781_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_782_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_783_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0(v_as_778_, v_i_boxed_781_, v_stop_boxed_782_);
lean_dec_ref(v_as_778_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_isEmpty___boxed(lean_object* v_x_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Lean_Html_isEmpty(v_x_785_);
lean_dec_ref(v_x_785_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__3_splitter___redArg(lean_object* v_x_788_, lean_object* v_h__1_789_, lean_object* v_h__2_790_, lean_object* v_h__3_791_, lean_object* v_h__4_792_){
_start:
{
switch(lean_obj_tag(v_x_788_))
{
case 0:
{
lean_object* v_tag_793_; lean_object* v_attrs_794_; lean_object* v_children_795_; lean_object* v___x_796_; 
lean_dec(v_h__3_791_);
lean_dec(v_h__2_790_);
lean_dec(v_h__1_789_);
v_tag_793_ = lean_ctor_get(v_x_788_, 0);
lean_inc_ref(v_tag_793_);
v_attrs_794_ = lean_ctor_get(v_x_788_, 1);
lean_inc_ref(v_attrs_794_);
v_children_795_ = lean_ctor_get(v_x_788_, 2);
lean_inc_ref(v_children_795_);
lean_dec_ref_known(v_x_788_, 3);
v___x_796_ = lean_apply_3(v_h__4_792_, v_tag_793_, v_attrs_794_, v_children_795_);
return v___x_796_;
}
case 1:
{
lean_object* v_a_797_; lean_object* v___x_798_; 
lean_dec(v_h__4_792_);
lean_dec(v_h__3_791_);
lean_dec(v_h__1_789_);
v_a_797_ = lean_ctor_get(v_x_788_, 0);
lean_inc_ref(v_a_797_);
lean_dec_ref_known(v_x_788_, 1);
v___x_798_ = lean_apply_1(v_h__2_790_, v_a_797_);
return v___x_798_;
}
case 2:
{
lean_object* v_a_799_; lean_object* v___x_800_; 
lean_dec(v_h__4_792_);
lean_dec(v_h__2_790_);
lean_dec(v_h__1_789_);
v_a_799_ = lean_ctor_get(v_x_788_, 0);
lean_inc_ref(v_a_799_);
lean_dec_ref_known(v_x_788_, 1);
v___x_800_ = lean_apply_1(v_h__3_791_, v_a_799_);
return v___x_800_;
}
default: 
{
lean_object* v_a_801_; lean_object* v___x_802_; 
lean_dec(v_h__4_792_);
lean_dec(v_h__3_791_);
lean_dec(v_h__2_790_);
v_a_801_ = lean_ctor_get(v_x_788_, 0);
lean_inc_ref(v_a_801_);
lean_dec_ref_known(v_x_788_, 1);
v___x_802_ = lean_apply_1(v_h__1_789_, v_a_801_);
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__3_splitter(lean_object* v_motive_803_, lean_object* v_x_804_, lean_object* v_h__1_805_, lean_object* v_h__2_806_, lean_object* v_h__3_807_, lean_object* v_h__4_808_){
_start:
{
switch(lean_obj_tag(v_x_804_))
{
case 0:
{
lean_object* v_tag_809_; lean_object* v_attrs_810_; lean_object* v_children_811_; lean_object* v___x_812_; 
lean_dec(v_h__3_807_);
lean_dec(v_h__2_806_);
lean_dec(v_h__1_805_);
v_tag_809_ = lean_ctor_get(v_x_804_, 0);
lean_inc_ref(v_tag_809_);
v_attrs_810_ = lean_ctor_get(v_x_804_, 1);
lean_inc_ref(v_attrs_810_);
v_children_811_ = lean_ctor_get(v_x_804_, 2);
lean_inc_ref(v_children_811_);
lean_dec_ref_known(v_x_804_, 3);
v___x_812_ = lean_apply_3(v_h__4_808_, v_tag_809_, v_attrs_810_, v_children_811_);
return v___x_812_;
}
case 1:
{
lean_object* v_a_813_; lean_object* v___x_814_; 
lean_dec(v_h__4_808_);
lean_dec(v_h__3_807_);
lean_dec(v_h__1_805_);
v_a_813_ = lean_ctor_get(v_x_804_, 0);
lean_inc_ref(v_a_813_);
lean_dec_ref_known(v_x_804_, 1);
v___x_814_ = lean_apply_1(v_h__2_806_, v_a_813_);
return v___x_814_;
}
case 2:
{
lean_object* v_a_815_; lean_object* v___x_816_; 
lean_dec(v_h__4_808_);
lean_dec(v_h__2_806_);
lean_dec(v_h__1_805_);
v_a_815_ = lean_ctor_get(v_x_804_, 0);
lean_inc_ref(v_a_815_);
lean_dec_ref_known(v_x_804_, 1);
v___x_816_ = lean_apply_1(v_h__3_807_, v_a_815_);
return v___x_816_;
}
default: 
{
lean_object* v_a_817_; lean_object* v___x_818_; 
lean_dec(v_h__4_808_);
lean_dec(v_h__3_807_);
lean_dec(v_h__2_806_);
v_a_817_ = lean_ctor_get(v_x_804_, 0);
lean_inc_ref(v_a_817_);
lean_dec_ref_known(v_x_804_, 1);
v___x_818_ = lean_apply_1(v_h__1_805_, v_a_817_);
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter___redArg(lean_object* v_x_819_, lean_object* v_h__1_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = lean_apply_2(v_h__1_820_, v_x_819_, lean_box(0));
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter(lean_object* v_a_822_, lean_object* v_motive_823_, lean_object* v_x_824_, lean_object* v_h__1_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = lean_apply_2(v_h__1_825_, v_x_824_, lean_box(0));
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter___boxed(lean_object* v_a_827_, lean_object* v_motive_828_, lean_object* v_x_829_, lean_object* v_h__1_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter(v_a_827_, v_motive_828_, v_x_829_, v_h__1_830_);
lean_dec_ref(v_a_827_);
return v_res_831_;
}
}
lean_object* l_Lean_Html_ofString(uint8_t v_escape_832_, lean_object* v_a_833_){
_start:
{
if (v_escape_832_ == 0)
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_834_, 0, v_a_833_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; 
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v_a_833_);
return v___x_835_;
}
}
}
LEAN_EXPORT void l_Lean_Html_ofString_0interp(lean_interpreter_value* stack)
{
uint8_t v_escape_832_ = stack[0].m_num;
lean_object* v_a_833_ = stack[1].m_obj;
lean_object* v_res_836_;
v_res_836_ = l_Lean_Html_ofString(v_escape_832_, v_a_833_);
stack->m_obj
 = v_res_836_;
}
LEAN_EXPORT lean_object* l_Lean_Html_ofString___boxed(lean_object* v_escape_837_, lean_object* v_a_838_){
_start:
{
uint8_t v_escape_boxed_839_; lean_object* v_res_840_; 
v_escape_boxed_839_ = lean_unbox(v_escape_837_);
v_res_840_ = l_Lean_Html_ofString(v_escape_boxed_839_, v_a_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instCoeString___lam__0(lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v_a_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_append(lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
if (lean_obj_tag(v_x_845_) == 3)
{
if (lean_obj_tag(v_x_846_) == 3)
{
lean_object* v_a_847_; lean_object* v_a_848_; uint8_t v___x_849_; 
v_a_847_ = lean_ctor_get(v_x_845_, 0);
v_a_848_ = lean_ctor_get(v_x_846_, 0);
v___x_849_ = l_Lean_Html_isEmpty(v_x_845_);
if (v___x_849_ == 0)
{
uint8_t v___x_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_858_; 
lean_inc_ref(v_a_848_);
v___x_850_ = l_Lean_Html_isEmpty(v_x_846_);
v_isSharedCheck_858_ = !lean_is_exclusive(v_x_846_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_x_846_, 0);
lean_dec(v_unused_859_);
v___x_852_ = v_x_846_;
v_isShared_853_ = v_isSharedCheck_858_;
goto v_resetjp_851_;
}
else
{
lean_dec(v_x_846_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_858_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
if (v___x_850_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_856_; 
lean_inc_ref(v_a_847_);
lean_dec_ref_known(v_x_845_, 1);
v___x_854_ = l_Array_append___redArg(v_a_847_, v_a_848_);
lean_dec_ref(v_a_848_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_854_);
v___x_856_ = v___x_852_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
else
{
lean_del_object(v___x_852_);
lean_dec_ref(v_a_848_);
return v_x_845_;
}
}
}
else
{
lean_dec_ref_known(v_x_845_, 1);
return v_x_846_;
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_871_; 
v_a_860_ = lean_ctor_get(v_x_845_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v_x_845_);
if (v_isSharedCheck_871_ == 0)
{
v___x_862_ = v_x_845_;
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v_x_845_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = lean_array_get_size(v_a_860_);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_nat_dec_eq(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = lean_array_push(v_a_860_, v_x_846_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_867_);
v___x_869_ = v___x_862_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
else
{
lean_del_object(v___x_862_);
lean_dec_ref(v_a_860_);
return v_x_846_;
}
}
}
}
else
{
if (lean_obj_tag(v_x_846_) == 3)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_886_; 
v_a_872_ = lean_ctor_get(v_x_846_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_846_);
if (v_isSharedCheck_886_ == 0)
{
v___x_874_ = v_x_846_;
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v_x_846_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_876_ = lean_array_get_size(v_a_872_);
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_nat_dec_eq(v___x_876_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = lean_mk_empty_array_with_capacity(v___x_879_);
v___x_881_ = lean_array_push(v___x_880_, v_x_845_);
v___x_882_ = l_Array_append___redArg(v___x_881_, v_a_872_);
lean_dec_ref(v_a_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_882_);
v___x_884_ = v___x_874_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_del_object(v___x_874_);
lean_dec_ref(v_a_872_);
return v_x_845_;
}
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_887_ = lean_unsigned_to_nat(2u);
v___x_888_ = lean_mk_empty_array_with_capacity(v___x_887_);
v___x_889_ = lean_array_push(v___x_888_, v_x_845_);
v___x_890_ = lean_array_push(v___x_889_, v_x_846_);
v___x_891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___redArg___lam__0(lean_object* v_h_894_, lean_object* v_____s_895_){
_start:
{
lean_object* v_out_896_; lean_object* v___x_897_; 
v_out_896_ = l_Lean_Html_append(v_____s_895_, v_h_894_);
v___x_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_897_, 0, v_out_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___redArg(lean_object* v_inst_899_, lean_object* v_hs_900_){
_start:
{
lean_object* v___f_901_; lean_object* v_out_902_; lean_object* v___x_903_; 
v___f_901_ = ((lean_object*)(l_Lean_Html_ofCollection___redArg___closed__0));
v_out_902_ = ((lean_object*)(l_Lean_Html_empty));
v___x_903_ = lean_apply_4(v_inst_899_, lean_box(0), v_hs_900_, v_out_902_, v___f_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection(lean_object* v_00_u03c1_904_, lean_object* v_inst_905_, lean_object* v_hs_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Html_ofCollection___redArg(v_inst_905_, v_hs_906_);
return v___x_907_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0(lean_object* v_as_908_, size_t v_sz_909_, size_t v_i_910_, lean_object* v_b_911_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = lean_usize_dec_lt(v_i_910_, v_sz_909_);
if (v___x_912_ == 0)
{
return v_b_911_;
}
else
{
lean_object* v_a_913_; lean_object* v_out_914_; size_t v___x_915_; size_t v___x_916_; 
v_a_913_ = lean_array_uget_borrowed(v_as_908_, v_i_910_);
lean_inc(v_a_913_);
v_out_914_ = l_Lean_Html_append(v_b_911_, v_a_913_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_910_, v___x_915_);
v_i_910_ = v___x_916_;
v_b_911_ = v_out_914_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_908_ = stack[0].m_obj;
size_t v_sz_909_ = stack[1].m_num;
size_t v_i_910_ = stack[2].m_num;
lean_object* v_b_911_ = stack[3].m_obj;
lean_object* v_res_918_;
v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0(v_as_908_, v_sz_909_, v_i_910_, v_b_911_);
stack->m_obj
 = v_res_918_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0___boxed(lean_object* v_as_919_, lean_object* v_sz_920_, lean_object* v_i_921_, lean_object* v_b_922_){
_start:
{
size_t v_sz_boxed_923_; size_t v_i_boxed_924_; lean_object* v_res_925_; 
v_sz_boxed_923_ = lean_unbox_usize(v_sz_920_);
lean_dec(v_sz_920_);
v_i_boxed_924_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0(v_as_919_, v_sz_boxed_923_, v_i_boxed_924_, v_b_922_);
lean_dec_ref(v_as_919_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0(lean_object* v_hs_926_){
_start:
{
lean_object* v_out_927_; size_t v_sz_928_; size_t v___x_929_; lean_object* v___x_930_; 
v_out_927_ = ((lean_object*)(l_Lean_Html_empty));
v_sz_928_ = lean_array_size(v_hs_926_);
v___x_929_ = ((size_t)0ULL);
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0(v_hs_926_, v_sz_928_, v___x_929_, v_out_927_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0___boxed(lean_object* v_hs_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0(v_hs_931_);
lean_dec_ref(v_hs_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofArray(lean_object* v_hs_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0(v_hs_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofArray___boxed(lean_object* v_hs_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Html_ofArray(v_hs_935_);
lean_dec_ref(v_hs_935_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(lean_object* v_as_x27_937_, lean_object* v_b_938_){
_start:
{
if (lean_obj_tag(v_as_x27_937_) == 0)
{
return v_b_938_;
}
else
{
lean_object* v_head_939_; lean_object* v_tail_940_; lean_object* v_out_941_; 
v_head_939_ = lean_ctor_get(v_as_x27_937_, 0);
v_tail_940_ = lean_ctor_get(v_as_x27_937_, 1);
lean_inc(v_head_939_);
v_out_941_ = l_Lean_Html_append(v_b_938_, v_head_939_);
v_as_x27_937_ = v_tail_940_;
v_b_938_ = v_out_941_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg___boxed(lean_object* v_as_x27_943_, lean_object* v_b_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(v_as_x27_943_, v_b_944_);
lean_dec(v_as_x27_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0(lean_object* v_hs_946_){
_start:
{
lean_object* v_out_947_; lean_object* v___x_948_; 
v_out_947_ = ((lean_object*)(l_Lean_Html_empty));
v___x_948_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(v_hs_946_, v_out_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0___boxed(lean_object* v_hs_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0(v_hs_949_);
lean_dec(v_hs_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofList(lean_object* v_hs_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0(v_hs_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofList___boxed(lean_object* v_hs_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Html_ofList(v_hs_953_);
lean_dec(v_hs_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0(lean_object* v_as_955_, lean_object* v_as_x27_956_, lean_object* v_b_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(v_as_x27_956_, v_b_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___boxed(lean_object* v_as_960_, lean_object* v_as_x27_961_, lean_object* v_b_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0(v_as_960_, v_as_x27_961_, v_b_962_, v_a_963_);
lean_dec(v_as_x27_961_);
lean_dec(v_as_960_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofOption(lean_object* v_h_x3f_965_){
_start:
{
if (lean_obj_tag(v_h_x3f_965_) == 0)
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Lean_Html_empty));
return v___x_966_;
}
else
{
lean_object* v_val_967_; 
v_val_967_ = lean_ctor_get(v_h_x3f_965_, 0);
lean_inc(v_val_967_);
return v_val_967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofOption___boxed(lean_object* v_h_x3f_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Html_ofOption(v_h_x3f_968_);
lean_dec(v_h_x3f_968_);
return v_res_969_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0(size_t v_sz_976_, size_t v_i_977_, lean_object* v_bs_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_lt(v_i_977_, v_sz_976_);
if (v___x_979_ == 0)
{
return v_bs_978_;
}
else
{
lean_object* v_v_980_; lean_object* v_fst_981_; lean_object* v_snd_982_; lean_object* v___x_983_; lean_object* v_bs_x27_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; 
v_v_980_ = lean_array_uget_borrowed(v_bs_978_, v_i_977_);
v_fst_981_ = lean_ctor_get(v_v_980_, 0);
lean_inc(v_fst_981_);
v_snd_982_ = lean_ctor_get(v_v_980_, 1);
lean_inc(v_snd_982_);
v___x_983_ = lean_unsigned_to_nat(0u);
v_bs_x27_984_ = lean_array_uset(v_bs_978_, v_i_977_, v___x_983_);
v___x_985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_985_, 0, v_fst_981_);
v___x_986_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_986_, 0, v_snd_982_);
v___x_987_ = lean_unsigned_to_nat(2u);
v___x_988_ = lean_mk_empty_array_with_capacity(v___x_987_);
v___x_989_ = lean_array_push(v___x_988_, v___x_985_);
v___x_990_ = lean_array_push(v___x_989_, v___x_986_);
v___x_991_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_add(v_i_977_, v___x_992_);
v___x_994_ = lean_array_uset(v_bs_x27_984_, v_i_977_, v___x_991_);
v_i_977_ = v___x_993_;
v_bs_978_ = v___x_994_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_976_ = stack[0].m_num;
size_t v_i_977_ = stack[1].m_num;
lean_object* v_bs_978_ = stack[2].m_obj;
lean_object* v_res_996_;
v_res_996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0(v_sz_976_, v_i_977_, v_bs_978_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0___boxed(lean_object* v_sz_997_, lean_object* v_i_998_, lean_object* v_bs_999_){
_start:
{
size_t v_sz_boxed_1000_; size_t v_i_boxed_1001_; lean_object* v_res_1002_; 
v_sz_boxed_1000_ = lean_unbox_usize(v_sz_997_);
lean_dec(v_sz_997_);
v_i_boxed_1001_ = lean_unbox_usize(v_i_998_);
lean_dec(v_i_998_);
v_res_1002_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0(v_sz_boxed_1000_, v_i_boxed_1001_, v_bs_999_);
return v_res_1002_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1(size_t v_sz_1003_, size_t v_i_1004_, lean_object* v_bs_1005_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_lt(v_i_1004_, v_sz_1003_);
if (v___x_1006_ == 0)
{
return v_bs_1005_;
}
else
{
lean_object* v_v_1007_; lean_object* v___x_1008_; lean_object* v_bs_x27_1009_; size_t v___x_1010_; size_t v___x_1011_; lean_object* v___x_1012_; 
v_v_1007_ = lean_array_uget(v_bs_1005_, v_i_1004_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v_bs_x27_1009_ = lean_array_uset(v_bs_1005_, v_i_1004_, v___x_1008_);
v___x_1010_ = ((size_t)1ULL);
v___x_1011_ = lean_usize_add(v_i_1004_, v___x_1010_);
v___x_1012_ = lean_array_uset(v_bs_x27_1009_, v_i_1004_, v_v_1007_);
v_i_1004_ = v___x_1011_;
v_bs_1005_ = v___x_1012_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1003_ = stack[0].m_num;
size_t v_i_1004_ = stack[1].m_num;
lean_object* v_bs_1005_ = stack[2].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1(v_sz_1003_, v_i_1004_, v_bs_1005_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1___boxed(lean_object* v_sz_1015_, lean_object* v_i_1016_, lean_object* v_bs_1017_){
_start:
{
size_t v_sz_boxed_1018_; size_t v_i_boxed_1019_; lean_object* v_res_1020_; 
v_sz_boxed_1018_ = lean_unbox_usize(v_sz_1015_);
lean_dec(v_sz_1015_);
v_i_boxed_1019_ = lean_unbox_usize(v_i_1016_);
lean_dec(v_i_1016_);
v_res_1020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1(v_sz_boxed_1018_, v_i_boxed_1019_, v_bs_1017_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1(lean_object* v_a_1021_){
_start:
{
size_t v_sz_1022_; size_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_sz_1022_ = lean_array_size(v_a_1021_);
v___x_1023_ = ((size_t)0ULL);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1(v_sz_1022_, v___x_1023_, v_a_1021_);
v___x_1025_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instToJson_to(lean_object* v_x_1030_){
_start:
{
switch(lean_obj_tag(v_x_1030_))
{
case 0:
{
lean_object* v_tag_1031_; lean_object* v_attrs_1032_; lean_object* v_children_1033_; size_t v_sz_1034_; size_t v___x_1035_; lean_object* v_attrs_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_tag_1031_ = lean_ctor_get(v_x_1030_, 0);
lean_inc_ref(v_tag_1031_);
v_attrs_1032_ = lean_ctor_get(v_x_1030_, 1);
lean_inc_ref(v_attrs_1032_);
v_children_1033_ = lean_ctor_get(v_x_1030_, 2);
lean_inc_ref(v_children_1033_);
lean_dec_ref_known(v_x_1030_, 3);
v_sz_1034_ = lean_array_size(v_attrs_1032_);
v___x_1035_ = ((size_t)0ULL);
v_attrs_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0(v_sz_1034_, v___x_1035_, v_attrs_1032_);
v___x_1037_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__0));
v___x_1038_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_tag_1031_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__1));
v___x_1041_ = l_Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1(v_attrs_1036_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__2));
v___x_1044_ = l_Lean_Html_instToJson_to(v_children_1033_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1042_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1039_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = l_Lean_Json_mkObj(v___x_1049_);
lean_dec_ref_known(v___x_1049_, 2);
return v___x_1050_;
}
case 1:
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
v_a_1051_ = lean_ctor_get(v_x_1030_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v_x_1030_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v_x_1030_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 3);
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
case 2:
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1071_; 
v_a_1059_ = lean_ctor_get(v_x_1030_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1061_ = v_x_1030_;
v_isShared_1062_ = v_isSharedCheck_1071_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v_x_1030_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1071_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__3));
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 3);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1059_);
v___x_1065_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1063_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_Json_mkObj(v___x_1068_);
lean_dec_ref_known(v___x_1068_, 2);
return v___x_1069_;
}
}
}
default: 
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1082_; 
v_a_1072_ = lean_ctor_get(v_x_1030_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1074_ = v_x_1030_;
v_isShared_1075_ = v_isSharedCheck_1082_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v_x_1030_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1082_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
size_t v_sz_1076_; size_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v_sz_1076_ = lean_array_size(v_a_1072_);
v___x_1077_ = ((size_t)0ULL);
v___x_1078_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2(v_sz_1076_, v___x_1077_, v_a_1072_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 4);
lean_ctor_set(v___x_1074_, 0, v___x_1078_);
v___x_1080_ = v___x_1074_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2(size_t v_sz_1083_, size_t v_i_1084_, lean_object* v_bs_1085_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = lean_usize_dec_lt(v_i_1084_, v_sz_1083_);
if (v___x_1086_ == 0)
{
return v_bs_1085_;
}
else
{
lean_object* v_v_1087_; lean_object* v___x_1088_; lean_object* v_bs_x27_1089_; lean_object* v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; lean_object* v___x_1093_; 
v_v_1087_ = lean_array_uget(v_bs_1085_, v_i_1084_);
v___x_1088_ = lean_unsigned_to_nat(0u);
v_bs_x27_1089_ = lean_array_uset(v_bs_1085_, v_i_1084_, v___x_1088_);
v___x_1090_ = l_Lean_Html_instToJson_to(v_v_1087_);
v___x_1091_ = ((size_t)1ULL);
v___x_1092_ = lean_usize_add(v_i_1084_, v___x_1091_);
v___x_1093_ = lean_array_uset(v_bs_x27_1089_, v_i_1084_, v___x_1090_);
v_i_1084_ = v___x_1092_;
v_bs_1085_ = v___x_1093_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1083_ = stack[0].m_num;
size_t v_i_1084_ = stack[1].m_num;
lean_object* v_bs_1085_ = stack[2].m_obj;
lean_object* v_res_1095_;
v_res_1095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2(v_sz_1083_, v_i_1084_, v_bs_1085_);
stack->m_obj
 = v_res_1095_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2___boxed(lean_object* v_sz_1096_, lean_object* v_i_1097_, lean_object* v_bs_1098_){
_start:
{
size_t v_sz_boxed_1099_; size_t v_i_boxed_1100_; lean_object* v_res_1101_; 
v_sz_boxed_1099_ = lean_unbox_usize(v_sz_1096_);
lean_dec(v_sz_1096_);
v_i_boxed_1100_ = lean_unbox_usize(v_i_1097_);
lean_dec(v_i_1097_);
v_res_1101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2(v_sz_boxed_1099_, v_i_boxed_1100_, v_bs_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__3_splitter___redArg(lean_object* v_x_1102_, lean_object* v_h__1_1103_, lean_object* v_h__2_1104_, lean_object* v_h__3_1105_, lean_object* v_h__4_1106_){
_start:
{
switch(lean_obj_tag(v_x_1102_))
{
case 0:
{
lean_object* v_tag_1107_; lean_object* v_attrs_1108_; lean_object* v_children_1109_; lean_object* v___x_1110_; 
lean_dec(v_h__4_1106_);
lean_dec(v_h__2_1104_);
lean_dec(v_h__1_1103_);
v_tag_1107_ = lean_ctor_get(v_x_1102_, 0);
lean_inc_ref(v_tag_1107_);
v_attrs_1108_ = lean_ctor_get(v_x_1102_, 1);
lean_inc_ref(v_attrs_1108_);
v_children_1109_ = lean_ctor_get(v_x_1102_, 2);
lean_inc_ref(v_children_1109_);
lean_dec_ref_known(v_x_1102_, 3);
v___x_1110_ = lean_apply_3(v_h__3_1105_, v_tag_1107_, v_attrs_1108_, v_children_1109_);
return v___x_1110_;
}
case 1:
{
lean_object* v_a_1111_; lean_object* v___x_1112_; 
lean_dec(v_h__4_1106_);
lean_dec(v_h__3_1105_);
lean_dec(v_h__2_1104_);
v_a_1111_ = lean_ctor_get(v_x_1102_, 0);
lean_inc_ref(v_a_1111_);
lean_dec_ref_known(v_x_1102_, 1);
v___x_1112_ = lean_apply_1(v_h__1_1103_, v_a_1111_);
return v___x_1112_;
}
case 2:
{
lean_object* v_a_1113_; lean_object* v___x_1114_; 
lean_dec(v_h__4_1106_);
lean_dec(v_h__3_1105_);
lean_dec(v_h__1_1103_);
v_a_1113_ = lean_ctor_get(v_x_1102_, 0);
lean_inc_ref(v_a_1113_);
lean_dec_ref_known(v_x_1102_, 1);
v___x_1114_ = lean_apply_1(v_h__2_1104_, v_a_1113_);
return v___x_1114_;
}
default: 
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
lean_dec(v_h__3_1105_);
lean_dec(v_h__2_1104_);
lean_dec(v_h__1_1103_);
v_a_1115_ = lean_ctor_get(v_x_1102_, 0);
lean_inc_ref(v_a_1115_);
lean_dec_ref_known(v_x_1102_, 1);
v___x_1116_ = lean_apply_1(v_h__4_1106_, v_a_1115_);
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__3_splitter(lean_object* v_motive_1117_, lean_object* v_x_1118_, lean_object* v_h__1_1119_, lean_object* v_h__2_1120_, lean_object* v_h__3_1121_, lean_object* v_h__4_1122_){
_start:
{
switch(lean_obj_tag(v_x_1118_))
{
case 0:
{
lean_object* v_tag_1123_; lean_object* v_attrs_1124_; lean_object* v_children_1125_; lean_object* v___x_1126_; 
lean_dec(v_h__4_1122_);
lean_dec(v_h__2_1120_);
lean_dec(v_h__1_1119_);
v_tag_1123_ = lean_ctor_get(v_x_1118_, 0);
lean_inc_ref(v_tag_1123_);
v_attrs_1124_ = lean_ctor_get(v_x_1118_, 1);
lean_inc_ref(v_attrs_1124_);
v_children_1125_ = lean_ctor_get(v_x_1118_, 2);
lean_inc_ref(v_children_1125_);
lean_dec_ref_known(v_x_1118_, 3);
v___x_1126_ = lean_apply_3(v_h__3_1121_, v_tag_1123_, v_attrs_1124_, v_children_1125_);
return v___x_1126_;
}
case 1:
{
lean_object* v_a_1127_; lean_object* v___x_1128_; 
lean_dec(v_h__4_1122_);
lean_dec(v_h__3_1121_);
lean_dec(v_h__2_1120_);
v_a_1127_ = lean_ctor_get(v_x_1118_, 0);
lean_inc_ref(v_a_1127_);
lean_dec_ref_known(v_x_1118_, 1);
v___x_1128_ = lean_apply_1(v_h__1_1119_, v_a_1127_);
return v___x_1128_;
}
case 2:
{
lean_object* v_a_1129_; lean_object* v___x_1130_; 
lean_dec(v_h__4_1122_);
lean_dec(v_h__3_1121_);
lean_dec(v_h__1_1119_);
v_a_1129_ = lean_ctor_get(v_x_1118_, 0);
lean_inc_ref(v_a_1129_);
lean_dec_ref_known(v_x_1118_, 1);
v___x_1130_ = lean_apply_1(v_h__2_1120_, v_a_1129_);
return v___x_1130_;
}
default: 
{
lean_object* v_a_1131_; lean_object* v___x_1132_; 
lean_dec(v_h__3_1121_);
lean_dec(v_h__2_1120_);
lean_dec(v_h__1_1119_);
v_a_1131_ = lean_ctor_get(v_x_1118_, 0);
lean_inc_ref(v_a_1131_);
lean_dec_ref_known(v_x_1118_, 1);
v___x_1132_ = lean_apply_1(v_h__4_1122_, v_a_1131_);
return v___x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_1133_, lean_object* v_h__1_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_apply_2(v_h__1_1134_, v_x_1133_, lean_box(0));
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_1136_, lean_object* v_P_1137_, lean_object* v_motive_1138_, lean_object* v_x_1139_, lean_object* v_h__1_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_apply_2(v_h__1_1140_, v_x_1139_, lean_box(0));
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__1_splitter___redArg(lean_object* v_x_1142_, lean_object* v_h__1_1143_){
_start:
{
lean_object* v_fst_1144_; lean_object* v_snd_1145_; lean_object* v___x_1146_; 
v_fst_1144_ = lean_ctor_get(v_x_1142_, 0);
lean_inc(v_fst_1144_);
v_snd_1145_ = lean_ctor_get(v_x_1142_, 1);
lean_inc(v_snd_1145_);
lean_dec_ref(v_x_1142_);
v___x_1146_ = lean_apply_2(v_h__1_1143_, v_fst_1144_, v_snd_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__1_splitter(lean_object* v_motive_1147_, lean_object* v_x_1148_, lean_object* v_h__1_1149_){
_start:
{
lean_object* v_fst_1150_; lean_object* v_snd_1151_; lean_object* v___x_1152_; 
v_fst_1150_ = lean_ctor_get(v_x_1148_, 0);
lean_inc(v_fst_1150_);
v_snd_1151_ = lean_ctor_get(v_x_1148_, 1);
lean_inc(v_snd_1151_);
lean_dec_ref(v_x_1148_);
v___x_1152_ = lean_apply_2(v_h__1_1149_, v_fst_1150_, v_snd_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(lean_object* v_t_1155_, lean_object* v_k_1156_){
_start:
{
if (lean_obj_tag(v_t_1155_) == 0)
{
lean_object* v_k_1157_; lean_object* v_v_1158_; lean_object* v_l_1159_; lean_object* v_r_1160_; uint8_t v___x_1161_; 
v_k_1157_ = lean_ctor_get(v_t_1155_, 1);
v_v_1158_ = lean_ctor_get(v_t_1155_, 2);
v_l_1159_ = lean_ctor_get(v_t_1155_, 3);
v_r_1160_ = lean_ctor_get(v_t_1155_, 4);
v___x_1161_ = lean_string_compare(v_k_1156_, v_k_1157_);
switch(v___x_1161_)
{
case 0:
{
v_t_1155_ = v_l_1159_;
goto _start;
}
case 1:
{
lean_object* v___x_1163_; 
lean_inc(v_v_1158_);
v___x_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1163_, 0, v_v_1158_);
return v___x_1163_;
}
default: 
{
v_t_1155_ = v_r_1160_;
goto _start;
}
}
}
else
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_box(0);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg___boxed(lean_object* v_t_1166_, lean_object* v_k_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_t_1166_, v_k_1167_);
lean_dec_ref(v_k_1167_);
lean_dec(v_t_1166_);
return v_res_1168_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3(size_t v_sz_1169_, size_t v_i_1170_, lean_object* v_bs_1171_){
_start:
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_usize_dec_lt(v_i_1170_, v_sz_1169_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_bs_1171_);
return v___x_1173_;
}
else
{
lean_object* v_v_1174_; lean_object* v___x_1175_; lean_object* v_bs_x27_1176_; size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
v_v_1174_ = lean_array_uget(v_bs_1171_, v_i_1170_);
v___x_1175_ = lean_unsigned_to_nat(0u);
v_bs_x27_1176_ = lean_array_uset(v_bs_1171_, v_i_1170_, v___x_1175_);
v___x_1177_ = ((size_t)1ULL);
v___x_1178_ = lean_usize_add(v_i_1170_, v___x_1177_);
v___x_1179_ = lean_array_uset(v_bs_x27_1176_, v_i_1170_, v_v_1174_);
v_i_1170_ = v___x_1178_;
v_bs_1171_ = v___x_1179_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1169_ = stack[0].m_num;
size_t v_i_1170_ = stack[1].m_num;
lean_object* v_bs_1171_ = stack[2].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3(v_sz_1169_, v_i_1170_, v_bs_1171_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1182_, lean_object* v_i_1183_, lean_object* v_bs_1184_){
_start:
{
size_t v_sz_boxed_1185_; size_t v_i_boxed_1186_; lean_object* v_res_1187_; 
v_sz_boxed_1185_ = lean_unbox_usize(v_sz_1182_);
lean_dec(v_sz_1182_);
v_i_boxed_1186_ = lean_unbox_usize(v_i_1183_);
lean_dec(v_i_1183_);
v_res_1187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3(v_sz_boxed_1185_, v_i_boxed_1186_, v_bs_1184_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2(lean_object* v_x_1190_){
_start:
{
if (lean_obj_tag(v_x_1190_) == 4)
{
lean_object* v_elems_1191_; size_t v_sz_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
v_elems_1191_ = lean_ctor_get(v_x_1190_, 0);
lean_inc_ref(v_elems_1191_);
lean_dec_ref_known(v_x_1190_, 1);
v_sz_1192_ = lean_array_size(v_elems_1191_);
v___x_1193_ = ((size_t)0ULL);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3(v_sz_1192_, v___x_1193_, v_elems_1191_);
return v___x_1194_;
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1195_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__0));
v___x_1196_ = lean_unsigned_to_nat(80u);
v___x_1197_ = l_Lean_Json_pretty(v_x_1190_, v___x_1196_);
v___x_1198_ = lean_string_append(v___x_1195_, v___x_1197_);
lean_dec_ref(v___x_1197_);
v___x_1199_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__1));
v___x_1200_ = lean_string_append(v___x_1198_, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2(lean_object* v_j_1202_, lean_object* v_k_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = l_Lean_Json_getObjValD(v_j_1202_, v_k_1203_);
v___x_1205_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2(v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2___boxed(lean_object* v_j_1206_, lean_object* v_k_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2(v_j_1206_, v_k_1207_);
lean_dec_ref(v_k_1207_);
return v_res_1208_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3(size_t v_sz_1210_, size_t v_i_1211_, lean_object* v_bs_1212_){
_start:
{
uint8_t v___x_1213_; 
v___x_1213_ = lean_usize_dec_lt(v_i_1211_, v_sz_1210_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_bs_1212_);
return v___x_1214_;
}
else
{
lean_object* v_v_1215_; 
v_v_1215_ = lean_array_uget_borrowed(v_bs_1212_, v_i_1211_);
if (lean_obj_tag(v_v_1215_) == 4)
{
lean_object* v_elems_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_elems_1221_ = lean_ctor_get(v_v_1215_, 0);
v___x_1222_ = lean_array_get_size(v_elems_1221_);
v___x_1223_ = lean_unsigned_to_nat(2u);
v___x_1224_ = lean_nat_dec_eq(v___x_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_inc_ref(v_v_1215_);
lean_dec_ref(v_bs_1212_);
goto v___jp_1216_;
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = lean_array_fget_borrowed(v_elems_1221_, v___x_1225_);
if (lean_obj_tag(v___x_1226_) == 3)
{
lean_object* v_s_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_s_1227_ = lean_ctor_get(v___x_1226_, 0);
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_array_fget_borrowed(v_elems_1221_, v___x_1228_);
if (lean_obj_tag(v___x_1229_) == 3)
{
lean_object* v_s_1230_; lean_object* v_bs_x27_1231_; lean_object* v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; 
lean_inc_ref(v_s_1227_);
v_s_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc_ref(v_s_1230_);
v_bs_x27_1231_ = lean_array_uset(v_bs_1212_, v_i_1211_, v___x_1225_);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v_s_1227_);
lean_ctor_set(v___x_1232_, 1, v_s_1230_);
v___x_1233_ = ((size_t)1ULL);
v___x_1234_ = lean_usize_add(v_i_1211_, v___x_1233_);
v___x_1235_ = lean_array_uset(v_bs_x27_1231_, v_i_1211_, v___x_1232_);
v_i_1211_ = v___x_1234_;
v_bs_1212_ = v___x_1235_;
goto _start;
}
else
{
lean_inc_ref(v_v_1215_);
lean_dec_ref(v_bs_1212_);
goto v___jp_1216_;
}
}
else
{
lean_inc_ref(v_v_1215_);
lean_dec_ref(v_bs_1212_);
goto v___jp_1216_;
}
}
}
else
{
lean_inc(v_v_1215_);
lean_dec_ref(v_bs_1212_);
goto v___jp_1216_;
}
v___jp_1216_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3___closed__0));
v___x_1218_ = l_Lean_Json_compress(v_v_1215_);
v___x_1219_ = lean_string_append(v___x_1217_, v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1210_ = stack[0].m_num;
size_t v_i_1211_ = stack[1].m_num;
lean_object* v_bs_1212_ = stack[2].m_obj;
lean_object* v_res_1237_;
v_res_1237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3(v_sz_1210_, v_i_1211_, v_bs_1212_);
stack->m_obj
 = v_res_1237_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3___boxed(lean_object* v_sz_1238_, lean_object* v_i_1239_, lean_object* v_bs_1240_){
_start:
{
size_t v_sz_boxed_1241_; size_t v_i_boxed_1242_; lean_object* v_res_1243_; 
v_sz_boxed_1241_ = lean_unbox_usize(v_sz_1238_);
lean_dec(v_sz_1238_);
v_i_boxed_1242_ = lean_unbox_usize(v_i_1239_);
lean_dec(v_i_1239_);
v_res_1243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3(v_sz_boxed_1241_, v_i_boxed_1242_, v_bs_1240_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instFromJson_from_x3f(lean_object* v_x_1247_){
_start:
{
switch(lean_obj_tag(v_x_1247_))
{
case 3:
{
lean_object* v_s_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1256_; 
v_s_1248_ = lean_ctor_get(v_x_1247_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_1247_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1250_ = v_x_1247_;
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_s_1248_);
lean_dec(v_x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set_tag(v___x_1250_, 1);
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_s_1248_);
v___x_1253_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
}
case 4:
{
lean_object* v_elems_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1283_; 
v_elems_1257_ = lean_ctor_get(v_x_1247_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_x_1247_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1259_ = v_x_1247_;
v_isShared_1260_ = v_isSharedCheck_1283_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_elems_1257_);
lean_dec(v_x_1247_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1283_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
size_t v_sz_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v_sz_1261_ = lean_array_size(v_elems_1257_);
v___x_1262_ = ((size_t)0ULL);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0(v_sz_1261_, v___x_1262_, v_elems_1257_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_del_object(v___x_1259_);
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1282_; 
v_a_1272_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1274_ = v___x_1263_;
v_isShared_1275_ = v_isSharedCheck_1282_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1263_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1282_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set_tag(v___x_1259_, 3);
lean_ctor_set(v___x_1259_, 0, v_a_1272_);
v___x_1277_ = v___x_1259_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1279_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1277_);
v___x_1279_ = v___x_1274_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
}
case 5:
{
lean_object* v_kvPairs_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_kvPairs_1284_ = lean_ctor_get(v_x_1247_, 0);
v___x_1285_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__0));
v___x_1286_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_kvPairs_1284_, v___x_1285_);
if (lean_obj_tag(v___x_1286_) == 1)
{
lean_object* v_val_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1342_; 
v_val_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1342_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_val_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1342_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
if (lean_obj_tag(v_val_1287_) == 3)
{
lean_object* v_s_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_del_object(v___x_1289_);
v_s_1291_ = lean_ctor_get(v_val_1287_, 0);
lean_inc_ref(v_s_1291_);
lean_dec_ref_known(v_val_1287_, 1);
v___x_1292_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__1));
lean_inc_ref(v_x_1247_);
v___x_1293_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2(v_x_1247_, v___x_1292_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v_s_1291_);
lean_dec_ref_known(v_x_1247_, 1);
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_object* v_a_1302_; size_t v_sz_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v_a_1302_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1293_, 1);
v_sz_1303_ = lean_array_size(v_a_1302_);
v___x_1304_ = ((size_t)0ULL);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3(v_sz_1303_, v___x_1304_, v_a_1302_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_s_1291_);
lean_dec_ref_known(v_x_1247_, 1);
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_a_1314_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1315_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__2));
v___x_1316_ = l_Lean_Json_getObjVal_x3f(v_x_1247_, v___x_1315_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_a_1314_);
lean_dec_ref(v_s_1291_);
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1326_; 
v_a_1325_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1326_ = l_Lean_Html_instFromJson_from_x3f(v_a_1325_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_dec(v_a_1314_);
lean_dec_ref(v_s_1291_);
return v___x_1326_;
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1335_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1331_, 0, v_s_1291_);
lean_ctor_set(v___x_1331_, 1, v_a_1314_);
lean_ctor_set(v___x_1331_, 2, v_a_1327_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1331_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_dec_ref_known(v_x_1247_, 1);
v___x_1336_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__0));
v___x_1337_ = l_Lean_Json_compress(v_val_1287_);
v___x_1338_ = lean_string_append(v___x_1336_, v___x_1337_);
lean_dec_ref(v___x_1337_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set_tag(v___x_1289_, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1338_);
v___x_1340_ = v___x_1289_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec(v___x_1286_);
v___x_1343_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__3));
v___x_1344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_kvPairs_1284_, v___x_1343_);
if (lean_obj_tag(v___x_1344_) == 1)
{
lean_object* v_val_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1366_; 
lean_dec_ref_known(v_x_1247_, 1);
v_val_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1366_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_val_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1366_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
if (lean_obj_tag(v_val_1345_) == 3)
{
lean_object* v_s_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1359_; 
v_s_1349_ = lean_ctor_get(v_val_1345_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_val_1345_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1351_ = v_val_1345_;
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_s_1349_);
lean_dec(v_val_1345_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set_tag(v___x_1351_, 2);
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_s_1349_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1354_);
v___x_1356_ = v___x_1347_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1360_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__0));
v___x_1361_ = l_Lean_Json_compress(v_val_1345_);
v___x_1362_ = lean_string_append(v___x_1360_, v___x_1361_);
lean_dec_ref(v___x_1361_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1362_);
v___x_1364_ = v___x_1347_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v___x_1344_);
v___x_1367_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__1));
v___x_1368_ = l_Lean_Json_compress(v_x_1247_);
v___x_1369_ = lean_string_append(v___x_1367_, v___x_1368_);
lean_dec_ref(v___x_1368_);
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
}
}
default: 
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1371_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__2));
v___x_1372_ = l_Lean_Json_compress(v_x_1247_);
v___x_1373_ = lean_string_append(v___x_1371_, v___x_1372_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0(size_t v_sz_1375_, size_t v_i_1376_, lean_object* v_bs_1377_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_usize_dec_lt(v_i_1376_, v_sz_1375_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_bs_1377_);
return v___x_1379_;
}
else
{
lean_object* v_v_1380_; lean_object* v___x_1381_; 
v_v_1380_ = lean_array_uget_borrowed(v_bs_1377_, v_i_1376_);
lean_inc(v_v_1380_);
v___x_1381_ = l_Lean_Html_instFromJson_from_x3f(v_v_1380_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v_bs_1377_);
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1391_; lean_object* v_bs_x27_1392_; size_t v___x_1393_; size_t v___x_1394_; lean_object* v___x_1395_; 
v_a_1390_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1391_ = lean_unsigned_to_nat(0u);
v_bs_x27_1392_ = lean_array_uset(v_bs_1377_, v_i_1376_, v___x_1391_);
v___x_1393_ = ((size_t)1ULL);
v___x_1394_ = lean_usize_add(v_i_1376_, v___x_1393_);
v___x_1395_ = lean_array_uset(v_bs_x27_1392_, v_i_1376_, v_a_1390_);
v_i_1376_ = v___x_1394_;
v_bs_1377_ = v___x_1395_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1375_ = stack[0].m_num;
size_t v_i_1376_ = stack[1].m_num;
lean_object* v_bs_1377_ = stack[2].m_obj;
lean_object* v_res_1397_;
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0(v_sz_1375_, v_i_1376_, v_bs_1377_);
stack->m_obj
 = v_res_1397_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0___boxed(lean_object* v_sz_1398_, lean_object* v_i_1399_, lean_object* v_bs_1400_){
_start:
{
size_t v_sz_boxed_1401_; size_t v_i_boxed_1402_; lean_object* v_res_1403_; 
v_sz_boxed_1401_ = lean_unbox_usize(v_sz_1398_);
lean_dec(v_sz_1398_);
v_i_boxed_1402_ = lean_unbox_usize(v_i_1399_);
lean_dec(v_i_1399_);
v_res_1403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0(v_sz_boxed_1401_, v_i_boxed_1402_, v_bs_1400_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1(lean_object* v_00_u03b4_1404_, lean_object* v_t_1405_, lean_object* v_k_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_t_1405_, v_k_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___boxed(lean_object* v_00_u03b4_1408_, lean_object* v_t_1409_, lean_object* v_k_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1(v_00_u03b4_1408_, v_t_1409_, v_k_1410_);
lean_dec_ref(v_k_1410_);
lean_dec(v_t_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instFromJson___lam__0(lean_object* v_j_1414_){
_start:
{
lean_object* v___x_1415_; 
lean_inc(v_j_1414_);
v___x_1415_ = l_Lean_Html_instFromJson_from_x3f(v_j_1414_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1429_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1429_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1429_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1420_ = ((lean_object*)(l_Lean_Html_instFromJson___lam__0___closed__0));
v___x_1421_ = l_Lean_Json_compress(v_j_1414_);
v___x_1422_ = lean_string_append(v___x_1420_, v___x_1421_);
lean_dec_ref(v___x_1421_);
v___x_1423_ = ((lean_object*)(l_Lean_Html_instFromJson___lam__0___closed__1));
v___x_1424_ = lean_string_append(v___x_1422_, v___x_1423_);
v___x_1425_ = lean_string_append(v___x_1424_, v_a_1416_);
lean_dec(v_a_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1425_);
v___x_1427_ = v___x_1418_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_dec(v_j_1414_);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1(lean_object* v_xs_1434_, lean_object* v_i_1435_, lean_object* v_args_1436_){
_start:
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = lean_array_get_size(v_xs_1434_);
v___x_1438_ = lean_nat_dec_lt(v_i_1435_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
lean_dec(v_i_1435_);
v___x_1439_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__0));
v___x_1440_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__1));
v___x_1441_ = l_Nat_reprFast(v___x_1437_);
v___x_1442_ = lean_string_append(v___x_1440_, v___x_1441_);
lean_dec_ref(v___x_1441_);
v___x_1443_ = l_Lean_Name_mkStr2(v___x_1439_, v___x_1442_);
v___x_1444_ = l_Lean_Syntax_mkCApp(v___x_1443_, v_args_1436_);
return v___x_1444_;
}
else
{
lean_object* v___x_1445_; lean_object* v_fst_1446_; lean_object* v_snd_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1445_ = lean_array_fget_borrowed(v_xs_1434_, v_i_1435_);
v_fst_1446_ = lean_ctor_get(v___x_1445_, 0);
v_snd_1447_ = lean_ctor_get(v___x_1445_, 1);
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_add(v_i_1435_, v___x_1448_);
lean_dec(v_i_1435_);
v___x_1450_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__5));
v___x_1451_ = lean_box(2);
lean_inc(v_fst_1446_);
v___x_1452_ = l_Lean_Syntax_mkStrLit(v_fst_1446_, v___x_1451_);
lean_inc(v_snd_1447_);
v___x_1453_ = l_Lean_Syntax_mkStrLit(v_snd_1447_, v___x_1451_);
v___x_1454_ = lean_unsigned_to_nat(2u);
v___x_1455_ = lean_mk_empty_array_with_capacity(v___x_1454_);
v___x_1456_ = lean_array_push(v___x_1455_, v___x_1452_);
v___x_1457_ = lean_array_push(v___x_1456_, v___x_1453_);
v___x_1458_ = l_Lean_Syntax_mkCApp(v___x_1450_, v___x_1457_);
v___x_1459_ = lean_array_push(v_args_1436_, v___x_1458_);
v_i_1435_ = v___x_1449_;
v_args_1436_ = v___x_1459_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___boxed(lean_object* v_xs_1461_, lean_object* v_i_1462_, lean_object* v_args_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1(v_xs_1461_, v_i_1462_, v_args_1463_);
lean_dec_ref(v_xs_1461_);
return v_res_1464_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__11));
v___x_1466_ = l_Lean_mkCIdent(v___x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0(lean_object* v_x_1467_){
_start:
{
if (lean_obj_tag(v_x_1467_) == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0, &l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0);
return v___x_1468_;
}
else
{
lean_object* v_head_1469_; lean_object* v_tail_1470_; lean_object* v_fst_1471_; lean_object* v_snd_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v_head_1469_ = lean_ctor_get(v_x_1467_, 0);
lean_inc(v_head_1469_);
v_tail_1470_ = lean_ctor_get(v_x_1467_, 1);
lean_inc(v_tail_1470_);
lean_dec_ref_known(v_x_1467_, 2);
v_fst_1471_ = lean_ctor_get(v_head_1469_, 0);
lean_inc(v_fst_1471_);
v_snd_1472_ = lean_ctor_get(v_head_1469_, 1);
lean_inc(v_snd_1472_);
lean_dec(v_head_1469_);
v___x_1473_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__15));
v___x_1474_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__5));
v___x_1475_ = lean_box(2);
v___x_1476_ = l_Lean_Syntax_mkStrLit(v_fst_1471_, v___x_1475_);
v___x_1477_ = l_Lean_Syntax_mkStrLit(v_snd_1472_, v___x_1475_);
v___x_1478_ = lean_unsigned_to_nat(2u);
v___x_1479_ = lean_mk_empty_array_with_capacity(v___x_1478_);
lean_inc_ref(v___x_1479_);
v___x_1480_ = lean_array_push(v___x_1479_, v___x_1476_);
v___x_1481_ = lean_array_push(v___x_1480_, v___x_1477_);
v___x_1482_ = l_Lean_Syntax_mkCApp(v___x_1474_, v___x_1481_);
v___x_1483_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0(v_tail_1470_);
v___x_1484_ = lean_array_push(v___x_1479_, v___x_1482_);
v___x_1485_ = lean_array_push(v___x_1484_, v___x_1483_);
v___x_1486_ = l_Lean_Syntax_mkCApp(v___x_1473_, v___x_1485_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0(lean_object* v_xs_1489_){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1490_ = lean_array_get_size(v_xs_1489_);
v___x_1491_ = lean_unsigned_to_nat(8u);
v___x_1492_ = lean_nat_dec_le(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1493_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__8));
v___x_1494_ = lean_array_to_list(v_xs_1489_);
v___x_1495_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0(v___x_1494_);
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = lean_mk_empty_array_with_capacity(v___x_1496_);
v___x_1498_ = lean_array_push(v___x_1497_, v___x_1495_);
v___x_1499_ = l_Lean_Syntax_mkCApp(v___x_1493_, v___x_1498_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = lean_unsigned_to_nat(0u);
v___x_1501_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__0));
v___x_1502_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1(v_xs_1489_, v___x_1500_, v___x_1501_);
lean_dec_ref(v_xs_1489_);
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__3(lean_object* v_x_1503_){
_start:
{
if (lean_obj_tag(v_x_1503_) == 0)
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0, &l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0);
return v___x_1504_;
}
else
{
lean_object* v_head_1505_; lean_object* v_tail_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_head_1505_ = lean_ctor_get(v_x_1503_, 0);
lean_inc(v_head_1505_);
v_tail_1506_ = lean_ctor_get(v_x_1503_, 1);
lean_inc(v_tail_1506_);
lean_dec_ref_known(v_x_1503_, 2);
v___x_1507_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__15));
v___x_1508_ = l_Lean_Html_instQuoteMkStr1_q(v_head_1505_);
v___x_1509_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__3(v_tail_1506_);
v___x_1510_ = lean_unsigned_to_nat(2u);
v___x_1511_ = lean_mk_empty_array_with_capacity(v___x_1510_);
v___x_1512_ = lean_array_push(v___x_1511_, v___x_1508_);
v___x_1513_ = lean_array_push(v___x_1512_, v___x_1509_);
v___x_1514_ = l_Lean_Syntax_mkCApp(v___x_1507_, v___x_1513_);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1(lean_object* v_xs_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1516_ = lean_array_get_size(v_xs_1515_);
v___x_1517_ = lean_unsigned_to_nat(8u);
v___x_1518_ = lean_nat_dec_le(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1519_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__8));
v___x_1520_ = lean_array_to_list(v_xs_1515_);
v___x_1521_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__3(v___x_1520_);
v___x_1522_ = lean_unsigned_to_nat(1u);
v___x_1523_ = lean_mk_empty_array_with_capacity(v___x_1522_);
v___x_1524_ = lean_array_push(v___x_1523_, v___x_1521_);
v___x_1525_ = l_Lean_Syntax_mkCApp(v___x_1519_, v___x_1524_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__0));
v___x_1528_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4(v_xs_1515_, v___x_1526_, v___x_1527_);
lean_dec_ref(v_xs_1515_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instQuoteMkStr1_q(lean_object* v_x_1529_){
_start:
{
switch(lean_obj_tag(v_x_1529_))
{
case 0:
{
lean_object* v_tag_1530_; lean_object* v_attrs_1531_; lean_object* v_children_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_tag_1530_ = lean_ctor_get(v_x_1529_, 0);
lean_inc_ref(v_tag_1530_);
v_attrs_1531_ = lean_ctor_get(v_x_1529_, 1);
lean_inc_ref(v_attrs_1531_);
v_children_1532_ = lean_ctor_get(v_x_1529_, 2);
lean_inc_ref(v_children_1532_);
lean_dec_ref_known(v_x_1529_, 3);
v___x_1533_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__1));
v___x_1534_ = lean_box(2);
v___x_1535_ = l_Lean_Syntax_mkStrLit(v_tag_1530_, v___x_1534_);
v___x_1536_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0(v_attrs_1531_);
v___x_1537_ = l_Lean_Html_instQuoteMkStr1_q(v_children_1532_);
v___x_1538_ = lean_unsigned_to_nat(3u);
v___x_1539_ = lean_mk_empty_array_with_capacity(v___x_1538_);
v___x_1540_ = lean_array_push(v___x_1539_, v___x_1535_);
v___x_1541_ = lean_array_push(v___x_1540_, v___x_1536_);
v___x_1542_ = lean_array_push(v___x_1541_, v___x_1537_);
v___x_1543_ = l_Lean_Syntax_mkCApp(v___x_1533_, v___x_1542_);
return v___x_1543_;
}
case 1:
{
lean_object* v_a_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_a_1544_ = lean_ctor_get(v_x_1529_, 0);
lean_inc_ref(v_a_1544_);
lean_dec_ref_known(v_x_1529_, 1);
v___x_1545_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__19));
v___x_1546_ = lean_box(2);
v___x_1547_ = l_Lean_Syntax_mkStrLit(v_a_1544_, v___x_1546_);
v___x_1548_ = lean_unsigned_to_nat(1u);
v___x_1549_ = lean_mk_empty_array_with_capacity(v___x_1548_);
v___x_1550_ = lean_array_push(v___x_1549_, v___x_1547_);
v___x_1551_ = l_Lean_Syntax_mkCApp(v___x_1545_, v___x_1550_);
return v___x_1551_;
}
case 2:
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_a_1552_ = lean_ctor_get(v_x_1529_, 0);
lean_inc_ref(v_a_1552_);
lean_dec_ref_known(v_x_1529_, 1);
v___x_1553_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__22));
v___x_1554_ = lean_box(2);
v___x_1555_ = l_Lean_Syntax_mkStrLit(v_a_1552_, v___x_1554_);
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_mk_empty_array_with_capacity(v___x_1556_);
v___x_1558_ = lean_array_push(v___x_1557_, v___x_1555_);
v___x_1559_ = l_Lean_Syntax_mkCApp(v___x_1553_, v___x_1558_);
return v___x_1559_;
}
default: 
{
lean_object* v_a_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_a_1560_ = lean_ctor_get(v_x_1529_, 0);
lean_inc_ref(v_a_1560_);
lean_dec_ref_known(v_x_1529_, 1);
v___x_1561_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__26));
v___x_1562_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1(v_a_1560_);
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = lean_mk_empty_array_with_capacity(v___x_1563_);
v___x_1565_ = lean_array_push(v___x_1564_, v___x_1562_);
v___x_1566_ = l_Lean_Syntax_mkCApp(v___x_1561_, v___x_1565_);
return v___x_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4(lean_object* v_xs_1567_, lean_object* v_i_1568_, lean_object* v_args_1569_){
_start:
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = lean_array_get_size(v_xs_1567_);
v___x_1571_ = lean_nat_dec_lt(v_i_1568_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_dec(v_i_1568_);
v___x_1572_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__0));
v___x_1573_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__1));
v___x_1574_ = l_Nat_reprFast(v___x_1570_);
v___x_1575_ = lean_string_append(v___x_1573_, v___x_1574_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = l_Lean_Name_mkStr2(v___x_1572_, v___x_1575_);
v___x_1577_ = l_Lean_Syntax_mkCApp(v___x_1576_, v_args_1569_);
return v___x_1577_;
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_add(v_i_1568_, v___x_1578_);
v___x_1580_ = lean_array_fget_borrowed(v_xs_1567_, v_i_1568_);
lean_dec(v_i_1568_);
lean_inc(v___x_1580_);
v___x_1581_ = l_Lean_Html_instQuoteMkStr1_q(v___x_1580_);
v___x_1582_ = lean_array_push(v_args_1569_, v___x_1581_);
v_i_1568_ = v___x_1579_;
v_args_1569_ = v___x_1582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4___boxed(lean_object* v_xs_1584_, lean_object* v_i_1585_, lean_object* v_args_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4(v_xs_1584_, v_i_1585_, v_args_1586_);
lean_dec_ref(v_xs_1584_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg___lam__0(lean_object* v_tag_1590_, lean_object* v_attrs_1591_, lean_object* v_fn_1592_, lean_object* v_children_x27_1593_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1594_, 0, v_tag_1590_);
lean_ctor_set(v___x_1594_, 1, v_attrs_1591_);
lean_ctor_set(v___x_1594_, 2, v_children_x27_1593_);
v___x_1595_ = lean_apply_1(v_fn_1592_, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg___lam__1(lean_object* v_fn_1596_, lean_object* v_s_x27_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_s_x27_1597_);
v___x_1599_ = lean_apply_1(v_fn_1596_, v___x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg(lean_object* v_inst_1600_, lean_object* v_fn_1601_, lean_object* v_x_1602_){
_start:
{
switch(lean_obj_tag(v_x_1602_))
{
case 0:
{
lean_object* v_toBind_1603_; lean_object* v_tag_1604_; lean_object* v_attrs_1605_; lean_object* v_children_1606_; lean_object* v___f_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_toBind_1603_ = lean_ctor_get(v_inst_1600_, 1);
lean_inc(v_toBind_1603_);
v_tag_1604_ = lean_ctor_get(v_x_1602_, 0);
lean_inc_ref(v_tag_1604_);
v_attrs_1605_ = lean_ctor_get(v_x_1602_, 1);
lean_inc_ref(v_attrs_1605_);
v_children_1606_ = lean_ctor_get(v_x_1602_, 2);
lean_inc_ref(v_children_1606_);
lean_dec_ref_known(v_x_1602_, 3);
lean_inc(v_fn_1601_);
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_Html_rewritePostM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1607_, 0, v_tag_1604_);
lean_closure_set(v___f_1607_, 1, v_attrs_1605_);
lean_closure_set(v___f_1607_, 2, v_fn_1601_);
v___x_1608_ = l_Lean_Html_rewritePostM___redArg(v_inst_1600_, v_fn_1601_, v_children_1606_);
v___x_1609_ = lean_apply_4(v_toBind_1603_, lean_box(0), lean_box(0), v___x_1608_, v___f_1607_);
return v___x_1609_;
}
case 3:
{
lean_object* v_toBind_1610_; lean_object* v_a_1611_; lean_object* v___f_1612_; lean_object* v___x_1613_; size_t v_sz_1614_; size_t v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v_toBind_1610_ = lean_ctor_get(v_inst_1600_, 1);
lean_inc(v_toBind_1610_);
v_a_1611_ = lean_ctor_get(v_x_1602_, 0);
lean_inc_ref(v_a_1611_);
lean_dec_ref_known(v_x_1602_, 1);
lean_inc(v_fn_1601_);
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_Html_rewritePostM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1612_, 0, v_fn_1601_);
lean_inc_ref(v_inst_1600_);
v___x_1613_ = lean_alloc_closure((void*)(l_Lean_Html_rewritePostM___redArg), 3, 2);
lean_closure_set(v___x_1613_, 0, v_inst_1600_);
lean_closure_set(v___x_1613_, 1, v_fn_1601_);
v_sz_1614_ = lean_array_size(v_a_1611_);
v___x_1615_ = ((size_t)0ULL);
v___x_1616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1600_, v___x_1613_, v_sz_1614_, v___x_1615_, v_a_1611_);
v___x_1617_ = lean_apply_4(v_toBind_1610_, lean_box(0), lean_box(0), v___x_1616_, v___f_1612_);
return v___x_1617_;
}
default: 
{
lean_object* v___x_1618_; 
lean_dec_ref(v_inst_1600_);
v___x_1618_ = lean_apply_1(v_fn_1601_, v_x_1602_);
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM(lean_object* v_m_1619_, lean_object* v_inst_1620_, lean_object* v_fn_1621_, lean_object* v_x_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Html_rewritePostM___redArg(v_inst_1620_, v_fn_1621_, v_x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(lean_object* v_fn_1624_, lean_object* v_x_1625_){
_start:
{
switch(lean_obj_tag(v_x_1625_))
{
case 0:
{
lean_object* v_tag_1626_; lean_object* v_attrs_1627_; lean_object* v_children_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1637_; 
v_tag_1626_ = lean_ctor_get(v_x_1625_, 0);
v_attrs_1627_ = lean_ctor_get(v_x_1625_, 1);
v_children_1628_ = lean_ctor_get(v_x_1625_, 2);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_x_1625_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1630_ = v_x_1625_;
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_children_1628_);
lean_inc(v_attrs_1627_);
lean_inc(v_tag_1626_);
lean_dec(v_x_1625_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1634_; 
lean_inc_ref(v_fn_1624_);
v___x_1632_ = l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(v_fn_1624_, v_children_1628_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 2, v___x_1632_);
v___x_1634_ = v___x_1630_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_tag_1626_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_attrs_1627_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_apply_1(v_fn_1624_, v___x_1634_);
return v___x_1635_;
}
}
}
case 3:
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1649_; 
v_a_1638_ = lean_ctor_get(v_x_1625_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_x_1625_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1640_ = v_x_1625_;
v_isShared_1641_ = v_isSharedCheck_1649_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v_x_1625_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1649_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
size_t v_sz_1642_; size_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v_sz_1642_ = lean_array_size(v_a_1638_);
v___x_1643_ = ((size_t)0ULL);
lean_inc_ref(v_fn_1624_);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0(v_fn_1624_, v_sz_1642_, v___x_1643_, v_a_1638_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1644_);
v___x_1646_ = v___x_1640_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_apply_1(v_fn_1624_, v___x_1646_);
return v___x_1647_;
}
}
}
default: 
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_apply_1(v_fn_1624_, v_x_1625_);
return v___x_1650_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0(lean_object* v_fn_1651_, size_t v_sz_1652_, size_t v_i_1653_, lean_object* v_bs_1654_){
_start:
{
uint8_t v___x_1655_; 
v___x_1655_ = lean_usize_dec_lt(v_i_1653_, v_sz_1652_);
if (v___x_1655_ == 0)
{
lean_dec_ref(v_fn_1651_);
return v_bs_1654_;
}
else
{
lean_object* v_v_1656_; lean_object* v___x_1657_; lean_object* v_bs_x27_1658_; lean_object* v___x_1659_; size_t v___x_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v_v_1656_ = lean_array_uget(v_bs_1654_, v_i_1653_);
v___x_1657_ = lean_unsigned_to_nat(0u);
v_bs_x27_1658_ = lean_array_uset(v_bs_1654_, v_i_1653_, v___x_1657_);
lean_inc_ref(v_fn_1651_);
v___x_1659_ = l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(v_fn_1651_, v_v_1656_);
v___x_1660_ = ((size_t)1ULL);
v___x_1661_ = lean_usize_add(v_i_1653_, v___x_1660_);
v___x_1662_ = lean_array_uset(v_bs_x27_1658_, v_i_1653_, v___x_1659_);
v_i_1653_ = v___x_1661_;
v_bs_1654_ = v___x_1662_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1651_ = stack[0].m_obj;
size_t v_sz_1652_ = stack[1].m_num;
size_t v_i_1653_ = stack[2].m_num;
lean_object* v_bs_1654_ = stack[3].m_obj;
lean_object* v_res_1664_;
v_res_1664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0(v_fn_1651_, v_sz_1652_, v_i_1653_, v_bs_1654_);
stack->m_obj
 = v_res_1664_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0___boxed(lean_object* v_fn_1665_, lean_object* v_sz_1666_, lean_object* v_i_1667_, lean_object* v_bs_1668_){
_start:
{
size_t v_sz_boxed_1669_; size_t v_i_boxed_1670_; lean_object* v_res_1671_; 
v_sz_boxed_1669_ = lean_unbox_usize(v_sz_1666_);
lean_dec(v_sz_1666_);
v_i_boxed_1670_ = lean_unbox_usize(v_i_1667_);
lean_dec(v_i_1667_);
v_res_1671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0(v_fn_1665_, v_sz_boxed_1669_, v_i_boxed_1670_, v_bs_1668_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePost(lean_object* v_fn_1672_, lean_object* v_h_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(v_fn_1672_, v_h_1673_);
return v___x_1674_;
}
}
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Mem(uint8_t builtin);
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_Elab(uint8_t builtin);
lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin);
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
res = runtime_initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instToExprHtml = _init_l_Lean_instToExprHtml();
lean_mark_persistent(l_Lean_instToExprHtml);
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
lean_object* initialize_Lean_ToExpr(uint8_t builtin);
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
res = initialize_Lean_ToExpr(builtin);
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
