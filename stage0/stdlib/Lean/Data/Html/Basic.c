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
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_00_u03b1Type_573_; 
v___x_571_ = lean_box(0);
v___x_572_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__1));
v_00_u03b1Type_573_ = l_Lean_mkConst(v___x_572_, v___x_571_);
return v_00_u03b1Type_573_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__8(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__7));
v___x_586_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__5));
v___x_587_ = l_Lean_mkConst(v___x_586_, v___x_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0(lean_object* v_nilFn_588_, lean_object* v_consFn_589_, lean_object* v_x_590_){
_start:
{
if (lean_obj_tag(v_x_590_) == 0)
{
lean_dec_ref(v_consFn_589_);
lean_inc_ref(v_nilFn_588_);
return v_nilFn_588_;
}
else
{
lean_object* v_head_591_; lean_object* v_tail_592_; lean_object* v_fst_593_; lean_object* v_snd_594_; lean_object* v_00_u03b1Type_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_head_591_ = lean_ctor_get(v_x_590_, 0);
lean_inc(v_head_591_);
v_tail_592_ = lean_ctor_get(v_x_590_, 1);
lean_inc(v_tail_592_);
lean_dec_ref_known(v_x_590_, 2);
v_fst_593_ = lean_ctor_get(v_head_591_, 0);
lean_inc(v_fst_593_);
v_snd_594_ = lean_ctor_get(v_head_591_, 1);
lean_inc(v_snd_594_);
lean_dec(v_head_591_);
v_00_u03b1Type_595_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2);
v___x_596_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__8, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__8_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__8);
v___x_597_ = l_Lean_mkStrLit(v_fst_593_);
v___x_598_ = l_Lean_mkStrLit(v_snd_594_);
v___x_599_ = l_Lean_mkApp4(v___x_596_, v_00_u03b1Type_595_, v_00_u03b1Type_595_, v___x_597_, v___x_598_);
lean_inc_ref(v_consFn_589_);
v___x_600_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0(v_nilFn_588_, v_consFn_589_, v_tail_592_);
v___x_601_ = l_Lean_mkAppB(v_consFn_589_, v___x_599_, v___x_600_);
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___boxed(lean_object* v_nilFn_602_, lean_object* v_consFn_603_, lean_object* v_x_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0(v_nilFn_602_, v_consFn_603_, v_x_604_);
lean_dec_ref(v_nilFn_602_);
return v_res_605_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__2(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_box(0);
v___x_612_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__1));
v___x_613_ = l_Lean_Expr_const___override(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__4(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__7));
v___x_617_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__3));
v___x_618_ = l_Lean_mkConst(v___x_617_, v___x_616_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__5(void){
_start:
{
lean_object* v_00_u03b1Type_619_; lean_object* v___x_620_; lean_object* v_type_621_; 
v_00_u03b1Type_619_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__2);
v___x_620_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__4, &l_Lean_instToExprHtml_toExpr___closed__4_once, _init_l_Lean_instToExprHtml_toExpr___closed__4);
v_type_621_ = l_Lean_mkAppB(v___x_620_, v_00_u03b1Type_619_, v_00_u03b1Type_619_);
return v_type_621_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__9(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__6));
v___x_628_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__8));
v___x_629_ = l_Lean_mkConst(v___x_628_, v___x_627_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__12(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__6));
v___x_635_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__11));
v___x_636_ = l_Lean_mkConst(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__13(void){
_start:
{
lean_object* v_type_637_; lean_object* v___x_638_; lean_object* v_nil_639_; 
v_type_637_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__5, &l_Lean_instToExprHtml_toExpr___closed__5_once, _init_l_Lean_instToExprHtml_toExpr___closed__5);
v___x_638_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__12, &l_Lean_instToExprHtml_toExpr___closed__12_once, _init_l_Lean_instToExprHtml_toExpr___closed__12);
v_nil_639_ = l_Lean_Expr_app___override(v___x_638_, v_type_637_);
return v_nil_639_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__16(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__6));
v___x_645_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__15));
v___x_646_ = l_Lean_mkConst(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__17(void){
_start:
{
lean_object* v_type_647_; lean_object* v___x_648_; lean_object* v_cons_649_; 
v_type_647_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__5, &l_Lean_instToExprHtml_toExpr___closed__5_once, _init_l_Lean_instToExprHtml_toExpr___closed__5);
v___x_648_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__16, &l_Lean_instToExprHtml_toExpr___closed__16_once, _init_l_Lean_instToExprHtml_toExpr___closed__16);
v_cons_649_ = l_Lean_Expr_app___override(v___x_648_, v_type_647_);
return v_cons_649_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__20(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_box(0);
v___x_656_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__19));
v___x_657_ = l_Lean_Expr_const___override(v___x_656_, v___x_655_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__23(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_box(0);
v___x_664_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__22));
v___x_665_ = l_Lean_Expr_const___override(v___x_664_, v___x_663_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__24(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_type_668_; 
v___x_666_ = lean_box(0);
v___x_667_ = ((lean_object*)(l_Lean_instImpl___closed__2_00___x40_Lean_Data_Html_Basic_2686543190____hygCtx___hyg_140_));
v_type_668_ = l_Lean_Expr_const___override(v___x_667_, v___x_666_);
return v_type_668_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__27(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_box(0);
v___x_675_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__26));
v___x_676_ = l_Lean_Expr_const___override(v___x_675_, v___x_674_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__28(void){
_start:
{
lean_object* v_type_677_; lean_object* v___x_678_; lean_object* v_nil_679_; 
v_type_677_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__24, &l_Lean_instToExprHtml_toExpr___closed__24_once, _init_l_Lean_instToExprHtml_toExpr___closed__24);
v___x_678_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__12, &l_Lean_instToExprHtml_toExpr___closed__12_once, _init_l_Lean_instToExprHtml_toExpr___closed__12);
v_nil_679_ = l_Lean_Expr_app___override(v___x_678_, v_type_677_);
return v_nil_679_;
}
}
static lean_object* _init_l_Lean_instToExprHtml_toExpr___closed__29(void){
_start:
{
lean_object* v_type_680_; lean_object* v___x_681_; lean_object* v_cons_682_; 
v_type_680_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__24, &l_Lean_instToExprHtml_toExpr___closed__24_once, _init_l_Lean_instToExprHtml_toExpr___closed__24);
v___x_681_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__16, &l_Lean_instToExprHtml_toExpr___closed__16_once, _init_l_Lean_instToExprHtml_toExpr___closed__16);
v_cons_682_ = l_Lean_Expr_app___override(v___x_681_, v_type_680_);
return v_cons_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprHtml_toExpr(lean_object* v_x_683_){
_start:
{
switch(lean_obj_tag(v_x_683_))
{
case 0:
{
lean_object* v_tag_684_; lean_object* v_attrs_685_; lean_object* v_children_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_type_690_; lean_object* v___x_691_; lean_object* v_nil_692_; lean_object* v_cons_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_tag_684_ = lean_ctor_get(v_x_683_, 0);
lean_inc_ref(v_tag_684_);
v_attrs_685_ = lean_ctor_get(v_x_683_, 1);
lean_inc_ref(v_attrs_685_);
v_children_686_ = lean_ctor_get(v_x_683_, 2);
lean_inc_ref(v_children_686_);
lean_dec_ref_known(v_x_683_, 3);
v___x_687_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__2, &l_Lean_instToExprHtml_toExpr___closed__2_once, _init_l_Lean_instToExprHtml_toExpr___closed__2);
v___x_688_ = l_Lean_mkStrLit(v_tag_684_);
v___x_689_ = l_Lean_Expr_app___override(v___x_687_, v___x_688_);
v_type_690_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__5, &l_Lean_instToExprHtml_toExpr___closed__5_once, _init_l_Lean_instToExprHtml_toExpr___closed__5);
v___x_691_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__9, &l_Lean_instToExprHtml_toExpr___closed__9_once, _init_l_Lean_instToExprHtml_toExpr___closed__9);
v_nil_692_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__13, &l_Lean_instToExprHtml_toExpr___closed__13_once, _init_l_Lean_instToExprHtml_toExpr___closed__13);
v_cons_693_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__17, &l_Lean_instToExprHtml_toExpr___closed__17_once, _init_l_Lean_instToExprHtml_toExpr___closed__17);
v___x_694_ = lean_array_to_list(v_attrs_685_);
v___x_695_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0(v_nil_692_, v_cons_693_, v___x_694_);
v___x_696_ = l_Lean_mkAppB(v___x_691_, v_type_690_, v___x_695_);
v___x_697_ = l_Lean_Expr_app___override(v___x_689_, v___x_696_);
v___x_698_ = l_Lean_instToExprHtml_toExpr(v_children_686_);
v___x_699_ = l_Lean_Expr_app___override(v___x_697_, v___x_698_);
return v___x_699_;
}
case 1:
{
lean_object* v_a_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_a_700_ = lean_ctor_get(v_x_683_, 0);
lean_inc_ref(v_a_700_);
lean_dec_ref_known(v_x_683_, 1);
v___x_701_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__20, &l_Lean_instToExprHtml_toExpr___closed__20_once, _init_l_Lean_instToExprHtml_toExpr___closed__20);
v___x_702_ = l_Lean_mkStrLit(v_a_700_);
v___x_703_ = l_Lean_Expr_app___override(v___x_701_, v___x_702_);
return v___x_703_;
}
case 2:
{
lean_object* v_a_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_a_704_ = lean_ctor_get(v_x_683_, 0);
lean_inc_ref(v_a_704_);
lean_dec_ref_known(v_x_683_, 1);
v___x_705_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__23, &l_Lean_instToExprHtml_toExpr___closed__23_once, _init_l_Lean_instToExprHtml_toExpr___closed__23);
v___x_706_ = l_Lean_mkStrLit(v_a_704_);
v___x_707_ = l_Lean_Expr_app___override(v___x_705_, v___x_706_);
return v___x_707_;
}
default: 
{
lean_object* v_a_708_; lean_object* v_type_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_nil_712_; lean_object* v_cons_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_a_708_ = lean_ctor_get(v_x_683_, 0);
lean_inc_ref(v_a_708_);
lean_dec_ref_known(v_x_683_, 1);
v_type_709_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__24, &l_Lean_instToExprHtml_toExpr___closed__24_once, _init_l_Lean_instToExprHtml_toExpr___closed__24);
v___x_710_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__27, &l_Lean_instToExprHtml_toExpr___closed__27_once, _init_l_Lean_instToExprHtml_toExpr___closed__27);
v___x_711_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__9, &l_Lean_instToExprHtml_toExpr___closed__9_once, _init_l_Lean_instToExprHtml_toExpr___closed__9);
v_nil_712_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__28, &l_Lean_instToExprHtml_toExpr___closed__28_once, _init_l_Lean_instToExprHtml_toExpr___closed__28);
v_cons_713_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__29, &l_Lean_instToExprHtml_toExpr___closed__29_once, _init_l_Lean_instToExprHtml_toExpr___closed__29);
v___x_714_ = lean_array_to_list(v_a_708_);
v___x_715_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1(v_nil_712_, v_cons_713_, v___x_714_);
v___x_716_ = l_Lean_mkAppB(v___x_711_, v_type_709_, v___x_715_);
v___x_717_ = l_Lean_Expr_app___override(v___x_710_, v___x_716_);
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1(lean_object* v_nilFn_718_, lean_object* v_consFn_719_, lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 0)
{
lean_dec_ref(v_consFn_719_);
lean_inc_ref(v_nilFn_718_);
return v_nilFn_718_;
}
else
{
lean_object* v_head_721_; lean_object* v_tail_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_head_721_ = lean_ctor_get(v_x_720_, 0);
lean_inc(v_head_721_);
v_tail_722_ = lean_ctor_get(v_x_720_, 1);
lean_inc(v_tail_722_);
lean_dec_ref_known(v_x_720_, 2);
v___x_723_ = l_Lean_instToExprHtml_toExpr(v_head_721_);
lean_inc_ref(v_consFn_719_);
v___x_724_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1(v_nilFn_718_, v_consFn_719_, v_tail_722_);
v___x_725_ = l_Lean_mkAppB(v_consFn_719_, v___x_723_, v___x_724_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1___boxed(lean_object* v_nilFn_726_, lean_object* v_consFn_727_, lean_object* v_x_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__1(v_nilFn_726_, v_consFn_727_, v_x_728_);
lean_dec_ref(v_nilFn_726_);
return v_res_729_;
}
}
static lean_object* _init_l_Lean_instToExprHtml___closed__1(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_obj_once(&l_Lean_instToExprHtml_toExpr___closed__24, &l_Lean_instToExprHtml_toExpr___closed__24_once, _init_l_Lean_instToExprHtml_toExpr___closed__24);
v___x_732_ = ((lean_object*)(l_Lean_instToExprHtml___closed__0));
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_instToExprHtml(void){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_obj_once(&l_Lean_instToExprHtml___closed__1, &l_Lean_instToExprHtml___closed__1_once, _init_l_Lean_instToExprHtml___closed__1);
return v___x_734_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_isEmpty(lean_object* v_x_740_){
_start:
{
lean_object* v_s_742_; 
switch(lean_obj_tag(v_x_740_))
{
case 0:
{
uint8_t v___x_746_; 
v___x_746_ = 0;
return v___x_746_;
}
case 3:
{
lean_object* v_a_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_a_747_ = lean_ctor_get(v_x_740_, 0);
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_array_get_size(v_a_747_);
v___x_750_ = lean_nat_dec_lt(v___x_748_, v___x_749_);
if (v___x_750_ == 0)
{
uint8_t v___x_751_; 
v___x_751_ = 1;
return v___x_751_;
}
else
{
if (v___x_750_ == 0)
{
return v___x_750_;
}
else
{
size_t v___x_752_; size_t v___x_753_; uint8_t v___x_754_; 
v___x_752_ = ((size_t)0ULL);
v___x_753_ = lean_usize_of_nat(v___x_749_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0(v_a_747_, v___x_752_, v___x_753_);
if (v___x_754_ == 0)
{
return v___x_750_;
}
else
{
uint8_t v___x_755_; 
v___x_755_ = 0;
return v___x_755_;
}
}
}
}
default: 
{
lean_object* v_a_756_; 
v_a_756_ = lean_ctor_get(v_x_740_, 0);
v_s_742_ = v_a_756_;
goto v___jp_741_;
}
}
v___jp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_string_utf8_byte_size(v_s_742_);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_nat_dec_eq(v___x_743_, v___x_744_);
return v___x_745_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0(lean_object* v_as_757_, size_t v_i_758_, size_t v_stop_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_eq(v_i_758_, v_stop_759_);
if (v___x_760_ == 0)
{
lean_object* v_val_761_; uint8_t v___x_762_; 
v_val_761_ = lean_array_uget_borrowed(v_as_757_, v_i_758_);
v___x_762_ = l_Lean_Html_isEmpty(v_val_761_);
if (v___x_762_ == 0)
{
uint8_t v___x_763_; 
v___x_763_ = 1;
return v___x_763_;
}
else
{
size_t v___x_764_; size_t v___x_765_; 
v___x_764_ = ((size_t)1ULL);
v___x_765_ = lean_usize_add(v_i_758_, v___x_764_);
v_i_758_ = v___x_765_;
goto _start;
}
}
else
{
uint8_t v___x_767_; 
v___x_767_ = 0;
return v___x_767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0___boxed(lean_object* v_as_768_, lean_object* v_i_769_, lean_object* v_stop_770_){
_start:
{
size_t v_i_boxed_771_; size_t v_stop_boxed_772_; uint8_t v_res_773_; lean_object* v_r_774_; 
v_i_boxed_771_ = lean_unbox_usize(v_i_769_);
lean_dec(v_i_769_);
v_stop_boxed_772_ = lean_unbox_usize(v_stop_770_);
lean_dec(v_stop_770_);
v_res_773_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Html_isEmpty_spec__0(v_as_768_, v_i_boxed_771_, v_stop_boxed_772_);
lean_dec_ref(v_as_768_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_isEmpty___boxed(lean_object* v_x_775_){
_start:
{
uint8_t v_res_776_; lean_object* v_r_777_; 
v_res_776_ = l_Lean_Html_isEmpty(v_x_775_);
lean_dec_ref(v_x_775_);
v_r_777_ = lean_box(v_res_776_);
return v_r_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__3_splitter___redArg(lean_object* v_x_778_, lean_object* v_h__1_779_, lean_object* v_h__2_780_, lean_object* v_h__3_781_, lean_object* v_h__4_782_){
_start:
{
switch(lean_obj_tag(v_x_778_))
{
case 0:
{
lean_object* v_tag_783_; lean_object* v_attrs_784_; lean_object* v_children_785_; lean_object* v___x_786_; 
lean_dec(v_h__3_781_);
lean_dec(v_h__2_780_);
lean_dec(v_h__1_779_);
v_tag_783_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_tag_783_);
v_attrs_784_ = lean_ctor_get(v_x_778_, 1);
lean_inc_ref(v_attrs_784_);
v_children_785_ = lean_ctor_get(v_x_778_, 2);
lean_inc_ref(v_children_785_);
lean_dec_ref_known(v_x_778_, 3);
v___x_786_ = lean_apply_3(v_h__4_782_, v_tag_783_, v_attrs_784_, v_children_785_);
return v___x_786_;
}
case 1:
{
lean_object* v_a_787_; lean_object* v___x_788_; 
lean_dec(v_h__4_782_);
lean_dec(v_h__3_781_);
lean_dec(v_h__1_779_);
v_a_787_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_a_787_);
lean_dec_ref_known(v_x_778_, 1);
v___x_788_ = lean_apply_1(v_h__2_780_, v_a_787_);
return v___x_788_;
}
case 2:
{
lean_object* v_a_789_; lean_object* v___x_790_; 
lean_dec(v_h__4_782_);
lean_dec(v_h__2_780_);
lean_dec(v_h__1_779_);
v_a_789_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_a_789_);
lean_dec_ref_known(v_x_778_, 1);
v___x_790_ = lean_apply_1(v_h__3_781_, v_a_789_);
return v___x_790_;
}
default: 
{
lean_object* v_a_791_; lean_object* v___x_792_; 
lean_dec(v_h__4_782_);
lean_dec(v_h__3_781_);
lean_dec(v_h__2_780_);
v_a_791_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_a_791_);
lean_dec_ref_known(v_x_778_, 1);
v___x_792_ = lean_apply_1(v_h__1_779_, v_a_791_);
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__3_splitter(lean_object* v_motive_793_, lean_object* v_x_794_, lean_object* v_h__1_795_, lean_object* v_h__2_796_, lean_object* v_h__3_797_, lean_object* v_h__4_798_){
_start:
{
switch(lean_obj_tag(v_x_794_))
{
case 0:
{
lean_object* v_tag_799_; lean_object* v_attrs_800_; lean_object* v_children_801_; lean_object* v___x_802_; 
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_tag_799_ = lean_ctor_get(v_x_794_, 0);
lean_inc_ref(v_tag_799_);
v_attrs_800_ = lean_ctor_get(v_x_794_, 1);
lean_inc_ref(v_attrs_800_);
v_children_801_ = lean_ctor_get(v_x_794_, 2);
lean_inc_ref(v_children_801_);
lean_dec_ref_known(v_x_794_, 3);
v___x_802_ = lean_apply_3(v_h__4_798_, v_tag_799_, v_attrs_800_, v_children_801_);
return v___x_802_;
}
case 1:
{
lean_object* v_a_803_; lean_object* v___x_804_; 
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__1_795_);
v_a_803_ = lean_ctor_get(v_x_794_, 0);
lean_inc_ref(v_a_803_);
lean_dec_ref_known(v_x_794_, 1);
v___x_804_ = lean_apply_1(v_h__2_796_, v_a_803_);
return v___x_804_;
}
case 2:
{
lean_object* v_a_805_; lean_object* v___x_806_; 
lean_dec(v_h__4_798_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_a_805_ = lean_ctor_get(v_x_794_, 0);
lean_inc_ref(v_a_805_);
lean_dec_ref_known(v_x_794_, 1);
v___x_806_ = lean_apply_1(v_h__3_797_, v_a_805_);
return v___x_806_;
}
default: 
{
lean_object* v_a_807_; lean_object* v___x_808_; 
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
v_a_807_ = lean_ctor_get(v_x_794_, 0);
lean_inc_ref(v_a_807_);
lean_dec_ref_known(v_x_794_, 1);
v___x_808_ = lean_apply_1(v_h__1_795_, v_a_807_);
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter___redArg(lean_object* v_x_809_, lean_object* v_h__1_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = lean_apply_2(v_h__1_810_, v_x_809_, lean_box(0));
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter(lean_object* v_a_812_, lean_object* v_motive_813_, lean_object* v_x_814_, lean_object* v_h__1_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = lean_apply_2(v_h__1_815_, v_x_814_, lean_box(0));
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter___boxed(lean_object* v_a_817_, lean_object* v_motive_818_, lean_object* v_x_819_, lean_object* v_h__1_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Data_Html_Basic_0__Lean_Html_isEmpty_match__1_splitter(v_a_817_, v_motive_818_, v_x_819_, v_h__1_820_);
lean_dec_ref(v_a_817_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofString(uint8_t v_escape_822_, lean_object* v_a_823_){
_start:
{
if (v_escape_822_ == 0)
{
lean_object* v___x_824_; 
v___x_824_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_824_, 0, v_a_823_);
return v___x_824_;
}
else
{
lean_object* v___x_825_; 
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v_a_823_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofString___boxed(lean_object* v_escape_826_, lean_object* v_a_827_){
_start:
{
uint8_t v_escape_boxed_828_; lean_object* v_res_829_; 
v_escape_boxed_828_ = lean_unbox(v_escape_826_);
v_res_829_ = l_Lean_Html_ofString(v_escape_boxed_828_, v_a_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instCoeString___lam__0(lean_object* v_a_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v_a_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_append(lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
if (lean_obj_tag(v_x_834_) == 3)
{
if (lean_obj_tag(v_x_835_) == 3)
{
lean_object* v_a_836_; lean_object* v_a_837_; uint8_t v___x_838_; 
v_a_836_ = lean_ctor_get(v_x_834_, 0);
v_a_837_ = lean_ctor_get(v_x_835_, 0);
v___x_838_ = l_Lean_Html_isEmpty(v_x_834_);
if (v___x_838_ == 0)
{
uint8_t v___x_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
lean_inc_ref(v_a_837_);
v___x_839_ = l_Lean_Html_isEmpty(v_x_835_);
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_835_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v_x_835_, 0);
lean_dec(v_unused_848_);
v___x_841_ = v_x_835_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_dec(v_x_835_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
if (v___x_839_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_845_; 
lean_inc_ref(v_a_836_);
lean_dec_ref_known(v_x_834_, 1);
v___x_843_ = l_Array_append___redArg(v_a_836_, v_a_837_);
lean_dec_ref(v_a_837_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_del_object(v___x_841_);
lean_dec_ref(v_a_837_);
return v_x_834_;
}
}
}
else
{
lean_dec_ref_known(v_x_834_, 1);
return v_x_835_;
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_860_; 
v_a_849_ = lean_ctor_get(v_x_834_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_x_834_);
if (v_isSharedCheck_860_ == 0)
{
v___x_851_ = v_x_834_;
v_isShared_852_ = v_isSharedCheck_860_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v_x_834_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_860_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_853_ = lean_array_get_size(v_a_849_);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_nat_dec_eq(v___x_853_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_array_push(v_a_849_, v_x_835_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_856_);
v___x_858_ = v___x_851_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
else
{
lean_del_object(v___x_851_);
lean_dec_ref(v_a_849_);
return v_x_835_;
}
}
}
}
else
{
if (lean_obj_tag(v_x_835_) == 3)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_875_; 
v_a_861_ = lean_ctor_get(v_x_835_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v_x_835_);
if (v_isSharedCheck_875_ == 0)
{
v___x_863_ = v_x_835_;
v_isShared_864_ = v_isSharedCheck_875_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v_x_835_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_875_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_865_ = lean_array_get_size(v_a_861_);
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = lean_nat_dec_eq(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = lean_mk_empty_array_with_capacity(v___x_868_);
v___x_870_ = lean_array_push(v___x_869_, v_x_834_);
v___x_871_ = l_Array_append___redArg(v___x_870_, v_a_861_);
lean_dec_ref(v_a_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_871_);
v___x_873_ = v___x_863_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
lean_del_object(v___x_863_);
lean_dec_ref(v_a_861_);
return v_x_834_;
}
}
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_876_ = lean_unsigned_to_nat(2u);
v___x_877_ = lean_mk_empty_array_with_capacity(v___x_876_);
v___x_878_ = lean_array_push(v___x_877_, v_x_834_);
v___x_879_ = lean_array_push(v___x_878_, v_x_835_);
v___x_880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___redArg___lam__0(lean_object* v_h_883_, lean_object* v_____s_884_){
_start:
{
lean_object* v_out_885_; lean_object* v___x_886_; 
v_out_885_ = l_Lean_Html_append(v_____s_884_, v_h_883_);
v___x_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_886_, 0, v_out_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___redArg(lean_object* v_inst_888_, lean_object* v_hs_889_){
_start:
{
lean_object* v___f_890_; lean_object* v_out_891_; lean_object* v___x_892_; 
v___f_890_ = ((lean_object*)(l_Lean_Html_ofCollection___redArg___closed__0));
v_out_891_ = ((lean_object*)(l_Lean_Html_empty));
v___x_892_ = lean_apply_4(v_inst_888_, lean_box(0), v_hs_889_, v_out_891_, v___f_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection(lean_object* v_00_u03c1_893_, lean_object* v_inst_894_, lean_object* v_hs_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Html_ofCollection___redArg(v_inst_894_, v_hs_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0(lean_object* v_as_897_, size_t v_sz_898_, size_t v_i_899_, lean_object* v_b_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_usize_dec_lt(v_i_899_, v_sz_898_);
if (v___x_901_ == 0)
{
return v_b_900_;
}
else
{
lean_object* v_a_902_; lean_object* v_out_903_; size_t v___x_904_; size_t v___x_905_; 
v_a_902_ = lean_array_uget_borrowed(v_as_897_, v_i_899_);
lean_inc(v_a_902_);
v_out_903_ = l_Lean_Html_append(v_b_900_, v_a_902_);
v___x_904_ = ((size_t)1ULL);
v___x_905_ = lean_usize_add(v_i_899_, v___x_904_);
v_i_899_ = v___x_905_;
v_b_900_ = v_out_903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0___boxed(lean_object* v_as_907_, lean_object* v_sz_908_, lean_object* v_i_909_, lean_object* v_b_910_){
_start:
{
size_t v_sz_boxed_911_; size_t v_i_boxed_912_; lean_object* v_res_913_; 
v_sz_boxed_911_ = lean_unbox_usize(v_sz_908_);
lean_dec(v_sz_908_);
v_i_boxed_912_ = lean_unbox_usize(v_i_909_);
lean_dec(v_i_909_);
v_res_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0(v_as_907_, v_sz_boxed_911_, v_i_boxed_912_, v_b_910_);
lean_dec_ref(v_as_907_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0(lean_object* v_hs_914_){
_start:
{
lean_object* v_out_915_; size_t v_sz_916_; size_t v___x_917_; lean_object* v___x_918_; 
v_out_915_ = ((lean_object*)(l_Lean_Html_empty));
v_sz_916_ = lean_array_size(v_hs_914_);
v___x_917_ = ((size_t)0ULL);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0_spec__0(v_hs_914_, v_sz_916_, v___x_917_, v_out_915_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0___boxed(lean_object* v_hs_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0(v_hs_919_);
lean_dec_ref(v_hs_919_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofArray(lean_object* v_hs_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofArray_spec__0(v_hs_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofArray___boxed(lean_object* v_hs_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Html_ofArray(v_hs_923_);
lean_dec_ref(v_hs_923_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(lean_object* v_as_x27_925_, lean_object* v_b_926_){
_start:
{
if (lean_obj_tag(v_as_x27_925_) == 0)
{
return v_b_926_;
}
else
{
lean_object* v_head_927_; lean_object* v_tail_928_; lean_object* v_out_929_; 
v_head_927_ = lean_ctor_get(v_as_x27_925_, 0);
v_tail_928_ = lean_ctor_get(v_as_x27_925_, 1);
lean_inc(v_head_927_);
v_out_929_ = l_Lean_Html_append(v_b_926_, v_head_927_);
v_as_x27_925_ = v_tail_928_;
v_b_926_ = v_out_929_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg___boxed(lean_object* v_as_x27_931_, lean_object* v_b_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(v_as_x27_931_, v_b_932_);
lean_dec(v_as_x27_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0(lean_object* v_hs_934_){
_start:
{
lean_object* v_out_935_; lean_object* v___x_936_; 
v_out_935_ = ((lean_object*)(l_Lean_Html_empty));
v___x_936_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(v_hs_934_, v_out_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0___boxed(lean_object* v_hs_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0(v_hs_937_);
lean_dec(v_hs_937_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofList(lean_object* v_hs_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0(v_hs_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofList___boxed(lean_object* v_hs_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Html_ofList(v_hs_941_);
lean_dec(v_hs_941_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0(lean_object* v_as_943_, lean_object* v_as_x27_944_, lean_object* v_b_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___redArg(v_as_x27_944_, v_b_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0___boxed(lean_object* v_as_948_, lean_object* v_as_x27_949_, lean_object* v_b_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_List_forIn_x27_loop___at___00Lean_Html_ofCollection___at___00Lean_Html_ofList_spec__0_spec__0(v_as_948_, v_as_x27_949_, v_b_950_, v_a_951_);
lean_dec(v_as_x27_949_);
lean_dec(v_as_948_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofOption(lean_object* v_h_x3f_953_){
_start:
{
if (lean_obj_tag(v_h_x3f_953_) == 0)
{
lean_object* v___x_954_; 
v___x_954_ = ((lean_object*)(l_Lean_Html_empty));
return v___x_954_;
}
else
{
lean_object* v_val_955_; 
v_val_955_ = lean_ctor_get(v_h_x3f_953_, 0);
lean_inc(v_val_955_);
return v_val_955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_ofOption___boxed(lean_object* v_h_x3f_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Html_ofOption(v_h_x3f_956_);
lean_dec(v_h_x3f_956_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0(size_t v_sz_964_, size_t v_i_965_, lean_object* v_bs_966_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = lean_usize_dec_lt(v_i_965_, v_sz_964_);
if (v___x_967_ == 0)
{
return v_bs_966_;
}
else
{
lean_object* v_v_968_; lean_object* v_fst_969_; lean_object* v_snd_970_; lean_object* v___x_971_; lean_object* v_bs_x27_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; size_t v___x_980_; size_t v___x_981_; lean_object* v___x_982_; 
v_v_968_ = lean_array_uget_borrowed(v_bs_966_, v_i_965_);
v_fst_969_ = lean_ctor_get(v_v_968_, 0);
lean_inc(v_fst_969_);
v_snd_970_ = lean_ctor_get(v_v_968_, 1);
lean_inc(v_snd_970_);
v___x_971_ = lean_unsigned_to_nat(0u);
v_bs_x27_972_ = lean_array_uset(v_bs_966_, v_i_965_, v___x_971_);
v___x_973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_973_, 0, v_fst_969_);
v___x_974_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_974_, 0, v_snd_970_);
v___x_975_ = lean_unsigned_to_nat(2u);
v___x_976_ = lean_mk_empty_array_with_capacity(v___x_975_);
v___x_977_ = lean_array_push(v___x_976_, v___x_973_);
v___x_978_ = lean_array_push(v___x_977_, v___x_974_);
v___x_979_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_add(v_i_965_, v___x_980_);
v___x_982_ = lean_array_uset(v_bs_x27_972_, v_i_965_, v___x_979_);
v_i_965_ = v___x_981_;
v_bs_966_ = v___x_982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0___boxed(lean_object* v_sz_984_, lean_object* v_i_985_, lean_object* v_bs_986_){
_start:
{
size_t v_sz_boxed_987_; size_t v_i_boxed_988_; lean_object* v_res_989_; 
v_sz_boxed_987_ = lean_unbox_usize(v_sz_984_);
lean_dec(v_sz_984_);
v_i_boxed_988_ = lean_unbox_usize(v_i_985_);
lean_dec(v_i_985_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0(v_sz_boxed_987_, v_i_boxed_988_, v_bs_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1(size_t v_sz_990_, size_t v_i_991_, lean_object* v_bs_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_lt(v_i_991_, v_sz_990_);
if (v___x_993_ == 0)
{
return v_bs_992_;
}
else
{
lean_object* v_v_994_; lean_object* v___x_995_; lean_object* v_bs_x27_996_; size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v_v_994_ = lean_array_uget(v_bs_992_, v_i_991_);
v___x_995_ = lean_unsigned_to_nat(0u);
v_bs_x27_996_ = lean_array_uset(v_bs_992_, v_i_991_, v___x_995_);
v___x_997_ = ((size_t)1ULL);
v___x_998_ = lean_usize_add(v_i_991_, v___x_997_);
v___x_999_ = lean_array_uset(v_bs_x27_996_, v_i_991_, v_v_994_);
v_i_991_ = v___x_998_;
v_bs_992_ = v___x_999_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1___boxed(lean_object* v_sz_1001_, lean_object* v_i_1002_, lean_object* v_bs_1003_){
_start:
{
size_t v_sz_boxed_1004_; size_t v_i_boxed_1005_; lean_object* v_res_1006_; 
v_sz_boxed_1004_ = lean_unbox_usize(v_sz_1001_);
lean_dec(v_sz_1001_);
v_i_boxed_1005_ = lean_unbox_usize(v_i_1002_);
lean_dec(v_i_1002_);
v_res_1006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1(v_sz_boxed_1004_, v_i_boxed_1005_, v_bs_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1(lean_object* v_a_1007_){
_start:
{
size_t v_sz_1008_; size_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_sz_1008_ = lean_array_size(v_a_1007_);
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1_spec__1(v_sz_1008_, v___x_1009_, v_a_1007_);
v___x_1011_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instToJson_to(lean_object* v_x_1016_){
_start:
{
switch(lean_obj_tag(v_x_1016_))
{
case 0:
{
lean_object* v_tag_1017_; lean_object* v_attrs_1018_; lean_object* v_children_1019_; size_t v_sz_1020_; size_t v___x_1021_; lean_object* v_attrs_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_tag_1017_ = lean_ctor_get(v_x_1016_, 0);
lean_inc_ref(v_tag_1017_);
v_attrs_1018_ = lean_ctor_get(v_x_1016_, 1);
lean_inc_ref(v_attrs_1018_);
v_children_1019_ = lean_ctor_get(v_x_1016_, 2);
lean_inc_ref(v_children_1019_);
lean_dec_ref_known(v_x_1016_, 3);
v_sz_1020_ = lean_array_size(v_attrs_1018_);
v___x_1021_ = ((size_t)0ULL);
v_attrs_1022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__0(v_sz_1020_, v___x_1021_, v_attrs_1018_);
v___x_1023_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__0));
v___x_1024_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_tag_1017_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__1));
v___x_1027_ = l_Lean_Array_toJson___at___00Lean_Html_instToJson_to_spec__1(v_attrs_1022_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__2));
v___x_1030_ = l_Lean_Html_instToJson_to(v_children_1019_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1028_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1025_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = l_Lean_Json_mkObj(v___x_1035_);
lean_dec_ref_known(v___x_1035_, 2);
return v___x_1036_;
}
case 1:
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_a_1037_ = lean_ctor_get(v_x_1016_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v_x_1016_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v_x_1016_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 3);
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
case 2:
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1057_; 
v_a_1045_ = lean_ctor_get(v_x_1016_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1047_ = v_x_1016_;
v_isShared_1048_ = v_isSharedCheck_1057_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v_x_1016_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1057_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__3));
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 3);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1045_);
v___x_1051_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1049_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_Json_mkObj(v___x_1054_);
lean_dec_ref_known(v___x_1054_, 2);
return v___x_1055_;
}
}
}
default: 
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1068_; 
v_a_1058_ = lean_ctor_get(v_x_1016_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1060_ = v_x_1016_;
v_isShared_1061_ = v_isSharedCheck_1068_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v_x_1016_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1068_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
size_t v_sz_1062_; size_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v_sz_1062_ = lean_array_size(v_a_1058_);
v___x_1063_ = ((size_t)0ULL);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2(v_sz_1062_, v___x_1063_, v_a_1058_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 4);
lean_ctor_set(v___x_1060_, 0, v___x_1064_);
v___x_1066_ = v___x_1060_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2(size_t v_sz_1069_, size_t v_i_1070_, lean_object* v_bs_1071_){
_start:
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_usize_dec_lt(v_i_1070_, v_sz_1069_);
if (v___x_1072_ == 0)
{
return v_bs_1071_;
}
else
{
lean_object* v_v_1073_; lean_object* v___x_1074_; lean_object* v_bs_x27_1075_; lean_object* v___x_1076_; size_t v___x_1077_; size_t v___x_1078_; lean_object* v___x_1079_; 
v_v_1073_ = lean_array_uget(v_bs_1071_, v_i_1070_);
v___x_1074_ = lean_unsigned_to_nat(0u);
v_bs_x27_1075_ = lean_array_uset(v_bs_1071_, v_i_1070_, v___x_1074_);
v___x_1076_ = l_Lean_Html_instToJson_to(v_v_1073_);
v___x_1077_ = ((size_t)1ULL);
v___x_1078_ = lean_usize_add(v_i_1070_, v___x_1077_);
v___x_1079_ = lean_array_uset(v_bs_x27_1075_, v_i_1070_, v___x_1076_);
v_i_1070_ = v___x_1078_;
v_bs_1071_ = v___x_1079_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2___boxed(lean_object* v_sz_1081_, lean_object* v_i_1082_, lean_object* v_bs_1083_){
_start:
{
size_t v_sz_boxed_1084_; size_t v_i_boxed_1085_; lean_object* v_res_1086_; 
v_sz_boxed_1084_ = lean_unbox_usize(v_sz_1081_);
lean_dec(v_sz_1081_);
v_i_boxed_1085_ = lean_unbox_usize(v_i_1082_);
lean_dec(v_i_1082_);
v_res_1086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instToJson_to_spec__2(v_sz_boxed_1084_, v_i_boxed_1085_, v_bs_1083_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__3_splitter___redArg(lean_object* v_x_1087_, lean_object* v_h__1_1088_, lean_object* v_h__2_1089_, lean_object* v_h__3_1090_, lean_object* v_h__4_1091_){
_start:
{
switch(lean_obj_tag(v_x_1087_))
{
case 0:
{
lean_object* v_tag_1092_; lean_object* v_attrs_1093_; lean_object* v_children_1094_; lean_object* v___x_1095_; 
lean_dec(v_h__4_1091_);
lean_dec(v_h__2_1089_);
lean_dec(v_h__1_1088_);
v_tag_1092_ = lean_ctor_get(v_x_1087_, 0);
lean_inc_ref(v_tag_1092_);
v_attrs_1093_ = lean_ctor_get(v_x_1087_, 1);
lean_inc_ref(v_attrs_1093_);
v_children_1094_ = lean_ctor_get(v_x_1087_, 2);
lean_inc_ref(v_children_1094_);
lean_dec_ref_known(v_x_1087_, 3);
v___x_1095_ = lean_apply_3(v_h__3_1090_, v_tag_1092_, v_attrs_1093_, v_children_1094_);
return v___x_1095_;
}
case 1:
{
lean_object* v_a_1096_; lean_object* v___x_1097_; 
lean_dec(v_h__4_1091_);
lean_dec(v_h__3_1090_);
lean_dec(v_h__2_1089_);
v_a_1096_ = lean_ctor_get(v_x_1087_, 0);
lean_inc_ref(v_a_1096_);
lean_dec_ref_known(v_x_1087_, 1);
v___x_1097_ = lean_apply_1(v_h__1_1088_, v_a_1096_);
return v___x_1097_;
}
case 2:
{
lean_object* v_a_1098_; lean_object* v___x_1099_; 
lean_dec(v_h__4_1091_);
lean_dec(v_h__3_1090_);
lean_dec(v_h__1_1088_);
v_a_1098_ = lean_ctor_get(v_x_1087_, 0);
lean_inc_ref(v_a_1098_);
lean_dec_ref_known(v_x_1087_, 1);
v___x_1099_ = lean_apply_1(v_h__2_1089_, v_a_1098_);
return v___x_1099_;
}
default: 
{
lean_object* v_a_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__3_1090_);
lean_dec(v_h__2_1089_);
lean_dec(v_h__1_1088_);
v_a_1100_ = lean_ctor_get(v_x_1087_, 0);
lean_inc_ref(v_a_1100_);
lean_dec_ref_known(v_x_1087_, 1);
v___x_1101_ = lean_apply_1(v_h__4_1091_, v_a_1100_);
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__3_splitter(lean_object* v_motive_1102_, lean_object* v_x_1103_, lean_object* v_h__1_1104_, lean_object* v_h__2_1105_, lean_object* v_h__3_1106_, lean_object* v_h__4_1107_){
_start:
{
switch(lean_obj_tag(v_x_1103_))
{
case 0:
{
lean_object* v_tag_1108_; lean_object* v_attrs_1109_; lean_object* v_children_1110_; lean_object* v___x_1111_; 
lean_dec(v_h__4_1107_);
lean_dec(v_h__2_1105_);
lean_dec(v_h__1_1104_);
v_tag_1108_ = lean_ctor_get(v_x_1103_, 0);
lean_inc_ref(v_tag_1108_);
v_attrs_1109_ = lean_ctor_get(v_x_1103_, 1);
lean_inc_ref(v_attrs_1109_);
v_children_1110_ = lean_ctor_get(v_x_1103_, 2);
lean_inc_ref(v_children_1110_);
lean_dec_ref_known(v_x_1103_, 3);
v___x_1111_ = lean_apply_3(v_h__3_1106_, v_tag_1108_, v_attrs_1109_, v_children_1110_);
return v___x_1111_;
}
case 1:
{
lean_object* v_a_1112_; lean_object* v___x_1113_; 
lean_dec(v_h__4_1107_);
lean_dec(v_h__3_1106_);
lean_dec(v_h__2_1105_);
v_a_1112_ = lean_ctor_get(v_x_1103_, 0);
lean_inc_ref(v_a_1112_);
lean_dec_ref_known(v_x_1103_, 1);
v___x_1113_ = lean_apply_1(v_h__1_1104_, v_a_1112_);
return v___x_1113_;
}
case 2:
{
lean_object* v_a_1114_; lean_object* v___x_1115_; 
lean_dec(v_h__4_1107_);
lean_dec(v_h__3_1106_);
lean_dec(v_h__1_1104_);
v_a_1114_ = lean_ctor_get(v_x_1103_, 0);
lean_inc_ref(v_a_1114_);
lean_dec_ref_known(v_x_1103_, 1);
v___x_1115_ = lean_apply_1(v_h__2_1105_, v_a_1114_);
return v___x_1115_;
}
default: 
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
lean_dec(v_h__3_1106_);
lean_dec(v_h__2_1105_);
lean_dec(v_h__1_1104_);
v_a_1116_ = lean_ctor_get(v_x_1103_, 0);
lean_inc_ref(v_a_1116_);
lean_dec_ref_known(v_x_1103_, 1);
v___x_1117_ = lean_apply_1(v_h__4_1107_, v_a_1116_);
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_1118_, lean_object* v_h__1_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_apply_2(v_h__1_1119_, v_x_1118_, lean_box(0));
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_1121_, lean_object* v_P_1122_, lean_object* v_motive_1123_, lean_object* v_x_1124_, lean_object* v_h__1_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_apply_2(v_h__1_1125_, v_x_1124_, lean_box(0));
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__1_splitter___redArg(lean_object* v_x_1127_, lean_object* v_h__1_1128_){
_start:
{
lean_object* v_fst_1129_; lean_object* v_snd_1130_; lean_object* v___x_1131_; 
v_fst_1129_ = lean_ctor_get(v_x_1127_, 0);
lean_inc(v_fst_1129_);
v_snd_1130_ = lean_ctor_get(v_x_1127_, 1);
lean_inc(v_snd_1130_);
lean_dec_ref(v_x_1127_);
v___x_1131_ = lean_apply_2(v_h__1_1128_, v_fst_1129_, v_snd_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Basic_0__Lean_Html_instToJson_match__1_splitter(lean_object* v_motive_1132_, lean_object* v_x_1133_, lean_object* v_h__1_1134_){
_start:
{
lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1137_; 
v_fst_1135_ = lean_ctor_get(v_x_1133_, 0);
lean_inc(v_fst_1135_);
v_snd_1136_ = lean_ctor_get(v_x_1133_, 1);
lean_inc(v_snd_1136_);
lean_dec_ref(v_x_1133_);
v___x_1137_ = lean_apply_2(v_h__1_1134_, v_fst_1135_, v_snd_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(lean_object* v_t_1140_, lean_object* v_k_1141_){
_start:
{
if (lean_obj_tag(v_t_1140_) == 0)
{
lean_object* v_k_1142_; lean_object* v_v_1143_; lean_object* v_l_1144_; lean_object* v_r_1145_; uint8_t v___x_1146_; 
v_k_1142_ = lean_ctor_get(v_t_1140_, 1);
v_v_1143_ = lean_ctor_get(v_t_1140_, 2);
v_l_1144_ = lean_ctor_get(v_t_1140_, 3);
v_r_1145_ = lean_ctor_get(v_t_1140_, 4);
v___x_1146_ = lean_string_compare(v_k_1141_, v_k_1142_);
switch(v___x_1146_)
{
case 0:
{
v_t_1140_ = v_l_1144_;
goto _start;
}
case 1:
{
lean_object* v___x_1148_; 
lean_inc(v_v_1143_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_v_1143_);
return v___x_1148_;
}
default: 
{
v_t_1140_ = v_r_1145_;
goto _start;
}
}
}
else
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_box(0);
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg___boxed(lean_object* v_t_1151_, lean_object* v_k_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_t_1151_, v_k_1152_);
lean_dec_ref(v_k_1152_);
lean_dec(v_t_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3(size_t v_sz_1154_, size_t v_i_1155_, lean_object* v_bs_1156_){
_start:
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_usize_dec_lt(v_i_1155_, v_sz_1154_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_bs_1156_);
return v___x_1158_;
}
else
{
lean_object* v_v_1159_; lean_object* v___x_1160_; lean_object* v_bs_x27_1161_; size_t v___x_1162_; size_t v___x_1163_; lean_object* v___x_1164_; 
v_v_1159_ = lean_array_uget(v_bs_1156_, v_i_1155_);
v___x_1160_ = lean_unsigned_to_nat(0u);
v_bs_x27_1161_ = lean_array_uset(v_bs_1156_, v_i_1155_, v___x_1160_);
v___x_1162_ = ((size_t)1ULL);
v___x_1163_ = lean_usize_add(v_i_1155_, v___x_1162_);
v___x_1164_ = lean_array_uset(v_bs_x27_1161_, v_i_1155_, v_v_1159_);
v_i_1155_ = v___x_1163_;
v_bs_1156_ = v___x_1164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1166_, lean_object* v_i_1167_, lean_object* v_bs_1168_){
_start:
{
size_t v_sz_boxed_1169_; size_t v_i_boxed_1170_; lean_object* v_res_1171_; 
v_sz_boxed_1169_ = lean_unbox_usize(v_sz_1166_);
lean_dec(v_sz_1166_);
v_i_boxed_1170_ = lean_unbox_usize(v_i_1167_);
lean_dec(v_i_1167_);
v_res_1171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3(v_sz_boxed_1169_, v_i_boxed_1170_, v_bs_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2(lean_object* v_x_1174_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 4)
{
lean_object* v_elems_1175_; size_t v_sz_1176_; size_t v___x_1177_; lean_object* v___x_1178_; 
v_elems_1175_ = lean_ctor_get(v_x_1174_, 0);
lean_inc_ref(v_elems_1175_);
lean_dec_ref_known(v_x_1174_, 1);
v_sz_1176_ = lean_array_size(v_elems_1175_);
v___x_1177_ = ((size_t)0ULL);
v___x_1178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2_spec__3(v_sz_1176_, v___x_1177_, v_elems_1175_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1179_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__0));
v___x_1180_ = lean_unsigned_to_nat(80u);
v___x_1181_ = l_Lean_Json_pretty(v_x_1174_, v___x_1180_);
v___x_1182_ = lean_string_append(v___x_1179_, v___x_1181_);
lean_dec_ref(v___x_1181_);
v___x_1183_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2___closed__1));
v___x_1184_ = lean_string_append(v___x_1182_, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2(lean_object* v_j_1186_, lean_object* v_k_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = l_Lean_Json_getObjValD(v_j_1186_, v_k_1187_);
v___x_1189_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2_spec__2(v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2___boxed(lean_object* v_j_1190_, lean_object* v_k_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2(v_j_1190_, v_k_1191_);
lean_dec_ref(v_k_1191_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3(size_t v_sz_1194_, size_t v_i_1195_, lean_object* v_bs_1196_){
_start:
{
uint8_t v___x_1197_; 
v___x_1197_ = lean_usize_dec_lt(v_i_1195_, v_sz_1194_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_bs_1196_);
return v___x_1198_;
}
else
{
lean_object* v_v_1199_; 
v_v_1199_ = lean_array_uget_borrowed(v_bs_1196_, v_i_1195_);
if (lean_obj_tag(v_v_1199_) == 4)
{
lean_object* v_elems_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_elems_1205_ = lean_ctor_get(v_v_1199_, 0);
v___x_1206_ = lean_array_get_size(v_elems_1205_);
v___x_1207_ = lean_unsigned_to_nat(2u);
v___x_1208_ = lean_nat_dec_eq(v___x_1206_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_inc_ref(v_v_1199_);
lean_dec_ref(v_bs_1196_);
goto v___jp_1200_;
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_array_fget_borrowed(v_elems_1205_, v___x_1209_);
if (lean_obj_tag(v___x_1210_) == 3)
{
lean_object* v_s_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_s_1211_ = lean_ctor_get(v___x_1210_, 0);
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_array_fget_borrowed(v_elems_1205_, v___x_1212_);
if (lean_obj_tag(v___x_1213_) == 3)
{
lean_object* v_s_1214_; lean_object* v_bs_x27_1215_; lean_object* v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; 
lean_inc_ref(v_s_1211_);
v_s_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc_ref(v_s_1214_);
v_bs_x27_1215_ = lean_array_uset(v_bs_1196_, v_i_1195_, v___x_1209_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_s_1211_);
lean_ctor_set(v___x_1216_, 1, v_s_1214_);
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1195_, v___x_1217_);
v___x_1219_ = lean_array_uset(v_bs_x27_1215_, v_i_1195_, v___x_1216_);
v_i_1195_ = v___x_1218_;
v_bs_1196_ = v___x_1219_;
goto _start;
}
else
{
lean_inc_ref(v_v_1199_);
lean_dec_ref(v_bs_1196_);
goto v___jp_1200_;
}
}
else
{
lean_inc_ref(v_v_1199_);
lean_dec_ref(v_bs_1196_);
goto v___jp_1200_;
}
}
}
else
{
lean_inc(v_v_1199_);
lean_dec_ref(v_bs_1196_);
goto v___jp_1200_;
}
v___jp_1200_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3___closed__0));
v___x_1202_ = l_Lean_Json_compress(v_v_1199_);
v___x_1203_ = lean_string_append(v___x_1201_, v___x_1202_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3___boxed(lean_object* v_sz_1221_, lean_object* v_i_1222_, lean_object* v_bs_1223_){
_start:
{
size_t v_sz_boxed_1224_; size_t v_i_boxed_1225_; lean_object* v_res_1226_; 
v_sz_boxed_1224_ = lean_unbox_usize(v_sz_1221_);
lean_dec(v_sz_1221_);
v_i_boxed_1225_ = lean_unbox_usize(v_i_1222_);
lean_dec(v_i_1222_);
v_res_1226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3(v_sz_boxed_1224_, v_i_boxed_1225_, v_bs_1223_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instFromJson_from_x3f(lean_object* v_x_1230_){
_start:
{
switch(lean_obj_tag(v_x_1230_))
{
case 3:
{
lean_object* v_s_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1239_; 
v_s_1231_ = lean_ctor_get(v_x_1230_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_x_1230_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1233_ = v_x_1230_;
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_s_1231_);
lean_dec(v_x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set_tag(v___x_1233_, 1);
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_s_1231_);
v___x_1236_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
}
}
case 4:
{
lean_object* v_elems_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1266_; 
v_elems_1240_ = lean_ctor_get(v_x_1230_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_x_1230_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1242_ = v_x_1230_;
v_isShared_1243_ = v_isSharedCheck_1266_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_elems_1240_);
lean_dec(v_x_1230_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1266_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
size_t v_sz_1244_; size_t v___x_1245_; lean_object* v___x_1246_; 
v_sz_1244_ = lean_array_size(v_elems_1240_);
v___x_1245_ = ((size_t)0ULL);
v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0(v_sz_1244_, v___x_1245_, v_elems_1240_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_del_object(v___x_1242_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1265_; 
v_a_1255_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1257_ = v___x_1246_;
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1246_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set_tag(v___x_1242_, 3);
lean_ctor_set(v___x_1242_, 0, v_a_1255_);
v___x_1260_ = v___x_1242_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1262_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1260_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
case 5:
{
lean_object* v_kvPairs_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_kvPairs_1267_ = lean_ctor_get(v_x_1230_, 0);
v___x_1268_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__0));
v___x_1269_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_kvPairs_1267_, v___x_1268_);
if (lean_obj_tag(v___x_1269_) == 1)
{
lean_object* v_val_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1325_; 
v_val_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1325_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_val_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1325_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
if (lean_obj_tag(v_val_1270_) == 3)
{
lean_object* v_s_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_del_object(v___x_1272_);
v_s_1274_ = lean_ctor_get(v_val_1270_, 0);
lean_inc_ref(v_s_1274_);
lean_dec_ref_known(v_val_1270_, 1);
v___x_1275_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__1));
lean_inc_ref(v_x_1230_);
v___x_1276_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__2(v_x_1230_, v___x_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_s_1274_);
lean_dec_ref_known(v_x_1230_, 1);
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1285_; size_t v_sz_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v_a_1285_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1276_, 1);
v_sz_1286_ = lean_array_size(v_a_1285_);
v___x_1287_ = ((size_t)0ULL);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__3(v_sz_1286_, v___x_1287_, v_a_1285_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v_s_1274_);
lean_dec_ref_known(v_x_1230_, 1);
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_a_1297_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1288_, 1);
v___x_1298_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__2));
v___x_1299_ = l_Lean_Json_getObjVal_x3f(v_x_1230_, v___x_1298_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_a_1297_);
lean_dec_ref(v_s_1274_);
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1299_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1309_; 
v_a_1308_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1309_ = l_Lean_Html_instFromJson_from_x3f(v_a_1308_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_dec(v_a_1297_);
lean_dec_ref(v_s_1274_);
return v___x_1309_;
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1318_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1314_, 0, v_s_1274_);
lean_ctor_set(v___x_1314_, 1, v_a_1297_);
lean_ctor_set(v___x_1314_, 2, v_a_1310_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
lean_dec_ref_known(v_x_1230_, 1);
v___x_1319_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__0));
v___x_1320_ = l_Lean_Json_compress(v_val_1270_);
v___x_1321_ = lean_string_append(v___x_1319_, v___x_1320_);
lean_dec_ref(v___x_1320_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1321_);
v___x_1323_ = v___x_1272_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec(v___x_1269_);
v___x_1326_ = ((lean_object*)(l_Lean_Html_instToJson_to___closed__3));
v___x_1327_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_kvPairs_1267_, v___x_1326_);
if (lean_obj_tag(v___x_1327_) == 1)
{
lean_object* v_val_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref_known(v_x_1230_, 1);
v_val_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1349_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_val_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1349_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
if (lean_obj_tag(v_val_1328_) == 3)
{
lean_object* v_s_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1342_; 
v_s_1332_ = lean_ctor_get(v_val_1328_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_val_1328_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1334_ = v_val_1328_;
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_s_1332_);
lean_dec(v_val_1328_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set_tag(v___x_1334_, 2);
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_s_1332_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1339_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1337_);
v___x_1339_ = v___x_1330_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1343_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__0));
v___x_1344_ = l_Lean_Json_compress(v_val_1328_);
v___x_1345_ = lean_string_append(v___x_1343_, v___x_1344_);
lean_dec_ref(v___x_1344_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1345_);
v___x_1347_ = v___x_1330_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec(v___x_1327_);
v___x_1350_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__1));
v___x_1351_ = l_Lean_Json_compress(v_x_1230_);
v___x_1352_ = lean_string_append(v___x_1350_, v___x_1351_);
lean_dec_ref(v___x_1351_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
}
}
default: 
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1354_ = ((lean_object*)(l_Lean_Html_instFromJson_from_x3f___closed__2));
v___x_1355_ = l_Lean_Json_compress(v_x_1230_);
v___x_1356_ = lean_string_append(v___x_1354_, v___x_1355_);
lean_dec_ref(v___x_1355_);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0(size_t v_sz_1358_, size_t v_i_1359_, lean_object* v_bs_1360_){
_start:
{
uint8_t v___x_1361_; 
v___x_1361_ = lean_usize_dec_lt(v_i_1359_, v_sz_1358_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_bs_1360_);
return v___x_1362_;
}
else
{
lean_object* v_v_1363_; lean_object* v___x_1364_; 
v_v_1363_ = lean_array_uget_borrowed(v_bs_1360_, v_i_1359_);
lean_inc(v_v_1363_);
v___x_1364_ = l_Lean_Html_instFromJson_from_x3f(v_v_1363_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v_bs_1360_);
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1374_; lean_object* v_bs_x27_1375_; size_t v___x_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
v_a_1373_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1374_ = lean_unsigned_to_nat(0u);
v_bs_x27_1375_ = lean_array_uset(v_bs_1360_, v_i_1359_, v___x_1374_);
v___x_1376_ = ((size_t)1ULL);
v___x_1377_ = lean_usize_add(v_i_1359_, v___x_1376_);
v___x_1378_ = lean_array_uset(v_bs_x27_1375_, v_i_1359_, v_a_1373_);
v_i_1359_ = v___x_1377_;
v_bs_1360_ = v___x_1378_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0___boxed(lean_object* v_sz_1380_, lean_object* v_i_1381_, lean_object* v_bs_1382_){
_start:
{
size_t v_sz_boxed_1383_; size_t v_i_boxed_1384_; lean_object* v_res_1385_; 
v_sz_boxed_1383_ = lean_unbox_usize(v_sz_1380_);
lean_dec(v_sz_1380_);
v_i_boxed_1384_ = lean_unbox_usize(v_i_1381_);
lean_dec(v_i_1381_);
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_instFromJson_from_x3f_spec__0(v_sz_boxed_1383_, v_i_boxed_1384_, v_bs_1382_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1(lean_object* v_00_u03b4_1386_, lean_object* v_t_1387_, lean_object* v_k_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___redArg(v_t_1387_, v_k_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1___boxed(lean_object* v_00_u03b4_1390_, lean_object* v_t_1391_, lean_object* v_k_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Html_instFromJson_from_x3f_spec__1(v_00_u03b4_1390_, v_t_1391_, v_k_1392_);
lean_dec_ref(v_k_1392_);
lean_dec(v_t_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instFromJson___lam__0(lean_object* v_j_1396_){
_start:
{
lean_object* v___x_1397_; 
lean_inc(v_j_1396_);
v___x_1397_ = l_Lean_Html_instFromJson_from_x3f(v_j_1396_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1411_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1411_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1411_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1402_ = ((lean_object*)(l_Lean_Html_instFromJson___lam__0___closed__0));
v___x_1403_ = l_Lean_Json_compress(v_j_1396_);
v___x_1404_ = lean_string_append(v___x_1402_, v___x_1403_);
lean_dec_ref(v___x_1403_);
v___x_1405_ = ((lean_object*)(l_Lean_Html_instFromJson___lam__0___closed__1));
v___x_1406_ = lean_string_append(v___x_1404_, v___x_1405_);
v___x_1407_ = lean_string_append(v___x_1406_, v_a_1398_);
lean_dec(v_a_1398_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1407_);
v___x_1409_ = v___x_1400_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
else
{
lean_dec(v_j_1396_);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1(lean_object* v_xs_1416_, lean_object* v_i_1417_, lean_object* v_args_1418_){
_start:
{
lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = lean_array_get_size(v_xs_1416_);
v___x_1420_ = lean_nat_dec_lt(v_i_1417_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec(v_i_1417_);
v___x_1421_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__0));
v___x_1422_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__1));
v___x_1423_ = l_Nat_reprFast(v___x_1419_);
v___x_1424_ = lean_string_append(v___x_1422_, v___x_1423_);
lean_dec_ref(v___x_1423_);
v___x_1425_ = l_Lean_Name_mkStr2(v___x_1421_, v___x_1424_);
v___x_1426_ = l_Lean_Syntax_mkCApp(v___x_1425_, v_args_1418_);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; lean_object* v_fst_1428_; lean_object* v_snd_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1427_ = lean_array_fget_borrowed(v_xs_1416_, v_i_1417_);
v_fst_1428_ = lean_ctor_get(v___x_1427_, 0);
v_snd_1429_ = lean_ctor_get(v___x_1427_, 1);
v___x_1430_ = lean_unsigned_to_nat(1u);
v___x_1431_ = lean_nat_add(v_i_1417_, v___x_1430_);
lean_dec(v_i_1417_);
v___x_1432_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__5));
v___x_1433_ = lean_box(2);
lean_inc(v_fst_1428_);
v___x_1434_ = l_Lean_Syntax_mkStrLit(v_fst_1428_, v___x_1433_);
lean_inc(v_snd_1429_);
v___x_1435_ = l_Lean_Syntax_mkStrLit(v_snd_1429_, v___x_1433_);
v___x_1436_ = lean_unsigned_to_nat(2u);
v___x_1437_ = lean_mk_empty_array_with_capacity(v___x_1436_);
v___x_1438_ = lean_array_push(v___x_1437_, v___x_1434_);
v___x_1439_ = lean_array_push(v___x_1438_, v___x_1435_);
v___x_1440_ = l_Lean_Syntax_mkCApp(v___x_1432_, v___x_1439_);
v___x_1441_ = lean_array_push(v_args_1418_, v___x_1440_);
v_i_1417_ = v___x_1431_;
v_args_1418_ = v___x_1441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___boxed(lean_object* v_xs_1443_, lean_object* v_i_1444_, lean_object* v_args_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1(v_xs_1443_, v_i_1444_, v_args_1445_);
lean_dec_ref(v_xs_1443_);
return v_res_1446_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__11));
v___x_1448_ = l_Lean_mkCIdent(v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0(lean_object* v_x_1449_){
_start:
{
if (lean_obj_tag(v_x_1449_) == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0, &l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0);
return v___x_1450_;
}
else
{
lean_object* v_head_1451_; lean_object* v_tail_1452_; lean_object* v_fst_1453_; lean_object* v_snd_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_head_1451_ = lean_ctor_get(v_x_1449_, 0);
lean_inc(v_head_1451_);
v_tail_1452_ = lean_ctor_get(v_x_1449_, 1);
lean_inc(v_tail_1452_);
lean_dec_ref_known(v_x_1449_, 2);
v_fst_1453_ = lean_ctor_get(v_head_1451_, 0);
lean_inc(v_fst_1453_);
v_snd_1454_ = lean_ctor_get(v_head_1451_, 1);
lean_inc(v_snd_1454_);
lean_dec(v_head_1451_);
v___x_1455_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__15));
v___x_1456_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_instToExprHtml_toExpr_spec__0___closed__5));
v___x_1457_ = lean_box(2);
v___x_1458_ = l_Lean_Syntax_mkStrLit(v_fst_1453_, v___x_1457_);
v___x_1459_ = l_Lean_Syntax_mkStrLit(v_snd_1454_, v___x_1457_);
v___x_1460_ = lean_unsigned_to_nat(2u);
v___x_1461_ = lean_mk_empty_array_with_capacity(v___x_1460_);
lean_inc_ref(v___x_1461_);
v___x_1462_ = lean_array_push(v___x_1461_, v___x_1458_);
v___x_1463_ = lean_array_push(v___x_1462_, v___x_1459_);
v___x_1464_ = l_Lean_Syntax_mkCApp(v___x_1456_, v___x_1463_);
v___x_1465_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0(v_tail_1452_);
v___x_1466_ = lean_array_push(v___x_1461_, v___x_1464_);
v___x_1467_ = lean_array_push(v___x_1466_, v___x_1465_);
v___x_1468_ = l_Lean_Syntax_mkCApp(v___x_1455_, v___x_1467_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0(lean_object* v_xs_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = lean_array_get_size(v_xs_1471_);
v___x_1473_ = lean_unsigned_to_nat(8u);
v___x_1474_ = lean_nat_dec_le(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1475_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__8));
v___x_1476_ = lean_array_to_list(v_xs_1471_);
v___x_1477_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0(v___x_1476_);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_mk_empty_array_with_capacity(v___x_1478_);
v___x_1480_ = lean_array_push(v___x_1479_, v___x_1477_);
v___x_1481_ = l_Lean_Syntax_mkCApp(v___x_1475_, v___x_1480_);
return v___x_1481_;
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_unsigned_to_nat(0u);
v___x_1483_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__0));
v___x_1484_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1(v_xs_1471_, v___x_1482_, v___x_1483_);
lean_dec_ref(v_xs_1471_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__3(lean_object* v_x_1485_){
_start:
{
if (lean_obj_tag(v_x_1485_) == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0, &l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__0___closed__0);
return v___x_1486_;
}
else
{
lean_object* v_head_1487_; lean_object* v_tail_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_head_1487_ = lean_ctor_get(v_x_1485_, 0);
lean_inc(v_head_1487_);
v_tail_1488_ = lean_ctor_get(v_x_1485_, 1);
lean_inc(v_tail_1488_);
lean_dec_ref_known(v_x_1485_, 2);
v___x_1489_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__15));
v___x_1490_ = l_Lean_Html_instQuoteMkStr1_q(v_head_1487_);
v___x_1491_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__3(v_tail_1488_);
v___x_1492_ = lean_unsigned_to_nat(2u);
v___x_1493_ = lean_mk_empty_array_with_capacity(v___x_1492_);
v___x_1494_ = lean_array_push(v___x_1493_, v___x_1490_);
v___x_1495_ = lean_array_push(v___x_1494_, v___x_1491_);
v___x_1496_ = l_Lean_Syntax_mkCApp(v___x_1489_, v___x_1495_);
return v___x_1496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1(lean_object* v_xs_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1498_ = lean_array_get_size(v_xs_1497_);
v___x_1499_ = lean_unsigned_to_nat(8u);
v___x_1500_ = lean_nat_dec_le(v___x_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1501_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__8));
v___x_1502_ = lean_array_to_list(v_xs_1497_);
v___x_1503_ = l___private_Init_Meta_Defs_0__Lean_quoteList___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__3(v___x_1502_);
v___x_1504_ = lean_unsigned_to_nat(1u);
v___x_1505_ = lean_mk_empty_array_with_capacity(v___x_1504_);
v___x_1506_ = lean_array_push(v___x_1505_, v___x_1503_);
v___x_1507_ = l_Lean_Syntax_mkCApp(v___x_1501_, v___x_1506_);
return v___x_1507_;
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0___closed__0));
v___x_1510_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4(v_xs_1497_, v___x_1508_, v___x_1509_);
lean_dec_ref(v_xs_1497_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_instQuoteMkStr1_q(lean_object* v_x_1511_){
_start:
{
switch(lean_obj_tag(v_x_1511_))
{
case 0:
{
lean_object* v_tag_1512_; lean_object* v_attrs_1513_; lean_object* v_children_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_tag_1512_ = lean_ctor_get(v_x_1511_, 0);
lean_inc_ref(v_tag_1512_);
v_attrs_1513_ = lean_ctor_get(v_x_1511_, 1);
lean_inc_ref(v_attrs_1513_);
v_children_1514_ = lean_ctor_get(v_x_1511_, 2);
lean_inc_ref(v_children_1514_);
lean_dec_ref_known(v_x_1511_, 3);
v___x_1515_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__1));
v___x_1516_ = lean_box(2);
v___x_1517_ = l_Lean_Syntax_mkStrLit(v_tag_1512_, v___x_1516_);
v___x_1518_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0(v_attrs_1513_);
v___x_1519_ = l_Lean_Html_instQuoteMkStr1_q(v_children_1514_);
v___x_1520_ = lean_unsigned_to_nat(3u);
v___x_1521_ = lean_mk_empty_array_with_capacity(v___x_1520_);
v___x_1522_ = lean_array_push(v___x_1521_, v___x_1517_);
v___x_1523_ = lean_array_push(v___x_1522_, v___x_1518_);
v___x_1524_ = lean_array_push(v___x_1523_, v___x_1519_);
v___x_1525_ = l_Lean_Syntax_mkCApp(v___x_1515_, v___x_1524_);
return v___x_1525_;
}
case 1:
{
lean_object* v_a_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_a_1526_ = lean_ctor_get(v_x_1511_, 0);
lean_inc_ref(v_a_1526_);
lean_dec_ref_known(v_x_1511_, 1);
v___x_1527_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__19));
v___x_1528_ = lean_box(2);
v___x_1529_ = l_Lean_Syntax_mkStrLit(v_a_1526_, v___x_1528_);
v___x_1530_ = lean_unsigned_to_nat(1u);
v___x_1531_ = lean_mk_empty_array_with_capacity(v___x_1530_);
v___x_1532_ = lean_array_push(v___x_1531_, v___x_1529_);
v___x_1533_ = l_Lean_Syntax_mkCApp(v___x_1527_, v___x_1532_);
return v___x_1533_;
}
case 2:
{
lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_a_1534_ = lean_ctor_get(v_x_1511_, 0);
lean_inc_ref(v_a_1534_);
lean_dec_ref_known(v_x_1511_, 1);
v___x_1535_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__22));
v___x_1536_ = lean_box(2);
v___x_1537_ = l_Lean_Syntax_mkStrLit(v_a_1534_, v___x_1536_);
v___x_1538_ = lean_unsigned_to_nat(1u);
v___x_1539_ = lean_mk_empty_array_with_capacity(v___x_1538_);
v___x_1540_ = lean_array_push(v___x_1539_, v___x_1537_);
v___x_1541_ = l_Lean_Syntax_mkCApp(v___x_1535_, v___x_1540_);
return v___x_1541_;
}
default: 
{
lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_a_1542_ = lean_ctor_get(v_x_1511_, 0);
lean_inc_ref(v_a_1542_);
lean_dec_ref_known(v_x_1511_, 1);
v___x_1543_ = ((lean_object*)(l_Lean_instToExprHtml_toExpr___closed__26));
v___x_1544_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1(v_a_1542_);
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = lean_mk_empty_array_with_capacity(v___x_1545_);
v___x_1547_ = lean_array_push(v___x_1546_, v___x_1544_);
v___x_1548_ = l_Lean_Syntax_mkCApp(v___x_1543_, v___x_1547_);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4(lean_object* v_xs_1549_, lean_object* v_i_1550_, lean_object* v_args_1551_){
_start:
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = lean_array_get_size(v_xs_1549_);
v___x_1553_ = lean_nat_dec_lt(v_i_1550_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec(v_i_1550_);
v___x_1554_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__0));
v___x_1555_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__0_spec__1___closed__1));
v___x_1556_ = l_Nat_reprFast(v___x_1552_);
v___x_1557_ = lean_string_append(v___x_1555_, v___x_1556_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = l_Lean_Name_mkStr2(v___x_1554_, v___x_1557_);
v___x_1559_ = l_Lean_Syntax_mkCApp(v___x_1558_, v_args_1551_);
return v___x_1559_;
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = lean_nat_add(v_i_1550_, v___x_1560_);
v___x_1562_ = lean_array_fget_borrowed(v_xs_1549_, v_i_1550_);
lean_dec(v_i_1550_);
lean_inc(v___x_1562_);
v___x_1563_ = l_Lean_Html_instQuoteMkStr1_q(v___x_1562_);
v___x_1564_ = lean_array_push(v_args_1551_, v___x_1563_);
v_i_1550_ = v___x_1561_;
v_args_1551_ = v___x_1564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4___boxed(lean_object* v_xs_1566_, lean_object* v_i_1567_, lean_object* v_args_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___at___00__private_Init_Meta_Defs_0__Lean_quoteArray___at___00Lean_Html_instQuoteMkStr1_q_spec__1_spec__4(v_xs_1566_, v_i_1567_, v_args_1568_);
lean_dec_ref(v_xs_1566_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg___lam__0(lean_object* v_tag_1572_, lean_object* v_attrs_1573_, lean_object* v_fn_1574_, lean_object* v_children_x27_1575_){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1576_, 0, v_tag_1572_);
lean_ctor_set(v___x_1576_, 1, v_attrs_1573_);
lean_ctor_set(v___x_1576_, 2, v_children_x27_1575_);
v___x_1577_ = lean_apply_1(v_fn_1574_, v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg___lam__1(lean_object* v_fn_1578_, lean_object* v_s_x27_1579_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_s_x27_1579_);
v___x_1581_ = lean_apply_1(v_fn_1578_, v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___redArg(lean_object* v_inst_1582_, lean_object* v_fn_1583_, lean_object* v_x_1584_){
_start:
{
switch(lean_obj_tag(v_x_1584_))
{
case 0:
{
lean_object* v_toBind_1585_; lean_object* v_tag_1586_; lean_object* v_attrs_1587_; lean_object* v_children_1588_; lean_object* v___f_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_toBind_1585_ = lean_ctor_get(v_inst_1582_, 1);
lean_inc(v_toBind_1585_);
v_tag_1586_ = lean_ctor_get(v_x_1584_, 0);
lean_inc_ref(v_tag_1586_);
v_attrs_1587_ = lean_ctor_get(v_x_1584_, 1);
lean_inc_ref(v_attrs_1587_);
v_children_1588_ = lean_ctor_get(v_x_1584_, 2);
lean_inc_ref(v_children_1588_);
lean_dec_ref_known(v_x_1584_, 3);
lean_inc(v_fn_1583_);
v___f_1589_ = lean_alloc_closure((void*)(l_Lean_Html_rewritePostM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1589_, 0, v_tag_1586_);
lean_closure_set(v___f_1589_, 1, v_attrs_1587_);
lean_closure_set(v___f_1589_, 2, v_fn_1583_);
v___x_1590_ = l_Lean_Html_rewritePostM___redArg(v_inst_1582_, v_fn_1583_, v_children_1588_);
v___x_1591_ = lean_apply_4(v_toBind_1585_, lean_box(0), lean_box(0), v___x_1590_, v___f_1589_);
return v___x_1591_;
}
case 3:
{
lean_object* v_toBind_1592_; lean_object* v_a_1593_; lean_object* v___f_1594_; lean_object* v___x_1595_; size_t v_sz_1596_; size_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_toBind_1592_ = lean_ctor_get(v_inst_1582_, 1);
lean_inc(v_toBind_1592_);
v_a_1593_ = lean_ctor_get(v_x_1584_, 0);
lean_inc_ref(v_a_1593_);
lean_dec_ref_known(v_x_1584_, 1);
lean_inc(v_fn_1583_);
v___f_1594_ = lean_alloc_closure((void*)(l_Lean_Html_rewritePostM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1594_, 0, v_fn_1583_);
lean_inc_ref(v_inst_1582_);
v___x_1595_ = lean_alloc_closure((void*)(l_Lean_Html_rewritePostM___redArg), 3, 2);
lean_closure_set(v___x_1595_, 0, v_inst_1582_);
lean_closure_set(v___x_1595_, 1, v_fn_1583_);
v_sz_1596_ = lean_array_size(v_a_1593_);
v___x_1597_ = ((size_t)0ULL);
v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1582_, v___x_1595_, v_sz_1596_, v___x_1597_, v_a_1593_);
v___x_1599_ = lean_apply_4(v_toBind_1592_, lean_box(0), lean_box(0), v___x_1598_, v___f_1594_);
return v___x_1599_;
}
default: 
{
lean_object* v___x_1600_; 
lean_dec_ref(v_inst_1582_);
v___x_1600_ = lean_apply_1(v_fn_1583_, v_x_1584_);
return v___x_1600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM(lean_object* v_m_1601_, lean_object* v_inst_1602_, lean_object* v_fn_1603_, lean_object* v_x_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_Html_rewritePostM___redArg(v_inst_1602_, v_fn_1603_, v_x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(lean_object* v_fn_1606_, lean_object* v_x_1607_){
_start:
{
switch(lean_obj_tag(v_x_1607_))
{
case 0:
{
lean_object* v_tag_1608_; lean_object* v_attrs_1609_; lean_object* v_children_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1619_; 
v_tag_1608_ = lean_ctor_get(v_x_1607_, 0);
v_attrs_1609_ = lean_ctor_get(v_x_1607_, 1);
v_children_1610_ = lean_ctor_get(v_x_1607_, 2);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_x_1607_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1612_ = v_x_1607_;
v_isShared_1613_ = v_isSharedCheck_1619_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_children_1610_);
lean_inc(v_attrs_1609_);
lean_inc(v_tag_1608_);
lean_dec(v_x_1607_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1619_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
lean_inc_ref(v_fn_1606_);
v___x_1614_ = l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(v_fn_1606_, v_children_1610_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 2, v___x_1614_);
v___x_1616_ = v___x_1612_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_tag_1608_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_attrs_1609_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_apply_1(v_fn_1606_, v___x_1616_);
return v___x_1617_;
}
}
}
case 3:
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1631_; 
v_a_1620_ = lean_ctor_get(v_x_1607_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_x_1607_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1622_ = v_x_1607_;
v_isShared_1623_ = v_isSharedCheck_1631_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v_x_1607_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1631_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
size_t v_sz_1624_; size_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v_sz_1624_ = lean_array_size(v_a_1620_);
v___x_1625_ = ((size_t)0ULL);
lean_inc_ref(v_fn_1606_);
v___x_1626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0(v_fn_1606_, v_sz_1624_, v___x_1625_, v_a_1620_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1626_);
v___x_1628_ = v___x_1622_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_apply_1(v_fn_1606_, v___x_1628_);
return v___x_1629_;
}
}
}
default: 
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_apply_1(v_fn_1606_, v_x_1607_);
return v___x_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0(lean_object* v_fn_1633_, size_t v_sz_1634_, size_t v_i_1635_, lean_object* v_bs_1636_){
_start:
{
uint8_t v___x_1637_; 
v___x_1637_ = lean_usize_dec_lt(v_i_1635_, v_sz_1634_);
if (v___x_1637_ == 0)
{
lean_dec_ref(v_fn_1633_);
return v_bs_1636_;
}
else
{
lean_object* v_v_1638_; lean_object* v___x_1639_; lean_object* v_bs_x27_1640_; lean_object* v___x_1641_; size_t v___x_1642_; size_t v___x_1643_; lean_object* v___x_1644_; 
v_v_1638_ = lean_array_uget(v_bs_1636_, v_i_1635_);
v___x_1639_ = lean_unsigned_to_nat(0u);
v_bs_x27_1640_ = lean_array_uset(v_bs_1636_, v_i_1635_, v___x_1639_);
lean_inc_ref(v_fn_1633_);
v___x_1641_ = l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(v_fn_1633_, v_v_1638_);
v___x_1642_ = ((size_t)1ULL);
v___x_1643_ = lean_usize_add(v_i_1635_, v___x_1642_);
v___x_1644_ = lean_array_uset(v_bs_x27_1640_, v_i_1635_, v___x_1641_);
v_i_1635_ = v___x_1643_;
v_bs_1636_ = v___x_1644_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0___boxed(lean_object* v_fn_1646_, lean_object* v_sz_1647_, lean_object* v_i_1648_, lean_object* v_bs_1649_){
_start:
{
size_t v_sz_boxed_1650_; size_t v_i_boxed_1651_; lean_object* v_res_1652_; 
v_sz_boxed_1650_ = lean_unbox_usize(v_sz_1647_);
lean_dec(v_sz_1647_);
v_i_boxed_1651_ = lean_unbox_usize(v_i_1648_);
lean_dec(v_i_1648_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0_spec__0(v_fn_1646_, v_sz_boxed_1650_, v_i_boxed_1651_, v_bs_1649_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_rewritePost(lean_object* v_fn_1653_, lean_object* v_h_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Html_rewritePostM___at___00Lean_Html_rewritePost_spec__0(v_fn_1653_, v_h_1654_);
return v___x_1655_;
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
