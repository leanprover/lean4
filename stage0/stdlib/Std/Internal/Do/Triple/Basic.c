// Lean compiler output
// Module: Std.Internal.Do.Triple.Basic
// Imports: public import Std.Internal.Do.WP public import Std.Internal.Do.ExceptPost
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value;
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value;
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value;
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 11, .m_data = "term⦃_⦄_⦃_⦄"};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_0),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_1),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_2),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value),LEAN_SCALAR_PTR_LITERAL(189, 151, 205, 53, 56, 32, 92, 197)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value;
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value;
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⦃ "};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value;
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value;
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⦄ "};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value;
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⦃ "};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value;
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = " ⦄"};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___u2984 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(56, 148, 225, 137, 79, 125, 168, 172)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_0),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_1),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(190, 57, 218, 157, 42, 52, 8, 129)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Order.bot"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bot"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(89, 51, 159, 172, 220, 225, 54, 137)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__20 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__20_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__21 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__21_value;
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 13, .m_data = "term⦃_⦄_⦃_,_⦄"};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_0),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_1),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_2),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 250, 213, 109, 82, 232, 13, 204)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value;
static const lean_string_object l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value;
static const lean_ctor_object l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value)}};
static const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984 = (const lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_0),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_1),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value;
static lean_once_cell_t l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21_value;
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Do_tripleEPost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tripleEPost"};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__0 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__1_value_aux_0),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__1_value_aux_1),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__1_value_aux_2),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 228, 187, 179, 135, 251, 133, 128)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__1 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__1_value;
static const lean_string_object l_Std_Internal_Do_tripleEPost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__2 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__2_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__2_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__3 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__3_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__3_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__4 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__4_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__2_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__5 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__5_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__4_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__5_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__6 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__6_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__6_value),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__7 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__7_value;
static const lean_ctor_object l_Std_Internal_Do_tripleEPost___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__1_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_tripleEPost___closed__7_value)}};
static const lean_object* l_Std_Internal_Do_tripleEPost___closed__8 = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__8_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Do_tripleEPost = (const lean_object*)&l_Std_Internal_Do_tripleEPost___closed__8_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 12, .m_data = "termEpost⟨_⟩"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__0 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__0_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_0),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_1),((lean_object*)&l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value_aux_2),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 191, 145, 121, 242, 68, 46, 80)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 6, .m_data = "epost⟨"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__2 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__2_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__3 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__3_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__4 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Do_unexpandTripleEPost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦃"};
static const lean_object* l_Std_Internal_Do_unexpandTripleEPost___closed__0 = (const lean_object*)&l_Std_Internal_Do_unexpandTripleEPost___closed__0_value;
static const lean_string_object l_Std_Internal_Do_unexpandTripleEPost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦄"};
static const lean_object* l_Std_Internal_Do_unexpandTripleEPost___closed__1 = (const lean_object*)&l_Std_Internal_Do_unexpandTripleEPost___closed__1_value;
static const lean_string_object l_Std_Internal_Do_unexpandTripleEPost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Std_Internal_Do_unexpandTripleEPost___closed__2 = (const lean_object*)&l_Std_Internal_Do_unexpandTripleEPost___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandTripleEPost(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandTripleEPost___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5));
v___x_71_ = l_String_toRawSubstring_x27(v___x_70_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15));
v___x_95_ = l_String_toRawSubstring_x27(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1(lean_object* v_x_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4));
lean_inc(v_x_108_);
v___x_112_ = l_Lean_Syntax_isOfKind(v_x_108_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_x_108_);
v___x_113_ = lean_box(1);
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_a_110_);
return v___x_114_;
}
else
{
lean_object* v_quotContext_115_; lean_object* v_currMacroScope_116_; lean_object* v_ref_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_quotContext_115_ = lean_ctor_get(v_a_109_, 1);
v_currMacroScope_116_ = lean_ctor_get(v_a_109_, 2);
v_ref_117_ = lean_ctor_get(v_a_109_, 5);
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = l_Lean_Syntax_getArg(v_x_108_, v___x_118_);
v___x_120_ = lean_unsigned_to_nat(3u);
v___x_121_ = l_Lean_Syntax_getArg(v_x_108_, v___x_120_);
v___x_122_ = lean_unsigned_to_nat(5u);
v___x_123_ = l_Lean_Syntax_getArg(v_x_108_, v___x_122_);
lean_dec(v_x_108_);
v___x_124_ = 0;
v___x_125_ = l_Lean_SourceInfo_fromRef(v_ref_117_, v___x_124_);
v___x_126_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4));
v___x_127_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6);
v___x_128_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7));
lean_inc_n(v_currMacroScope_116_, 2);
lean_inc_n(v_quotContext_115_, 2);
v___x_129_ = l_Lean_addMacroScope(v_quotContext_115_, v___x_128_, v_currMacroScope_116_);
v___x_130_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12));
lean_inc_n(v___x_125_, 3);
v___x_131_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_131_, 0, v___x_125_);
lean_ctor_set(v___x_131_, 1, v___x_127_);
lean_ctor_set(v___x_131_, 2, v___x_129_);
lean_ctor_set(v___x_131_, 3, v___x_130_);
v___x_132_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14));
v___x_133_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16);
v___x_134_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19));
v___x_135_ = l_Lean_addMacroScope(v_quotContext_115_, v___x_134_, v_currMacroScope_116_);
v___x_136_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__21));
v___x_137_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_137_, 0, v___x_125_);
lean_ctor_set(v___x_137_, 1, v___x_133_);
lean_ctor_set(v___x_137_, 2, v___x_135_);
lean_ctor_set(v___x_137_, 3, v___x_136_);
v___x_138_ = l_Lean_Syntax_node4(v___x_125_, v___x_132_, v___x_119_, v___x_121_, v___x_123_, v___x_137_);
v___x_139_ = l_Lean_Syntax_node2(v___x_125_, v___x_126_, v___x_131_, v___x_138_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v_a_110_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___boxed(lean_object* v_x_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1(v_x_141_, v_a_142_, v_a_143_);
lean_dec_ref(v_a_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1(lean_object* v_x_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4));
lean_inc(v_x_148_);
v___x_152_ = l_Lean_Syntax_isOfKind(v_x_148_, v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_x_148_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_a_150_);
return v___x_154_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = l_Lean_Syntax_getArg(v_x_148_, v___x_155_);
v___x_157_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1));
lean_inc(v___x_156_);
v___x_158_ = l_Lean_Syntax_isOfKind(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v___x_156_);
lean_dec(v_x_148_);
v___x_159_ = lean_box(0);
v___x_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v_a_150_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = l_Lean_Syntax_getArg(v_x_148_, v___x_161_);
lean_dec(v_x_148_);
v___x_163_ = lean_unsigned_to_nat(4u);
lean_inc(v___x_162_);
v___x_164_ = l_Lean_Syntax_matchesNull(v___x_162_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v___x_162_);
lean_dec(v___x_156_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v_a_150_);
return v___x_166_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_167_ = lean_unsigned_to_nat(3u);
v___x_168_ = l_Lean_Syntax_getArg(v___x_162_, v___x_167_);
v___x_169_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19));
v___x_170_ = l_Lean_Syntax_matchesIdent(v___x_168_, v___x_169_);
lean_dec(v___x_168_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v___x_162_);
lean_dec(v___x_156_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v_a_150_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_ref_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_173_ = l_Lean_Syntax_getArg(v___x_162_, v___x_155_);
v___x_174_ = l_Lean_Syntax_getArg(v___x_162_, v___x_161_);
v___x_175_ = lean_unsigned_to_nat(2u);
v___x_176_ = l_Lean_Syntax_getArg(v___x_162_, v___x_175_);
lean_dec(v___x_162_);
v_ref_177_ = l_Lean_replaceRef(v___x_156_, v_a_149_);
lean_dec(v___x_156_);
v___x_178_ = 0;
v___x_179_ = l_Lean_SourceInfo_fromRef(v_ref_177_, v___x_178_);
lean_dec(v_ref_177_);
v___x_180_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4));
v___x_181_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7));
lean_inc_n(v___x_179_, 4);
v___x_182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_179_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13));
v___x_184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_179_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17));
v___x_186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_179_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21));
v___x_188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_179_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = l_Lean_Syntax_node7(v___x_179_, v___x_180_, v___x_182_, v___x_173_, v___x_184_, v___x_174_, v___x_186_, v___x_176_, v___x_188_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_150_);
return v___x_190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___boxed(lean_object* v_x_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1(v_x_191_, v_a_192_, v_a_193_);
lean_dec(v_a_192_);
return v_res_194_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7));
v___x_239_ = l_String_toRawSubstring_x27(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19(void){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Array_mkArray0(lean_box(0));
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1(lean_object* v_x_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1));
lean_inc(v_x_272_);
v___x_276_ = l_Lean_Syntax_isOfKind(v_x_272_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v_x_272_);
v___x_277_ = lean_box(1);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_a_274_);
return v___x_278_;
}
else
{
lean_object* v_quotContext_279_; lean_object* v_currMacroScope_280_; lean_object* v_ref_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_quotContext_279_ = lean_ctor_get(v_a_273_, 1);
v_currMacroScope_280_ = lean_ctor_get(v_a_273_, 2);
v_ref_281_ = lean_ctor_get(v_a_273_, 5);
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = l_Lean_Syntax_getArg(v_x_272_, v___x_282_);
v___x_284_ = lean_unsigned_to_nat(3u);
v___x_285_ = l_Lean_Syntax_getArg(v_x_272_, v___x_284_);
v___x_286_ = lean_unsigned_to_nat(5u);
v___x_287_ = l_Lean_Syntax_getArg(v_x_272_, v___x_286_);
v___x_288_ = lean_unsigned_to_nat(7u);
v___x_289_ = l_Lean_Syntax_getArg(v_x_272_, v___x_288_);
lean_dec(v_x_272_);
v___x_290_ = 0;
v___x_291_ = l_Lean_SourceInfo_fromRef(v_ref_281_, v___x_290_);
v___x_292_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4));
v___x_293_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6);
v___x_294_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7));
lean_inc_n(v_currMacroScope_280_, 3);
lean_inc_n(v_quotContext_279_, 3);
v___x_295_ = l_Lean_addMacroScope(v_quotContext_279_, v___x_294_, v_currMacroScope_280_);
v___x_296_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12));
lean_inc_n(v___x_291_, 15);
v___x_297_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_297_, 0, v___x_291_);
lean_ctor_set(v___x_297_, 1, v___x_293_);
lean_ctor_set(v___x_297_, 2, v___x_295_);
lean_ctor_set(v___x_297_, 3, v___x_296_);
v___x_298_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14));
v___x_299_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1));
v___x_300_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3));
v___x_301_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4));
v___x_302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_291_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6));
v___x_304_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8);
v___x_305_ = lean_box(0);
v___x_306_ = l_Lean_addMacroScope(v_quotContext_279_, v___x_305_, v_currMacroScope_280_);
v___x_307_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14));
v___x_308_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_308_, 0, v___x_291_);
lean_ctor_set(v___x_308_, 1, v___x_304_);
lean_ctor_set(v___x_308_, 2, v___x_306_);
lean_ctor_set(v___x_308_, 3, v___x_307_);
v___x_309_ = l_Lean_Syntax_node1(v___x_291_, v___x_303_, v___x_308_);
v___x_310_ = l_Lean_Syntax_node2(v___x_291_, v___x_300_, v___x_302_, v___x_309_);
v___x_311_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15));
v___x_312_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16));
v___x_313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_291_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
v___x_314_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18));
v___x_315_ = l_Lean_Syntax_node1(v___x_291_, v___x_298_, v___x_287_);
v___x_316_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19);
v___x_317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_317_, 0, v___x_291_);
lean_ctor_set(v___x_317_, 1, v___x_298_);
lean_ctor_set(v___x_317_, 2, v___x_316_);
v___x_318_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20));
v___x_319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_291_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = l_Lean_Syntax_node4(v___x_291_, v___x_314_, v___x_315_, v___x_317_, v___x_319_, v___x_289_);
v___x_321_ = l_Lean_Syntax_node2(v___x_291_, v___x_312_, v___x_313_, v___x_320_);
v___x_322_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21));
v___x_323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_291_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = l_Lean_Syntax_node3(v___x_291_, v___x_299_, v___x_310_, v___x_321_, v___x_323_);
v___x_325_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16);
v___x_326_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19));
v___x_327_ = l_Lean_addMacroScope(v_quotContext_279_, v___x_326_, v_currMacroScope_280_);
v___x_328_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__21));
v___x_329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_329_, 0, v___x_291_);
lean_ctor_set(v___x_329_, 1, v___x_325_);
lean_ctor_set(v___x_329_, 2, v___x_327_);
lean_ctor_set(v___x_329_, 3, v___x_328_);
v___x_330_ = l_Lean_Syntax_node4(v___x_291_, v___x_298_, v___x_283_, v___x_285_, v___x_324_, v___x_329_);
v___x_331_ = l_Lean_Syntax_node2(v___x_291_, v___x_292_, v___x_297_, v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_a_274_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___boxed(lean_object* v_x_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1(v_x_333_, v_a_334_, v_a_335_);
lean_dec_ref(v_a_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2(lean_object* v_x_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4));
lean_inc(v_x_337_);
v___x_341_ = l_Lean_Syntax_isOfKind(v_x_337_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_x_337_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_a_339_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = l_Lean_Syntax_getArg(v_x_337_, v___x_344_);
v___x_346_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1));
lean_inc(v___x_345_);
v___x_347_ = l_Lean_Syntax_isOfKind(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v___x_345_);
lean_dec(v_x_337_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_a_339_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = l_Lean_Syntax_getArg(v_x_337_, v___x_350_);
lean_dec(v_x_337_);
v___x_352_ = lean_unsigned_to_nat(4u);
lean_inc(v___x_351_);
v___x_353_ = l_Lean_Syntax_matchesNull(v___x_351_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v___x_351_);
lean_dec(v___x_345_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v_a_339_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_356_ = lean_unsigned_to_nat(2u);
v___x_357_ = l_Lean_Syntax_getArg(v___x_351_, v___x_356_);
v___x_358_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16));
lean_inc(v___x_357_);
v___x_359_ = l_Lean_Syntax_isOfKind(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v___x_357_);
lean_dec(v___x_351_);
lean_dec(v___x_345_);
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v_a_339_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = l_Lean_Syntax_getArg(v___x_357_, v___x_350_);
lean_dec(v___x_357_);
v___x_363_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18));
lean_inc(v___x_362_);
v___x_364_ = l_Lean_Syntax_isOfKind(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec(v___x_362_);
lean_dec(v___x_351_);
lean_dec(v___x_345_);
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_a_339_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = l_Lean_Syntax_getArg(v___x_362_, v___x_344_);
lean_inc(v___x_367_);
v___x_368_ = l_Lean_Syntax_matchesNull(v___x_367_, v___x_350_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_dec(v___x_367_);
lean_dec(v___x_362_);
lean_dec(v___x_351_);
lean_dec(v___x_345_);
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v_a_339_);
return v___x_370_;
}
else
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = l_Lean_Syntax_getArg(v___x_362_, v___x_350_);
v___x_372_ = l_Lean_Syntax_matchesNull(v___x_371_, v___x_344_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v___x_367_);
lean_dec(v___x_362_);
lean_dec(v___x_351_);
lean_dec(v___x_345_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v_a_339_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_375_ = lean_unsigned_to_nat(3u);
v___x_376_ = l_Lean_Syntax_getArg(v___x_351_, v___x_375_);
v___x_377_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__19));
v___x_378_ = l_Lean_Syntax_matchesIdent(v___x_376_, v___x_377_);
lean_dec(v___x_376_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v___x_367_);
lean_dec(v___x_362_);
lean_dec(v___x_351_);
lean_dec(v___x_345_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v_a_339_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v_ref_385_; uint8_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_381_ = l_Lean_Syntax_getArg(v___x_351_, v___x_344_);
v___x_382_ = l_Lean_Syntax_getArg(v___x_351_, v___x_350_);
lean_dec(v___x_351_);
v___x_383_ = l_Lean_Syntax_getArg(v___x_367_, v___x_344_);
lean_dec(v___x_367_);
v___x_384_ = l_Lean_Syntax_getArg(v___x_362_, v___x_375_);
lean_dec(v___x_362_);
v_ref_385_ = l_Lean_replaceRef(v___x_345_, v_a_338_);
lean_dec(v___x_345_);
v___x_386_ = 0;
v___x_387_ = l_Lean_SourceInfo_fromRef(v_ref_385_, v___x_386_);
lean_dec(v_ref_385_);
v___x_388_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1));
v___x_389_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7));
lean_inc_n(v___x_387_, 5);
v___x_390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_387_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13));
v___x_392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_387_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17));
v___x_394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_387_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2));
v___x_396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_387_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21));
v___x_398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_387_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_unsigned_to_nat(9u);
v___x_400_ = lean_mk_empty_array_with_capacity(v___x_399_);
v___x_401_ = lean_array_push(v___x_400_, v___x_390_);
v___x_402_ = lean_array_push(v___x_401_, v___x_381_);
v___x_403_ = lean_array_push(v___x_402_, v___x_392_);
v___x_404_ = lean_array_push(v___x_403_, v___x_382_);
v___x_405_ = lean_array_push(v___x_404_, v___x_394_);
v___x_406_ = lean_array_push(v___x_405_, v___x_383_);
v___x_407_ = lean_array_push(v___x_406_, v___x_396_);
v___x_408_ = lean_array_push(v___x_407_, v___x_384_);
v___x_409_ = lean_array_push(v___x_408_, v___x_398_);
v___x_410_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_410_, 0, v___x_387_);
lean_ctor_set(v___x_410_, 1, v___x_388_);
lean_ctor_set(v___x_410_, 2, v___x_409_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_a_339_);
return v___x_411_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2___boxed(lean_object* v_x_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2(v_x_412_, v_a_413_, v_a_414_);
lean_dec(v_a_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1(lean_object* v_x_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = ((lean_object*)(l_Std_Internal_Do_tripleEPost___closed__1));
lean_inc(v_x_456_);
v___x_460_ = l_Lean_Syntax_isOfKind(v_x_456_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec(v_x_456_);
v___x_461_ = lean_box(1);
v___x_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v_a_458_);
return v___x_462_;
}
else
{
lean_object* v_quotContext_463_; lean_object* v_currMacroScope_464_; lean_object* v_ref_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_Es_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_quotContext_463_ = lean_ctor_get(v_a_457_, 1);
v_currMacroScope_464_ = lean_ctor_get(v_a_457_, 2);
v_ref_465_ = lean_ctor_get(v_a_457_, 5);
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = l_Lean_Syntax_getArg(v_x_456_, v___x_466_);
v___x_468_ = lean_unsigned_to_nat(3u);
v___x_469_ = l_Lean_Syntax_getArg(v_x_456_, v___x_468_);
v___x_470_ = lean_unsigned_to_nat(5u);
v___x_471_ = l_Lean_Syntax_getArg(v_x_456_, v___x_470_);
v___x_472_ = lean_unsigned_to_nat(7u);
v___x_473_ = l_Lean_Syntax_getArg(v_x_456_, v___x_472_);
lean_dec(v_x_456_);
v_Es_474_ = l_Lean_Syntax_getArgs(v___x_473_);
lean_dec(v___x_473_);
v___x_475_ = 0;
v___x_476_ = l_Lean_SourceInfo_fromRef(v_ref_465_, v___x_475_);
v___x_477_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4));
v___x_478_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6);
v___x_479_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7));
lean_inc(v_currMacroScope_464_);
lean_inc(v_quotContext_463_);
v___x_480_ = l_Lean_addMacroScope(v_quotContext_463_, v___x_479_, v_currMacroScope_464_);
v___x_481_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12));
lean_inc_n(v___x_476_, 6);
v___x_482_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_482_, 0, v___x_476_);
lean_ctor_set(v___x_482_, 1, v___x_478_);
lean_ctor_set(v___x_482_, 2, v___x_480_);
lean_ctor_set(v___x_482_, 3, v___x_481_);
v___x_483_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14));
v___x_484_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1));
v___x_485_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__2));
v___x_486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_476_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19);
v___x_488_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__3));
v___x_489_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_Es_474_);
lean_dec_ref(v_Es_474_);
v___x_490_ = l_Lean_Syntax_SepArray_ofElems(v___x_488_, v___x_489_);
lean_dec_ref(v___x_489_);
v___x_491_ = l_Array_append___redArg(v___x_487_, v___x_490_);
lean_dec_ref(v___x_490_);
v___x_492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_492_, 0, v___x_476_);
lean_ctor_set(v___x_492_, 1, v___x_483_);
lean_ctor_set(v___x_492_, 2, v___x_491_);
v___x_493_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__4));
v___x_494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_476_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = l_Lean_Syntax_node3(v___x_476_, v___x_484_, v___x_486_, v___x_492_, v___x_494_);
v___x_496_ = l_Lean_Syntax_node4(v___x_476_, v___x_483_, v___x_467_, v___x_469_, v___x_471_, v___x_495_);
v___x_497_ = l_Lean_Syntax_node2(v___x_476_, v___x_477_, v___x_482_, v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_a_458_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___boxed(lean_object* v_x_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1(v_x_499_, v_a_500_, v_a_501_);
lean_dec_ref(v_a_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandTripleEPost(lean_object* v_x_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4));
lean_inc(v_x_506_);
v___x_510_ = l_Lean_Syntax_isOfKind(v_x_506_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_x_506_);
v___x_511_ = lean_box(0);
v___x_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_a_508_);
return v___x_512_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = l_Lean_Syntax_getArg(v_x_506_, v___x_513_);
lean_dec(v_x_506_);
v___x_515_ = lean_unsigned_to_nat(4u);
lean_inc(v___x_514_);
v___x_516_ = l_Lean_Syntax_matchesNull(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v___x_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v_a_508_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_519_ = lean_unsigned_to_nat(3u);
v___x_520_ = l_Lean_Syntax_getArg(v___x_514_, v___x_519_);
v___x_521_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__tripleEPost__1___closed__1));
lean_inc(v___x_520_);
v___x_522_ = l_Lean_Syntax_isOfKind(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec(v___x_520_);
lean_dec(v___x_514_);
v___x_523_ = lean_box(0);
v___x_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v_a_508_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v_Es_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_525_ = l_Lean_Syntax_getArg(v___x_520_, v___x_513_);
lean_dec(v___x_520_);
v_Es_526_ = l_Lean_Syntax_getArgs(v___x_525_);
lean_dec(v___x_525_);
v___x_527_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_Es_526_);
lean_dec_ref(v_Es_526_);
v___x_528_ = lean_array_get_size(v___x_527_);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_nat_dec_eq(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_531_ = l_Lean_Syntax_getArg(v___x_514_, v___x_529_);
v___x_532_ = l_Lean_Syntax_getArg(v___x_514_, v___x_513_);
v___x_533_ = lean_unsigned_to_nat(2u);
v___x_534_ = l_Lean_Syntax_getArg(v___x_514_, v___x_533_);
lean_dec(v___x_514_);
v___x_535_ = l_Lean_SourceInfo_fromRef(v_a_507_, v___x_530_);
v___x_536_ = ((lean_object*)(l_Std_Internal_Do_tripleEPost___closed__1));
v___x_537_ = ((lean_object*)(l_Std_Internal_Do_unexpandTripleEPost___closed__0));
lean_inc_n(v___x_535_, 4);
v___x_538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_535_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = ((lean_object*)(l_Std_Internal_Do_unexpandTripleEPost___closed__1));
v___x_540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_535_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = ((lean_object*)(l_Std_Internal_Do_unexpandTripleEPost___closed__2));
v___x_542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_535_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14));
v___x_544_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19);
v___x_545_ = l_Lean_Syntax_SepArray_ofElems(v___x_541_, v___x_527_);
lean_dec_ref(v___x_527_);
v___x_546_ = l_Array_append___redArg(v___x_544_, v___x_545_);
lean_dec_ref(v___x_545_);
v___x_547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_547_, 0, v___x_535_);
lean_ctor_set(v___x_547_, 1, v___x_543_);
lean_ctor_set(v___x_547_, 2, v___x_546_);
v___x_548_ = lean_unsigned_to_nat(9u);
v___x_549_ = lean_mk_empty_array_with_capacity(v___x_548_);
lean_inc_ref(v___x_538_);
v___x_550_ = lean_array_push(v___x_549_, v___x_538_);
v___x_551_ = lean_array_push(v___x_550_, v___x_531_);
lean_inc_ref(v___x_540_);
v___x_552_ = lean_array_push(v___x_551_, v___x_540_);
v___x_553_ = lean_array_push(v___x_552_, v___x_532_);
v___x_554_ = lean_array_push(v___x_553_, v___x_538_);
v___x_555_ = lean_array_push(v___x_554_, v___x_534_);
v___x_556_ = lean_array_push(v___x_555_, v___x_542_);
v___x_557_ = lean_array_push(v___x_556_, v___x_547_);
v___x_558_ = lean_array_push(v___x_557_, v___x_540_);
v___x_559_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_559_, 0, v___x_535_);
lean_ctor_set(v___x_559_, 1, v___x_536_);
lean_ctor_set(v___x_559_, 2, v___x_558_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v_a_508_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v___x_527_);
lean_dec(v___x_514_);
v___x_561_ = lean_box(0);
v___x_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v_a_508_);
return v___x_562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_unexpandTripleEPost___boxed(lean_object* v_x_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_Internal_Do_unexpandTripleEPost(v_x_563_, v_a_564_, v_a_565_);
lean_dec(v_a_564_);
return v_res_566_;
}
}
lean_object* runtime_initialize_Std_Internal_Do_WP(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_ExceptPost(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Do_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_ExceptPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Do_WP(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_ExceptPost(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_ExceptPost(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_Triple_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
