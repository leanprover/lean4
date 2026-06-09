// Lean compiler output
// Module: Std.Internal.Do.Triple.Basic
// Imports: public import Std.Internal.Do.WP
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term⊥"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value;
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_1),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(232, 78, 68, 112, 65, 121, 100, 195)}};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value;
static const lean_string_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊥"};
static const lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18 = (const lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18_value;
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
static const lean_ctor_object l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value_aux_0),((lean_object*)&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
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
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5));
v___x_71_ = l_String_toRawSubstring_x27(v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1(lean_object* v_x_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4));
lean_inc(v_x_100_);
v___x_104_ = l_Lean_Syntax_isOfKind(v_x_100_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_x_100_);
v___x_105_ = lean_box(1);
v___x_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v_a_102_);
return v___x_106_;
}
else
{
lean_object* v_quotContext_107_; lean_object* v_currMacroScope_108_; lean_object* v_ref_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_quotContext_107_ = lean_ctor_get(v_a_101_, 1);
v_currMacroScope_108_ = lean_ctor_get(v_a_101_, 2);
v_ref_109_ = lean_ctor_get(v_a_101_, 5);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = l_Lean_Syntax_getArg(v_x_100_, v___x_110_);
v___x_112_ = lean_unsigned_to_nat(3u);
v___x_113_ = l_Lean_Syntax_getArg(v_x_100_, v___x_112_);
v___x_114_ = lean_unsigned_to_nat(5u);
v___x_115_ = l_Lean_Syntax_getArg(v_x_100_, v___x_114_);
lean_dec(v_x_100_);
v___x_116_ = 0;
v___x_117_ = l_Lean_SourceInfo_fromRef(v_ref_109_, v___x_116_);
v___x_118_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4));
v___x_119_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6);
v___x_120_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7));
lean_inc(v_currMacroScope_108_);
lean_inc(v_quotContext_107_);
v___x_121_ = l_Lean_addMacroScope(v_quotContext_107_, v___x_120_, v_currMacroScope_108_);
v___x_122_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12));
lean_inc_n(v___x_117_, 4);
v___x_123_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_123_, 0, v___x_117_);
lean_ctor_set(v___x_123_, 1, v___x_119_);
lean_ctor_set(v___x_123_, 2, v___x_121_);
lean_ctor_set(v___x_123_, 3, v___x_122_);
v___x_124_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14));
v___x_125_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17));
v___x_126_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18));
v___x_127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_117_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = l_Lean_Syntax_node1(v___x_117_, v___x_125_, v___x_127_);
v___x_129_ = l_Lean_Syntax_node4(v___x_117_, v___x_124_, v___x_111_, v___x_113_, v___x_115_, v___x_128_);
v___x_130_ = l_Lean_Syntax_node2(v___x_117_, v___x_118_, v___x_123_, v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_102_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___boxed(lean_object* v_x_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1(v_x_132_, v_a_133_, v_a_134_);
lean_dec_ref(v_a_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1(lean_object* v_x_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4));
lean_inc(v_x_139_);
v___x_143_ = l_Lean_Syntax_isOfKind(v_x_139_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_x_139_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_a_141_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = l_Lean_Syntax_getArg(v_x_139_, v___x_146_);
v___x_148_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1));
lean_inc(v___x_147_);
v___x_149_ = l_Lean_Syntax_isOfKind(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v___x_147_);
lean_dec(v_x_139_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_a_141_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = l_Lean_Syntax_getArg(v_x_139_, v___x_152_);
lean_dec(v_x_139_);
v___x_154_ = lean_unsigned_to_nat(4u);
lean_inc(v___x_153_);
v___x_155_ = l_Lean_Syntax_matchesNull(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v___x_153_);
lean_dec(v___x_147_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_141_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_158_ = lean_unsigned_to_nat(3u);
v___x_159_ = l_Lean_Syntax_getArg(v___x_153_, v___x_158_);
v___x_160_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17));
v___x_161_ = l_Lean_Syntax_isOfKind(v___x_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v___x_153_);
lean_dec(v___x_147_);
v___x_162_ = lean_box(0);
v___x_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_a_141_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_ref_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_164_ = l_Lean_Syntax_getArg(v___x_153_, v___x_146_);
v___x_165_ = l_Lean_Syntax_getArg(v___x_153_, v___x_152_);
v___x_166_ = lean_unsigned_to_nat(2u);
v___x_167_ = l_Lean_Syntax_getArg(v___x_153_, v___x_166_);
lean_dec(v___x_153_);
v_ref_168_ = l_Lean_replaceRef(v___x_147_, v_a_140_);
lean_dec(v___x_147_);
v___x_169_ = 0;
v___x_170_ = l_Lean_SourceInfo_fromRef(v_ref_168_, v___x_169_);
lean_dec(v_ref_168_);
v___x_171_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4));
v___x_172_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7));
lean_inc_n(v___x_170_, 4);
v___x_173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_170_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13));
v___x_175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_170_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17));
v___x_177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_170_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21));
v___x_179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_170_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = l_Lean_Syntax_node7(v___x_170_, v___x_171_, v___x_173_, v___x_164_, v___x_175_, v___x_165_, v___x_177_, v___x_167_, v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_a_141_);
return v___x_181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___boxed(lean_object* v_x_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1(v_x_182_, v_a_183_, v_a_184_);
lean_dec(v_a_183_);
return v_res_185_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7));
v___x_230_ = l_String_toRawSubstring_x27(v___x_229_);
return v___x_230_;
}
}
static lean_object* _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19(void){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Array_mkArray0(lean_box(0));
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1(lean_object* v_x_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1));
lean_inc(v_x_263_);
v___x_267_ = l_Lean_Syntax_isOfKind(v_x_263_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v_x_263_);
v___x_268_ = lean_box(1);
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_a_265_);
return v___x_269_;
}
else
{
lean_object* v_quotContext_270_; lean_object* v_currMacroScope_271_; lean_object* v_ref_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v_quotContext_270_ = lean_ctor_get(v_a_264_, 1);
v_currMacroScope_271_ = lean_ctor_get(v_a_264_, 2);
v_ref_272_ = lean_ctor_get(v_a_264_, 5);
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = l_Lean_Syntax_getArg(v_x_263_, v___x_273_);
v___x_275_ = lean_unsigned_to_nat(3u);
v___x_276_ = l_Lean_Syntax_getArg(v_x_263_, v___x_275_);
v___x_277_ = lean_unsigned_to_nat(5u);
v___x_278_ = l_Lean_Syntax_getArg(v_x_263_, v___x_277_);
v___x_279_ = lean_unsigned_to_nat(7u);
v___x_280_ = l_Lean_Syntax_getArg(v_x_263_, v___x_279_);
lean_dec(v_x_263_);
v___x_281_ = 0;
v___x_282_ = l_Lean_SourceInfo_fromRef(v_ref_272_, v___x_281_);
v___x_283_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4));
v___x_284_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6);
v___x_285_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7));
lean_inc_n(v_currMacroScope_271_, 2);
lean_inc_n(v_quotContext_270_, 2);
v___x_286_ = l_Lean_addMacroScope(v_quotContext_270_, v___x_285_, v_currMacroScope_271_);
v___x_287_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12));
lean_inc_n(v___x_282_, 16);
v___x_288_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_288_, 0, v___x_282_);
lean_ctor_set(v___x_288_, 1, v___x_284_);
lean_ctor_set(v___x_288_, 2, v___x_286_);
lean_ctor_set(v___x_288_, 3, v___x_287_);
v___x_289_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14));
v___x_290_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1));
v___x_291_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3));
v___x_292_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4));
v___x_293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_282_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6));
v___x_295_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8);
v___x_296_ = lean_box(0);
v___x_297_ = l_Lean_addMacroScope(v_quotContext_270_, v___x_296_, v_currMacroScope_271_);
v___x_298_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14));
v___x_299_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_299_, 0, v___x_282_);
lean_ctor_set(v___x_299_, 1, v___x_295_);
lean_ctor_set(v___x_299_, 2, v___x_297_);
lean_ctor_set(v___x_299_, 3, v___x_298_);
v___x_300_ = l_Lean_Syntax_node1(v___x_282_, v___x_294_, v___x_299_);
v___x_301_ = l_Lean_Syntax_node2(v___x_282_, v___x_291_, v___x_293_, v___x_300_);
v___x_302_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15));
v___x_303_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16));
v___x_304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_282_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
v___x_305_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18));
v___x_306_ = l_Lean_Syntax_node1(v___x_282_, v___x_289_, v___x_278_);
v___x_307_ = lean_obj_once(&l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19, &l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19_once, _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19);
v___x_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_308_, 0, v___x_282_);
lean_ctor_set(v___x_308_, 1, v___x_289_);
lean_ctor_set(v___x_308_, 2, v___x_307_);
v___x_309_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20));
v___x_310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_282_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = l_Lean_Syntax_node4(v___x_282_, v___x_305_, v___x_306_, v___x_308_, v___x_310_, v___x_280_);
v___x_312_ = l_Lean_Syntax_node2(v___x_282_, v___x_303_, v___x_304_, v___x_311_);
v___x_313_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21));
v___x_314_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_282_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = l_Lean_Syntax_node3(v___x_282_, v___x_290_, v___x_301_, v___x_312_, v___x_314_);
v___x_316_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17));
v___x_317_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18));
v___x_318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_282_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = l_Lean_Syntax_node1(v___x_282_, v___x_316_, v___x_318_);
v___x_320_ = l_Lean_Syntax_node4(v___x_282_, v___x_289_, v___x_274_, v___x_276_, v___x_315_, v___x_319_);
v___x_321_ = l_Lean_Syntax_node2(v___x_282_, v___x_283_, v___x_288_, v___x_320_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v_a_265_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___boxed(lean_object* v_x_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1(v_x_323_, v_a_324_, v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2(lean_object* v_x_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4));
lean_inc(v_x_327_);
v___x_331_ = l_Lean_Syntax_isOfKind(v_x_327_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_x_327_);
v___x_332_ = lean_box(0);
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_a_329_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = l_Lean_Syntax_getArg(v_x_327_, v___x_334_);
v___x_336_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1));
lean_inc(v___x_335_);
v___x_337_ = l_Lean_Syntax_isOfKind(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v___x_335_);
lean_dec(v_x_327_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v_a_329_);
return v___x_339_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = l_Lean_Syntax_getArg(v_x_327_, v___x_340_);
lean_dec(v_x_327_);
v___x_342_ = lean_unsigned_to_nat(4u);
lean_inc(v___x_341_);
v___x_343_ = l_Lean_Syntax_matchesNull(v___x_341_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec(v___x_341_);
lean_dec(v___x_335_);
v___x_344_ = lean_box(0);
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_a_329_);
return v___x_345_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_346_ = lean_unsigned_to_nat(2u);
v___x_347_ = l_Lean_Syntax_getArg(v___x_341_, v___x_346_);
v___x_348_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16));
lean_inc(v___x_347_);
v___x_349_ = l_Lean_Syntax_isOfKind(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v___x_347_);
lean_dec(v___x_341_);
lean_dec(v___x_335_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_a_329_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_352_ = l_Lean_Syntax_getArg(v___x_347_, v___x_340_);
lean_dec(v___x_347_);
v___x_353_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18));
lean_inc(v___x_352_);
v___x_354_ = l_Lean_Syntax_isOfKind(v___x_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v___x_352_);
lean_dec(v___x_341_);
lean_dec(v___x_335_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_a_329_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = l_Lean_Syntax_getArg(v___x_352_, v___x_334_);
lean_inc(v___x_357_);
v___x_358_ = l_Lean_Syntax_matchesNull(v___x_357_, v___x_340_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec(v___x_357_);
lean_dec(v___x_352_);
lean_dec(v___x_341_);
lean_dec(v___x_335_);
v___x_359_ = lean_box(0);
v___x_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v_a_329_);
return v___x_360_;
}
else
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = l_Lean_Syntax_getArg(v___x_352_, v___x_340_);
v___x_362_ = l_Lean_Syntax_matchesNull(v___x_361_, v___x_334_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v___x_357_);
lean_dec(v___x_352_);
lean_dec(v___x_341_);
lean_dec(v___x_335_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_a_329_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_365_ = lean_unsigned_to_nat(3u);
v___x_366_ = l_Lean_Syntax_getArg(v___x_341_, v___x_365_);
v___x_367_ = ((lean_object*)(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17));
v___x_368_ = l_Lean_Syntax_isOfKind(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_dec(v___x_357_);
lean_dec(v___x_352_);
lean_dec(v___x_341_);
lean_dec(v___x_335_);
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v_a_329_);
return v___x_370_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v_ref_375_; uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_371_ = l_Lean_Syntax_getArg(v___x_341_, v___x_334_);
v___x_372_ = l_Lean_Syntax_getArg(v___x_341_, v___x_340_);
lean_dec(v___x_341_);
v___x_373_ = l_Lean_Syntax_getArg(v___x_357_, v___x_334_);
lean_dec(v___x_357_);
v___x_374_ = l_Lean_Syntax_getArg(v___x_352_, v___x_365_);
lean_dec(v___x_352_);
v_ref_375_ = l_Lean_replaceRef(v___x_335_, v_a_328_);
lean_dec(v___x_335_);
v___x_376_ = 0;
v___x_377_ = l_Lean_SourceInfo_fromRef(v_ref_375_, v___x_376_);
lean_dec(v_ref_375_);
v___x_378_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1));
v___x_379_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7));
lean_inc_n(v___x_377_, 5);
v___x_380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_377_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13));
v___x_382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_377_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17));
v___x_384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_377_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2));
v___x_386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_377_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = ((lean_object*)(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21));
v___x_388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_377_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_unsigned_to_nat(9u);
v___x_390_ = lean_mk_empty_array_with_capacity(v___x_389_);
v___x_391_ = lean_array_push(v___x_390_, v___x_380_);
v___x_392_ = lean_array_push(v___x_391_, v___x_371_);
v___x_393_ = lean_array_push(v___x_392_, v___x_382_);
v___x_394_ = lean_array_push(v___x_393_, v___x_372_);
v___x_395_ = lean_array_push(v___x_394_, v___x_384_);
v___x_396_ = lean_array_push(v___x_395_, v___x_373_);
v___x_397_ = lean_array_push(v___x_396_, v___x_386_);
v___x_398_ = lean_array_push(v___x_397_, v___x_374_);
v___x_399_ = lean_array_push(v___x_398_, v___x_388_);
v___x_400_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_400_, 0, v___x_377_);
lean_ctor_set(v___x_400_, 1, v___x_378_);
lean_ctor_set(v___x_400_, 2, v___x_399_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v_a_329_);
return v___x_401_;
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
LEAN_EXPORT lean_object* l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2___boxed(lean_object* v_x_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2(v_x_402_, v_a_403_, v_a_404_);
lean_dec(v_a_403_);
return v_res_405_;
}
}
lean_object* runtime_initialize_Std_Internal_Do_WP(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Do_WP(builtin);
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
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_WP(builtin);
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
