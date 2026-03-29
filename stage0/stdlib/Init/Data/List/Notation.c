// Lean compiler output
// Module: Init.Data.List.Notation
// Imports: public meta import Init.Grind.Tactics public import Init.Notation
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_appendCore___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static const lean_string_object l_term_x5b___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term[_]"};
static const lean_object* l_term_x5b___x5d___closed__0 = (const lean_object*)&l_term_x5b___x5d___closed__0_value;
static const lean_ctor_object l_term_x5b___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_x5b___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 147, 168, 74, 195, 98, 232, 161)}};
static const lean_object* l_term_x5b___x5d___closed__1 = (const lean_object*)&l_term_x5b___x5d___closed__1_value;
static const lean_string_object l_term_x5b___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_term_x5b___x5d___closed__2 = (const lean_object*)&l_term_x5b___x5d___closed__2_value;
static const lean_ctor_object l_term_x5b___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_x5b___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_term_x5b___x5d___closed__3 = (const lean_object*)&l_term_x5b___x5d___closed__3_value;
static const lean_string_object l_term_x5b___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_term_x5b___x5d___closed__4 = (const lean_object*)&l_term_x5b___x5d___closed__4_value;
static const lean_ctor_object l_term_x5b___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__4_value)}};
static const lean_object* l_term_x5b___x5d___closed__5 = (const lean_object*)&l_term_x5b___x5d___closed__5_value;
static const lean_string_object l_term_x5b___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_term_x5b___x5d___closed__6 = (const lean_object*)&l_term_x5b___x5d___closed__6_value;
static const lean_ctor_object l_term_x5b___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_x5b___x5d___closed__6_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_term_x5b___x5d___closed__7 = (const lean_object*)&l_term_x5b___x5d___closed__7_value;
static const lean_string_object l_term_x5b___x5d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_term_x5b___x5d___closed__8 = (const lean_object*)&l_term_x5b___x5d___closed__8_value;
static const lean_ctor_object l_term_x5b___x5d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_x5b___x5d___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_term_x5b___x5d___closed__9 = (const lean_object*)&l_term_x5b___x5d___closed__9_value;
static const lean_ctor_object l_term_x5b___x5d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_term_x5b___x5d___closed__10 = (const lean_object*)&l_term_x5b___x5d___closed__10_value;
static const lean_string_object l_term_x5b___x5d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_term_x5b___x5d___closed__11 = (const lean_object*)&l_term_x5b___x5d___closed__11_value;
static const lean_string_object l_term_x5b___x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_term_x5b___x5d___closed__12 = (const lean_object*)&l_term_x5b___x5d___closed__12_value;
static const lean_ctor_object l_term_x5b___x5d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__12_value)}};
static const lean_object* l_term_x5b___x5d___closed__13 = (const lean_object*)&l_term_x5b___x5d___closed__13_value;
static const lean_ctor_object l_term_x5b___x5d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__10_value),((lean_object*)&l_term_x5b___x5d___closed__11_value),((lean_object*)&l_term_x5b___x5d___closed__13_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_term_x5b___x5d___closed__14 = (const lean_object*)&l_term_x5b___x5d___closed__14_value;
static const lean_ctor_object l_term_x5b___x5d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__7_value),((lean_object*)&l_term_x5b___x5d___closed__14_value)}};
static const lean_object* l_term_x5b___x5d___closed__15 = (const lean_object*)&l_term_x5b___x5d___closed__15_value;
static const lean_ctor_object l_term_x5b___x5d___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__3_value),((lean_object*)&l_term_x5b___x5d___closed__5_value),((lean_object*)&l_term_x5b___x5d___closed__15_value)}};
static const lean_object* l_term_x5b___x5d___closed__16 = (const lean_object*)&l_term_x5b___x5d___closed__16_value;
static const lean_string_object l_term_x5b___x5d___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_term_x5b___x5d___closed__17 = (const lean_object*)&l_term_x5b___x5d___closed__17_value;
static const lean_ctor_object l_term_x5b___x5d___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__17_value)}};
static const lean_object* l_term_x5b___x5d___closed__18 = (const lean_object*)&l_term_x5b___x5d___closed__18_value;
static const lean_ctor_object l_term_x5b___x5d___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__3_value),((lean_object*)&l_term_x5b___x5d___closed__16_value),((lean_object*)&l_term_x5b___x5d___closed__18_value)}};
static const lean_object* l_term_x5b___x5d___closed__19 = (const lean_object*)&l_term_x5b___x5d___closed__19_value;
static const lean_ctor_object l_term_x5b___x5d___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_term_x5b___x5d___closed__19_value)}};
static const lean_object* l_term_x5b___x5d___closed__20 = (const lean_object*)&l_term_x5b___x5d___closed__20_value;
LEAN_EXPORT const lean_object* l_term_x5b___x5d = (const lean_object*)&l_term_x5b___x5d___closed__20_value;
static const lean_string_object l_term_x25_x5b___x7c___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term%[_|_]"};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__0 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__0_value;
static const lean_ctor_object l_term_x25_x5b___x7c___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_x25_x5b___x7c___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 149, 151, 28, 109, 173, 225, 162)}};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__1 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__1_value;
static const lean_string_object l_term_x25_x5b___x7c___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "%["};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__2 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__2_value;
static const lean_ctor_object l_term_x25_x5b___x7c___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_x25_x5b___x7c___x5d___closed__2_value)}};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__3 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__3_value;
static const lean_string_object l_term_x25_x5b___x7c___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " | "};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__4 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__4_value;
static const lean_ctor_object l_term_x25_x5b___x7c___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_x25_x5b___x7c___x5d___closed__4_value)}};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__5 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__5_value;
static const lean_ctor_object l_term_x25_x5b___x7c___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__3_value),((lean_object*)&l_term_x5b___x5d___closed__14_value),((lean_object*)&l_term_x25_x5b___x7c___x5d___closed__5_value)}};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__6 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__6_value;
static const lean_ctor_object l_term_x25_x5b___x7c___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__3_value),((lean_object*)&l_term_x25_x5b___x7c___x5d___closed__6_value),((lean_object*)&l_term_x5b___x5d___closed__10_value)}};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__7 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__7_value;
static const lean_ctor_object l_term_x25_x5b___x7c___x5d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__7_value),((lean_object*)&l_term_x25_x5b___x7c___x5d___closed__7_value)}};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__8 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__8_value;
static const lean_ctor_object l_term_x25_x5b___x7c___x5d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__3_value),((lean_object*)&l_term_x25_x5b___x7c___x5d___closed__3_value),((lean_object*)&l_term_x25_x5b___x7c___x5d___closed__8_value)}};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__9 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__9_value;
static const lean_ctor_object l_term_x25_x5b___x7c___x5d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__3_value),((lean_object*)&l_term_x25_x5b___x7c___x5d___closed__9_value),((lean_object*)&l_term_x5b___x5d___closed__18_value)}};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__10 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__10_value;
static const lean_ctor_object l_term_x25_x5b___x7c___x5d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_term_x25_x5b___x7c___x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_term_x25_x5b___x7c___x5d___closed__10_value)}};
static const lean_object* l_term_x25_x5b___x7c___x5d___closed__11 = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__11_value;
LEAN_EXPORT const lean_object* l_term_x25_x5b___x7c___x5d = (const lean_object*)&l_term_x25_x5b___x7c___x5d___closed__11_value;
static const lean_string_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0_value;
static const lean_string_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1_value;
static const lean_string_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2_value;
static const lean_string_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3_value;
static const lean_ctor_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value;
static const lean_string_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "List.cons"};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5_value;
static lean_once_cell_t l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6;
static const lean_string_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value;
static const lean_string_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8_value;
static const lean_ctor_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value;
static const lean_ctor_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10_value;
static const lean_ctor_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value)}};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11_value;
static const lean_ctor_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12_value;
static const lean_ctor_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10_value),((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12_value)}};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13_value;
static const lean_string_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14_value;
static const lean_ctor_object l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15 = (const lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0;
static const lean_string_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "List.nil"};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2_value;
static lean_once_cell_t l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3;
static const lean_string_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value;
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value_aux_0),((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value;
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value;
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value)}};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value;
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8_value;
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value),((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8_value)}};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5));
v___x_91_ = l_String_toRawSubstring_x27(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(lean_object* v_elems_111_, lean_object* v_i_112_, uint8_t v_skip_113_, lean_object* v_result_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_zero_117_; uint8_t v_isZero_118_; 
v_zero_117_ = lean_unsigned_to_nat(0u);
v_isZero_118_ = lean_nat_dec_eq(v_i_112_, v_zero_117_);
if (v_isZero_118_ == 1)
{
lean_object* v___x_119_; 
lean_dec(v_i_112_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_result_114_);
lean_ctor_set(v___x_119_, 1, v_a_116_);
return v___x_119_;
}
else
{
lean_object* v_one_120_; lean_object* v_n_121_; 
v_one_120_ = lean_unsigned_to_nat(1u);
v_n_121_ = lean_nat_sub(v_i_112_, v_one_120_);
lean_dec(v_i_112_);
if (v_skip_113_ == 0)
{
lean_object* v_quotContext_122_; lean_object* v_currMacroScope_123_; lean_object* v_ref_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_quotContext_122_ = lean_ctor_get(v_a_115_, 1);
v_currMacroScope_123_ = lean_ctor_get(v_a_115_, 2);
v_ref_124_ = lean_ctor_get(v_a_115_, 5);
v___x_125_ = lean_box(0);
v___x_126_ = l_Lean_SourceInfo_fromRef(v_ref_124_, v_skip_113_);
v___x_127_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4));
v___x_128_ = lean_obj_once(&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6, &l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6_once, _init_l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6);
v___x_129_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9));
lean_inc(v_currMacroScope_123_);
lean_inc(v_quotContext_122_);
v___x_130_ = l_Lean_addMacroScope(v_quotContext_122_, v___x_129_, v_currMacroScope_123_);
v___x_131_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13));
lean_inc_n(v___x_126_, 2);
v___x_132_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_132_, 0, v___x_126_);
lean_ctor_set(v___x_132_, 1, v___x_128_);
lean_ctor_set(v___x_132_, 2, v___x_130_);
lean_ctor_set(v___x_132_, 3, v___x_131_);
v___x_133_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15));
v___x_134_ = lean_array_get_borrowed(v___x_125_, v_elems_111_, v_n_121_);
lean_inc(v___x_134_);
v___x_135_ = l_Lean_Syntax_node2(v___x_126_, v___x_133_, v___x_134_, v_result_114_);
v___x_136_ = l_Lean_Syntax_node2(v___x_126_, v___x_127_, v___x_132_, v___x_135_);
v___x_137_ = 1;
v_i_112_ = v_n_121_;
v_skip_113_ = v___x_137_;
v_result_114_ = v___x_136_;
goto _start;
}
else
{
v_i_112_ = v_n_121_;
v_skip_113_ = v_isZero_118_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___boxed(lean_object* v_elems_140_, lean_object* v_i_141_, lean_object* v_skip_142_, lean_object* v_result_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
uint8_t v_skip_boxed_146_; lean_object* v_res_147_; 
v_skip_boxed_146_ = lean_unbox(v_skip_142_);
v_res_147_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(v_elems_140_, v_i_141_, v_skip_boxed_146_, v_result_143_, v_a_144_, v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec_ref(v_elems_140_);
return v_res_147_;
}
}
static lean_object* _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Array_mkArray0(lean_box(0));
return v___x_148_;
}
}
static lean_object* _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2));
v___x_152_ = l_String_toRawSubstring_x27(v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(lean_object* v_x_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l_term_x5b___x5d___closed__1));
lean_inc(v_x_168_);
v___x_172_ = l_Lean_Syntax_isOfKind(v_x_168_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_x_168_);
v___x_173_ = lean_box(1);
v___x_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_a_170_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_elems_177_; lean_object* v_size_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = l_Lean_Syntax_getArg(v_x_168_, v___x_175_);
lean_dec(v_x_168_);
v_elems_177_ = l_Lean_Syntax_getArgs(v___x_176_);
lean_dec(v___x_176_);
v_size_178_ = lean_array_get_size(v_elems_177_);
v___x_179_ = lean_unsigned_to_nat(64u);
v___x_180_ = lean_nat_dec_lt(v_size_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v_quotContext_181_; lean_object* v_currMacroScope_182_; lean_object* v_ref_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_quotContext_181_ = lean_ctor_get(v_a_169_, 1);
v_currMacroScope_182_ = lean_ctor_get(v_a_169_, 2);
v_ref_183_ = lean_ctor_get(v_a_169_, 5);
v___x_184_ = l_Lean_SourceInfo_fromRef(v_ref_183_, v___x_180_);
v___x_185_ = ((lean_object*)(l_term_x25_x5b___x7c___x5d___closed__1));
v___x_186_ = ((lean_object*)(l_term_x25_x5b___x7c___x5d___closed__2));
lean_inc_n(v___x_184_, 5);
v___x_187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_184_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15));
v___x_189_ = lean_obj_once(&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0, &l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0_once, _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0);
v___x_190_ = l_Array_appendCore___redArg(v___x_189_, v_elems_177_);
lean_dec_ref(v_elems_177_);
v___x_191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_184_);
lean_ctor_set(v___x_191_, 1, v___x_188_);
lean_ctor_set(v___x_191_, 2, v___x_190_);
v___x_192_ = ((lean_object*)(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1));
v___x_193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_184_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_obj_once(&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3, &l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_once, _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3);
v___x_195_ = ((lean_object*)(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5));
lean_inc(v_currMacroScope_182_);
lean_inc(v_quotContext_181_);
v___x_196_ = l_Lean_addMacroScope(v_quotContext_181_, v___x_195_, v_currMacroScope_182_);
v___x_197_ = ((lean_object*)(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9));
v___x_198_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_198_, 0, v___x_184_);
lean_ctor_set(v___x_198_, 1, v___x_194_);
lean_ctor_set(v___x_198_, 2, v___x_196_);
lean_ctor_set(v___x_198_, 3, v___x_197_);
v___x_199_ = ((lean_object*)(l_term_x5b___x5d___closed__17));
v___x_200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_184_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = l_Lean_Syntax_node5(v___x_184_, v___x_185_, v___x_187_, v___x_191_, v___x_193_, v___x_198_, v___x_200_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_a_170_);
return v___x_202_;
}
else
{
lean_object* v_quotContext_203_; lean_object* v_currMacroScope_204_; lean_object* v_ref_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; 
v_quotContext_203_ = lean_ctor_get(v_a_169_, 1);
v_currMacroScope_204_ = lean_ctor_get(v_a_169_, 2);
v_ref_205_ = lean_ctor_get(v_a_169_, 5);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_unsigned_to_nat(2u);
v___x_208_ = 0;
v___x_209_ = l_Lean_SourceInfo_fromRef(v_ref_205_, v___x_208_);
v___x_210_ = lean_obj_once(&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3, &l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_once, _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3);
v___x_211_ = ((lean_object*)(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5));
lean_inc(v_currMacroScope_204_);
lean_inc(v_quotContext_203_);
v___x_212_ = l_Lean_addMacroScope(v_quotContext_203_, v___x_211_, v_currMacroScope_204_);
v___x_213_ = ((lean_object*)(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9));
v___x_214_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_214_, 0, v___x_209_);
lean_ctor_set(v___x_214_, 1, v___x_210_);
lean_ctor_set(v___x_214_, 2, v___x_212_);
lean_ctor_set(v___x_214_, 3, v___x_213_);
v___x_215_ = lean_nat_mod(v_size_178_, v___x_207_);
v___x_216_ = lean_nat_dec_eq(v___x_215_, v___x_206_);
lean_dec(v___x_215_);
v___x_217_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(v_elems_177_, v_size_178_, v___x_216_, v___x_214_, v_a_169_, v_a_170_);
lean_dec_ref(v_elems_177_);
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___boxed(lean_object* v_x_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(v_x_218_, v_a_219_, v_a_220_);
lean_dec_ref(v_a_219_);
return v_res_221_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Notation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Notation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Notation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Notation(builtin);
}
#ifdef __cplusplus
}
#endif
