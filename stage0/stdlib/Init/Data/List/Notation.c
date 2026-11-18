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
lean_object* l_Array_mkArray0___redArg();
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_appendCore___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_listTreeLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "listTreeLit"};
static const lean_object* l_listTreeLit___closed__0 = (const lean_object*)&l_listTreeLit___closed__0_value;
static const lean_ctor_object l_listTreeLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_listTreeLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 194, 89, 43, 254, 92, 144, 135)}};
static const lean_object* l_listTreeLit___closed__1 = (const lean_object*)&l_listTreeLit___closed__1_value;
static const lean_string_object l_listTreeLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "%["};
static const lean_object* l_listTreeLit___closed__2 = (const lean_object*)&l_listTreeLit___closed__2_value;
static const lean_ctor_object l_listTreeLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_listTreeLit___closed__2_value)}};
static const lean_object* l_listTreeLit___closed__3 = (const lean_object*)&l_listTreeLit___closed__3_value;
static const lean_ctor_object l_listTreeLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__3_value),((lean_object*)&l_listTreeLit___closed__3_value),((lean_object*)&l_term_x5b___x5d___closed__15_value)}};
static const lean_object* l_listTreeLit___closed__4 = (const lean_object*)&l_listTreeLit___closed__4_value;
static const lean_ctor_object l_listTreeLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_x5b___x5d___closed__3_value),((lean_object*)&l_listTreeLit___closed__4_value),((lean_object*)&l_term_x5b___x5d___closed__18_value)}};
static const lean_object* l_listTreeLit___closed__5 = (const lean_object*)&l_listTreeLit___closed__5_value;
static const lean_ctor_object l_listTreeLit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_listTreeLit___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_listTreeLit___closed__5_value)}};
static const lean_object* l_listTreeLit___closed__6 = (const lean_object*)&l_listTreeLit___closed__6_value;
LEAN_EXPORT const lean_object* l_listTreeLit = (const lean_object*)&l_listTreeLit___closed__6_value;
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
static const lean_string_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "List.nil"};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1_value;
static lean_once_cell_t l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2;
static const lean_string_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_value;
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value_aux_0),((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value;
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value;
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value)}};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value;
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value;
static const lean_ctor_object l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value),((lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value)}};
static const lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8 = (const lean_object*)&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5));
v___x_77_ = l_String_toRawSubstring_x27(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(lean_object* v_elems_97_, lean_object* v_i_98_, uint8_t v_skip_99_, lean_object* v_result_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_zero_103_; uint8_t v_isZero_104_; 
v_zero_103_ = lean_unsigned_to_nat(0u);
v_isZero_104_ = lean_nat_dec_eq(v_i_98_, v_zero_103_);
if (v_isZero_104_ == 1)
{
lean_object* v___x_105_; 
lean_dec(v_i_98_);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v_result_100_);
lean_ctor_set(v___x_105_, 1, v_a_102_);
return v___x_105_;
}
else
{
lean_object* v_one_106_; lean_object* v_n_107_; 
v_one_106_ = lean_unsigned_to_nat(1u);
v_n_107_ = lean_nat_sub(v_i_98_, v_one_106_);
lean_dec(v_i_98_);
if (v_skip_99_ == 0)
{
lean_object* v_quotContext_108_; lean_object* v_currMacroScope_109_; lean_object* v_ref_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_quotContext_108_ = lean_ctor_get(v_a_101_, 1);
v_currMacroScope_109_ = lean_ctor_get(v_a_101_, 2);
v_ref_110_ = lean_ctor_get(v_a_101_, 5);
v___x_111_ = lean_box(0);
v___x_112_ = l_Lean_SourceInfo_fromRef(v_ref_110_, v_skip_99_);
v___x_113_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4));
v___x_114_ = lean_obj_once(&l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6, &l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6_once, _init_l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6);
v___x_115_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9));
lean_inc(v_currMacroScope_109_);
lean_inc(v_quotContext_108_);
v___x_116_ = l_Lean_addMacroScope(v_quotContext_108_, v___x_115_, v_currMacroScope_109_);
v___x_117_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13));
lean_inc_n(v___x_112_, 2);
v___x_118_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_118_, 0, v___x_112_);
lean_ctor_set(v___x_118_, 1, v___x_114_);
lean_ctor_set(v___x_118_, 2, v___x_116_);
lean_ctor_set(v___x_118_, 3, v___x_117_);
v___x_119_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15));
v___x_120_ = lean_array_get_borrowed(v___x_111_, v_elems_97_, v_n_107_);
lean_inc(v___x_120_);
v___x_121_ = l_Lean_Syntax_node2(v___x_112_, v___x_119_, v___x_120_, v_result_100_);
v___x_122_ = l_Lean_Syntax_node2(v___x_112_, v___x_113_, v___x_118_, v___x_121_);
v___x_123_ = 1;
v_i_98_ = v_n_107_;
v_skip_99_ = v___x_123_;
v_result_100_ = v___x_122_;
goto _start;
}
else
{
v_i_98_ = v_n_107_;
v_skip_99_ = v_isZero_104_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___boxed(lean_object* v_elems_126_, lean_object* v_i_127_, lean_object* v_skip_128_, lean_object* v_result_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
uint8_t v_skip_boxed_132_; lean_object* v_res_133_; 
v_skip_boxed_132_ = lean_unbox(v_skip_128_);
v_res_133_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(v_elems_126_, v_i_127_, v_skip_boxed_132_, v_result_129_, v_a_130_, v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec_ref(v_elems_126_);
return v_res_133_;
}
}
static lean_object* _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0(void){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Array_mkArray0___redArg();
return v___x_134_;
}
}
static lean_object* _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1));
v___x_137_ = l_String_toRawSubstring_x27(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(lean_object* v_x_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = ((lean_object*)(l_term_x5b___x5d___closed__1));
lean_inc(v_x_153_);
v___x_157_ = l_Lean_Syntax_isOfKind(v_x_153_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec(v_x_153_);
v___x_158_ = lean_box(1);
v___x_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v_a_155_);
return v___x_159_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v_elems_162_; lean_object* v_size_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = l_Lean_Syntax_getArg(v_x_153_, v___x_160_);
lean_dec(v_x_153_);
v_elems_162_ = l_Lean_Syntax_getArgs(v___x_161_);
lean_dec(v___x_161_);
v_size_163_ = lean_array_get_size(v_elems_162_);
v___x_164_ = lean_unsigned_to_nat(64u);
v___x_165_ = lean_nat_dec_lt(v_size_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v_ref_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_ref_166_ = lean_ctor_get(v_a_154_, 5);
v___x_167_ = l_Lean_SourceInfo_fromRef(v_ref_166_, v___x_165_);
v___x_168_ = ((lean_object*)(l_listTreeLit___closed__1));
v___x_169_ = ((lean_object*)(l_listTreeLit___closed__2));
lean_inc_n(v___x_167_, 3);
v___x_170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_167_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = ((lean_object*)(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15));
v___x_172_ = lean_obj_once(&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0, &l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0_once, _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0);
v___x_173_ = l_Array_appendCore___redArg(v___x_172_, v_elems_162_);
lean_dec_ref(v_elems_162_);
v___x_174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_174_, 0, v___x_167_);
lean_ctor_set(v___x_174_, 1, v___x_171_);
lean_ctor_set(v___x_174_, 2, v___x_173_);
v___x_175_ = ((lean_object*)(l_term_x5b___x5d___closed__17));
v___x_176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_167_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = l_Lean_Syntax_node3(v___x_167_, v___x_168_, v___x_170_, v___x_174_, v___x_176_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v_a_155_);
return v___x_178_;
}
else
{
lean_object* v_quotContext_179_; lean_object* v_currMacroScope_180_; lean_object* v_ref_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; 
v_quotContext_179_ = lean_ctor_get(v_a_154_, 1);
v_currMacroScope_180_ = lean_ctor_get(v_a_154_, 2);
v_ref_181_ = lean_ctor_get(v_a_154_, 5);
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_unsigned_to_nat(2u);
v___x_184_ = 0;
v___x_185_ = l_Lean_SourceInfo_fromRef(v_ref_181_, v___x_184_);
v___x_186_ = lean_obj_once(&l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2, &l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2_once, _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2);
v___x_187_ = ((lean_object*)(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4));
lean_inc(v_currMacroScope_180_);
lean_inc(v_quotContext_179_);
v___x_188_ = l_Lean_addMacroScope(v_quotContext_179_, v___x_187_, v_currMacroScope_180_);
v___x_189_ = ((lean_object*)(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8));
v___x_190_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_190_, 0, v___x_185_);
lean_ctor_set(v___x_190_, 1, v___x_186_);
lean_ctor_set(v___x_190_, 2, v___x_188_);
lean_ctor_set(v___x_190_, 3, v___x_189_);
v___x_191_ = lean_nat_mod(v_size_163_, v___x_183_);
v___x_192_ = lean_nat_dec_eq(v___x_191_, v___x_182_);
lean_dec(v___x_191_);
v___x_193_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(v_elems_162_, v_size_163_, v___x_192_, v___x_190_, v_a_154_, v_a_155_);
lean_dec_ref(v_elems_162_);
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___boxed(lean_object* v_x_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(v_x_194_, v_a_195_, v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_197_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Notation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
