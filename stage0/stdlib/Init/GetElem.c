// Lean compiler output
// Module: Init.GetElem
// Imports: public import Init.Util public import Init.Data.Option.Basic
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
static const lean_string_object l_outOfBounds___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Init.GetElem"};
static const lean_object* l_outOfBounds___redArg___closed__0 = (const lean_object*)&l_outOfBounds___redArg___closed__0_value;
static const lean_string_object l_outOfBounds___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "outOfBounds"};
static const lean_object* l_outOfBounds___redArg___closed__1 = (const lean_object*)&l_outOfBounds___redArg___closed__1_value;
static const lean_string_object l_outOfBounds___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "index out of bounds"};
static const lean_object* l_outOfBounds___redArg___closed__2 = (const lean_object*)&l_outOfBounds___redArg___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_outOfBounds___redArg(lean_object*);
LEAN_EXPORT lean_object* l_outOfBounds(lean_object*, lean_object*);
static const lean_string_object l_term_____x5b___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term__[_]"};
static const lean_object* l_term_____x5b___x5d___closed__0 = (const lean_object*)&l_term_____x5b___x5d___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_term_____x5b___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 146, 84, 128, 183, 70, 246)}};
static const lean_object* l_term_____x5b___x5d___closed__1 = (const lean_object*)&l_term_____x5b___x5d___closed__1_value;
static const lean_string_object l_term_____x5b___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_term_____x5b___x5d___closed__2 = (const lean_object*)&l_term_____x5b___x5d___closed__2_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_term_____x5b___x5d___closed__3 = (const lean_object*)&l_term_____x5b___x5d___closed__3_value;
static const lean_string_object l_term_____x5b___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noWs"};
static const lean_object* l_term_____x5b___x5d___closed__4 = (const lean_object*)&l_term_____x5b___x5d___closed__4_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d___closed__4_value),LEAN_SCALAR_PTR_LITERAL(92, 29, 204, 148, 167, 109, 242, 21)}};
static const lean_object* l_term_____x5b___x5d___closed__5 = (const lean_object*)&l_term_____x5b___x5d___closed__5_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__5_value)}};
static const lean_object* l_term_____x5b___x5d___closed__6 = (const lean_object*)&l_term_____x5b___x5d___closed__6_value;
static const lean_string_object l_term_____x5b___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_term_____x5b___x5d___closed__7 = (const lean_object*)&l_term_____x5b___x5d___closed__7_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__7_value)}};
static const lean_object* l_term_____x5b___x5d___closed__8 = (const lean_object*)&l_term_____x5b___x5d___closed__8_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__3_value),((lean_object*)&l_term_____x5b___x5d___closed__6_value),((lean_object*)&l_term_____x5b___x5d___closed__8_value)}};
static const lean_object* l_term_____x5b___x5d___closed__9 = (const lean_object*)&l_term_____x5b___x5d___closed__9_value;
static const lean_string_object l_term_____x5b___x5d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_term_____x5b___x5d___closed__10 = (const lean_object*)&l_term_____x5b___x5d___closed__10_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d___closed__10_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_term_____x5b___x5d___closed__11 = (const lean_object*)&l_term_____x5b___x5d___closed__11_value;
static const lean_string_object l_term_____x5b___x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_term_____x5b___x5d___closed__12 = (const lean_object*)&l_term_____x5b___x5d___closed__12_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d___closed__12_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_term_____x5b___x5d___closed__13 = (const lean_object*)&l_term_____x5b___x5d___closed__13_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_term_____x5b___x5d___closed__14 = (const lean_object*)&l_term_____x5b___x5d___closed__14_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__11_value),((lean_object*)&l_term_____x5b___x5d___closed__14_value)}};
static const lean_object* l_term_____x5b___x5d___closed__15 = (const lean_object*)&l_term_____x5b___x5d___closed__15_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__3_value),((lean_object*)&l_term_____x5b___x5d___closed__9_value),((lean_object*)&l_term_____x5b___x5d___closed__15_value)}};
static const lean_object* l_term_____x5b___x5d___closed__16 = (const lean_object*)&l_term_____x5b___x5d___closed__16_value;
static const lean_string_object l_term_____x5b___x5d___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_term_____x5b___x5d___closed__17 = (const lean_object*)&l_term_____x5b___x5d___closed__17_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__17_value)}};
static const lean_object* l_term_____x5b___x5d___closed__18 = (const lean_object*)&l_term_____x5b___x5d___closed__18_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__3_value),((lean_object*)&l_term_____x5b___x5d___closed__16_value),((lean_object*)&l_term_____x5b___x5d___closed__18_value)}};
static const lean_object* l_term_____x5b___x5d___closed__19 = (const lean_object*)&l_term_____x5b___x5d___closed__19_value;
static const lean_ctor_object l_term_____x5b___x5d___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d___closed__19_value)}};
static const lean_object* l_term_____x5b___x5d___closed__20 = (const lean_object*)&l_term_____x5b___x5d___closed__20_value;
LEAN_EXPORT const lean_object* l_term_____x5b___x5d = (const lean_object*)&l_term_____x5b___x5d___closed__20_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getElem"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(134, 42, 44, 29, 5, 206, 236, 250)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "GetElem"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(111, 233, 51, 226, 114, 128, 218, 11)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 164, 165, 74, 8, 252, 37, 122)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__12 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__12_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_2),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__16 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__16_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_2),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__19 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__19_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21_value;
static lean_once_cell_t l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__25 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__25_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_2),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__29 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__29_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_2),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__31 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__31_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_2),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__33 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__33_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term_____x5b___x5d_x27___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_]'_"};
static const lean_object* l_term_____x5b___x5d_x27___00__closed__0 = (const lean_object*)&l_term_____x5b___x5d_x27___00__closed__0_value;
static const lean_ctor_object l_term_____x5b___x5d_x27___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d_x27___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 98, 175, 4, 199, 28, 246, 201)}};
static const lean_object* l_term_____x5b___x5d_x27___00__closed__1 = (const lean_object*)&l_term_____x5b___x5d_x27___00__closed__1_value;
static const lean_string_object l_term_____x5b___x5d_x27___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]'"};
static const lean_object* l_term_____x5b___x5d_x27___00__closed__2 = (const lean_object*)&l_term_____x5b___x5d_x27___00__closed__2_value;
static const lean_ctor_object l_term_____x5b___x5d_x27___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_____x5b___x5d_x27___00__closed__2_value)}};
static const lean_object* l_term_____x5b___x5d_x27___00__closed__3 = (const lean_object*)&l_term_____x5b___x5d_x27___00__closed__3_value;
static const lean_ctor_object l_term_____x5b___x5d_x27___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__3_value),((lean_object*)&l_term_____x5b___x5d___closed__16_value),((lean_object*)&l_term_____x5b___x5d_x27___00__closed__3_value)}};
static const lean_object* l_term_____x5b___x5d_x27___00__closed__4 = (const lean_object*)&l_term_____x5b___x5d_x27___00__closed__4_value;
static const lean_ctor_object l_term_____x5b___x5d_x27___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__13_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_term_____x5b___x5d_x27___00__closed__5 = (const lean_object*)&l_term_____x5b___x5d_x27___00__closed__5_value;
static const lean_ctor_object l_term_____x5b___x5d_x27___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__3_value),((lean_object*)&l_term_____x5b___x5d_x27___00__closed__4_value),((lean_object*)&l_term_____x5b___x5d_x27___00__closed__5_value)}};
static const lean_object* l_term_____x5b___x5d_x27___00__closed__6 = (const lean_object*)&l_term_____x5b___x5d_x27___00__closed__6_value;
static const lean_ctor_object l_term_____x5b___x5d_x27___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term_____x5b___x5d_x27___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d_x27___00__closed__6_value)}};
static const lean_object* l_term_____x5b___x5d_x27___00__closed__7 = (const lean_object*)&l_term_____x5b___x5d_x27___00__closed__7_value;
LEAN_EXPORT const lean_object* l_term_____x5b___x5d_x27__ = (const lean_object*)&l_term_____x5b___x5d_x27___00__closed__7_value;
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_decidableGetElem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term_____x5b___x5d___x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_]_\?"};
static const lean_object* l_term_____x5b___x5d___x3f___closed__0 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__0_value;
static const lean_ctor_object l_term_____x5b___x5d___x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d___x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 178, 109, 68, 161, 229, 23, 17)}};
static const lean_object* l_term_____x5b___x5d___x3f___closed__1 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__1_value;
static const lean_string_object l_term_____x5b___x5d___x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_term_____x5b___x5d___x3f___closed__2 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__2_value;
static const lean_ctor_object l_term_____x5b___x5d___x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d___x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_term_____x5b___x5d___x3f___closed__3 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__3_value;
static const lean_ctor_object l_term_____x5b___x5d___x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___x3f___closed__3_value),((lean_object*)&l_term_____x5b___x5d___closed__6_value)}};
static const lean_object* l_term_____x5b___x5d___x3f___closed__4 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__4_value;
static const lean_ctor_object l_term_____x5b___x5d___x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__3_value),((lean_object*)&l_term_____x5b___x5d___x3f___closed__4_value),((lean_object*)&l_term_____x5b___x5d___closed__8_value)}};
static const lean_object* l_term_____x5b___x5d___x3f___closed__5 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__5_value;
static const lean_ctor_object l_term_____x5b___x5d___x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__3_value),((lean_object*)&l_term_____x5b___x5d___x3f___closed__5_value),((lean_object*)&l_term_____x5b___x5d___closed__14_value)}};
static const lean_object* l_term_____x5b___x5d___x3f___closed__6 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__6_value;
static const lean_ctor_object l_term_____x5b___x5d___x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__3_value),((lean_object*)&l_term_____x5b___x5d___x3f___closed__6_value),((lean_object*)&l_term_____x5b___x5d___closed__18_value)}};
static const lean_object* l_term_____x5b___x5d___x3f___closed__7 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__7_value;
static const lean_ctor_object l_term_____x5b___x5d___x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__3_value),((lean_object*)&l_term_____x5b___x5d___x3f___closed__7_value),((lean_object*)&l_term_____x5b___x5d___x3f___closed__4_value)}};
static const lean_object* l_term_____x5b___x5d___x3f___closed__8 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__8_value;
static const lean_string_object l_term_____x5b___x5d___x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_term_____x5b___x5d___x3f___closed__9 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__9_value;
static const lean_ctor_object l_term_____x5b___x5d___x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___x3f___closed__9_value)}};
static const lean_object* l_term_____x5b___x5d___x3f___closed__10 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__10_value;
static const lean_ctor_object l_term_____x5b___x5d___x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__3_value),((lean_object*)&l_term_____x5b___x5d___x3f___closed__8_value),((lean_object*)&l_term_____x5b___x5d___x3f___closed__10_value)}};
static const lean_object* l_term_____x5b___x5d___x3f___closed__11 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__11_value;
static const lean_ctor_object l_term_____x5b___x5d___x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___x3f___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d___x3f___closed__11_value)}};
static const lean_object* l_term_____x5b___x5d___x3f___closed__12 = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__12_value;
LEAN_EXPORT const lean_object* l_term_____x5b___x5d___x3f = (const lean_object*)&l_term_____x5b___x5d___x3f___closed__12_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "getElem\?"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value;
static lean_once_cell_t l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 221, 90, 49, 49, 121, 142, 170)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "GetElem\?"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(76, 182, 194, 21, 171, 76, 210, 17)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 183, 124, 210, 168, 65, 205)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term_____x5b___x5d___x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_]_!"};
static const lean_object* l_term_____x5b___x5d___x21___closed__0 = (const lean_object*)&l_term_____x5b___x5d___x21___closed__0_value;
static const lean_ctor_object l_term_____x5b___x5d___x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d___x21___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 145, 92, 47, 59, 8, 18, 13)}};
static const lean_object* l_term_____x5b___x5d___x21___closed__1 = (const lean_object*)&l_term_____x5b___x5d___x21___closed__1_value;
static const lean_string_object l_term_____x5b___x5d___x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l_term_____x5b___x5d___x21___closed__2 = (const lean_object*)&l_term_____x5b___x5d___x21___closed__2_value;
static const lean_ctor_object l_term_____x5b___x5d___x21___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___x21___closed__2_value)}};
static const lean_object* l_term_____x5b___x5d___x21___closed__3 = (const lean_object*)&l_term_____x5b___x5d___x21___closed__3_value;
static const lean_ctor_object l_term_____x5b___x5d___x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___closed__3_value),((lean_object*)&l_term_____x5b___x5d___x3f___closed__8_value),((lean_object*)&l_term_____x5b___x5d___x21___closed__3_value)}};
static const lean_object* l_term_____x5b___x5d___x21___closed__4 = (const lean_object*)&l_term_____x5b___x5d___x21___closed__4_value;
static const lean_ctor_object l_term_____x5b___x5d___x21___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term_____x5b___x5d___x21___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_____x5b___x5d___x21___closed__4_value)}};
static const lean_object* l_term_____x5b___x5d___x21___closed__5 = (const lean_object*)&l_term_____x5b___x5d___x21___closed__5_value;
LEAN_EXPORT const lean_object* l_term_____x5b___x5d___x21 = (const lean_object*)&l_term_____x5b___x5d___x21___closed__5_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "getElem!"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value;
static lean_once_cell_t l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 78, 92, 164, 205, 1, 45, 205)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(76, 182, 194, 21, 171, 76, 210, 17)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 107, 135, 132, 224, 239, 185, 227)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4_value;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5_value;
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "intros"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_2),((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 175, 18, 116, 252, 50, 128, 45)}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__10 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__10_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_2),((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__15 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__15_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_2),((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__15_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_2),((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__21 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__21_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_2),((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__21_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__34 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__34_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_2),((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__34_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_2),((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value),LEAN_SCALAR_PTR_LITERAL(41, 88, 242, 177, 210, 111, 166, 107)}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76;
LEAN_EXPORT lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__0;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__1;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__2;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__3;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__4;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__5;
static const lean_string_object l_LawfulGetElem_getElem_x21__def___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__6 = (const lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__6_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__7;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__8;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__9;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__10;
static const lean_string_object l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "outOfBounds_eq_default"};
static const lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__11 = (const lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__12;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__13;
static const lean_ctor_object l_LawfulGetElem_getElem_x21__def___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value),LEAN_SCALAR_PTR_LITERAL(243, 130, 123, 167, 75, 248, 230, 65)}};
static const lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__14 = (const lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__14_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__15;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__16;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__17;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__18;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__19;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__20;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__21;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__22;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__23;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__24;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__25;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__26;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__27;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__28;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__29;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__30;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__31;
LEAN_EXPORT lean_object* l_LawfulGetElem_getElem_x21__def___autoParam;
LEAN_EXPORT lean_object* l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "tacticGet_elem_tactic_extensible"};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value;
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 80, 20, 121, 148, 193, 237, 106)}};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value;
static const lean_string_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value;
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2),((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value;
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value;
static const lean_string_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value;
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2),((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value;
static const lean_string_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value;
static const lean_string_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value;
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_2),((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value;
static const lean_string_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Fin.val_lt_of_le"};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value;
static lean_once_cell_t l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11;
static const lean_string_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value;
static const lean_string_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "val_lt_of_le"};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value;
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value_aux_0),((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(58, 50, 241, 227, 148, 57, 233, 165)}};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value;
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value;
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value;
static const lean_string_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value;
static const lean_string_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "get_elem_tactic_extensible"};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value;
static const lean_string_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value;
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2),((lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20 = (const lean_object*)&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_instGetElemNatLtLength___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instGetElemNatLtLength___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instGetElemNatLtLength___closed__0 = (const lean_object*)&l_List_instGetElemNatLtLength___closed__0_value;
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_get_x3fInternal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_get_x3fInternal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_get_x3fInternal___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_get_x21Internal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "List.get!Internal"};
static const lean_object* l_List_get_x21Internal___redArg___closed__0 = (const lean_object*)&l_List_get_x21Internal___redArg___closed__0_value;
static const lean_string_object l_List_get_x21Internal___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid index"};
static const lean_object* l_List_get_x21Internal___redArg___closed__1 = (const lean_object*)&l_List_get_x21Internal___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_get_x21Internal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_get_x21Internal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_get_x21Internal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_instGetElem_x3fNatLtLength___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_get_x3fInternal___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instGetElem_x3fNatLtLength___closed__0 = (const lean_object*)&l_List_instGetElem_x3fNatLtLength___closed__0_value;
static const lean_closure_object l_List_instGetElem_x3fNatLtLength___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_get_x21Internal___redArg___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instGetElem_x3fNatLtLength___closed__1 = (const lean_object*)&l_List_instGetElem_x3fNatLtLength___closed__1_value;
static const lean_ctor_object l_List_instGetElem_x3fNatLtLength___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_instGetElemNatLtLength___closed__0_value),((lean_object*)&l_List_instGetElem_x3fNatLtLength___closed__0_value),((lean_object*)&l_List_instGetElem_x3fNatLtLength___closed__1_value)}};
static const lean_object* l_List_instGetElem_x3fNatLtLength___closed__2 = (const lean_object*)&l_List_instGetElem_x3fNatLtLength___closed__2_value;
LEAN_EXPORT lean_object* l_List_instGetElem_x3fNatLtLength(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instGetElemNatLtSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instGetElemNatLtSize___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instGetElemNatLtSize___closed__0 = (const lean_object*)&l_Array_instGetElemNatLtSize___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instGetElem_x3fNatLtSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instGetElem_x3fNatLtSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instGetElem_x3fNatLtSize___closed__0 = (const lean_object*)&l_Array_instGetElem_x3fNatLtSize___closed__0_value;
static const lean_closure_object l_Array_instGetElem_x3fNatLtSize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instGetElem_x3fNatLtSize___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instGetElem_x3fNatLtSize___closed__1 = (const lean_object*)&l_Array_instGetElem_x3fNatLtSize___closed__1_value;
static const lean_ctor_object l_Array_instGetElem_x3fNatLtSize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_instGetElemNatLtSize___closed__0_value),((lean_object*)&l_Array_instGetElem_x3fNatLtSize___closed__0_value),((lean_object*)&l_Array_instGetElem_x3fNatLtSize___closed__1_value)}};
static const lean_object* l_Array_instGetElem_x3fNatLtSize___closed__2 = (const lean_object*)&l_Array_instGetElem_x3fNatLtSize___closed__2_value;
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instGetElemNatTrue___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instGetElemNatTrue___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instGetElemNatTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instGetElemNatTrue___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instGetElemNatTrue___closed__0 = (const lean_object*)&l_Lean_Syntax_instGetElemNatTrue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instGetElemNatTrue = (const lean_object*)&l_Lean_Syntax_instGetElemNatTrue___closed__0_value;
LEAN_EXPORT lean_object* l_outOfBounds___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = ((lean_object*)(l_outOfBounds___redArg___closed__0));
x_3 = ((lean_object*)(l_outOfBounds___redArg___closed__1));
x_4 = lean_unsigned_to_nat(18u);
x_5 = lean_unsigned_to_nat(2u);
x_6 = ((lean_object*)(l_outOfBounds___redArg___closed__2));
x_7 = l_mkPanicMessageWithDecl(x_2, x_3, x_4, x_5, x_6);
x_8 = l_panic___redArg(x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_outOfBounds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_outOfBounds___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_term_____x5b___x5d___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_10, x_15);
lean_dec(x_10);
x_17 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
x_18 = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6);
x_19 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7));
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_addMacroScope(x_8, x_19, x_9);
x_21 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11));
lean_inc(x_16);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
x_24 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15));
x_25 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17));
x_26 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18));
lean_inc(x_16);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
x_28 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20));
x_29 = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22);
x_30 = lean_box(0);
x_31 = l_Lean_addMacroScope(x_8, x_30, x_9);
x_32 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24));
lean_inc(x_16);
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_32);
lean_inc(x_16);
x_34 = l_Lean_Syntax_node1(x_16, x_28, x_33);
lean_inc(x_16);
x_35 = l_Lean_Syntax_node2(x_16, x_25, x_27, x_34);
x_36 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26));
x_37 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27));
lean_inc(x_16);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_16);
lean_ctor_set(x_38, 1, x_37);
x_39 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
x_40 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
x_41 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34));
x_42 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35));
lean_inc(x_16);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_16);
x_44 = l_Lean_Syntax_node1(x_16, x_41, x_43);
lean_inc(x_16);
x_45 = l_Lean_Syntax_node1(x_16, x_23, x_44);
lean_inc(x_16);
x_46 = l_Lean_Syntax_node1(x_16, x_40, x_45);
lean_inc(x_16);
x_47 = l_Lean_Syntax_node1(x_16, x_39, x_46);
lean_inc(x_16);
x_48 = l_Lean_Syntax_node2(x_16, x_36, x_38, x_47);
x_49 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36));
lean_inc(x_16);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_16);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_16);
x_51 = l_Lean_Syntax_node3(x_16, x_24, x_35, x_48, x_50);
lean_inc(x_16);
x_52 = l_Lean_Syntax_node3(x_16, x_23, x_12, x_14, x_51);
x_53 = l_Lean_Syntax_node2(x_16, x_17, x_22, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_term_____x5b___x5d_x27___00__closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = 0;
x_18 = l_Lean_SourceInfo_fromRef(x_10, x_17);
lean_dec(x_10);
x_19 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
x_20 = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6);
x_21 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7));
x_22 = l_Lean_addMacroScope(x_8, x_21, x_9);
x_23 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11));
lean_inc(x_18);
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
x_25 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
lean_inc(x_18);
x_26 = l_Lean_Syntax_node3(x_18, x_25, x_12, x_14, x_16);
x_27 = l_Lean_Syntax_node2(x_18, x_19, x_24, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_3(x_1, x_2, x_3, lean_box(0));
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_decidableGetElem_x3f___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_3(x_5, x_6, x_7, lean_box(0));
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
x_10 = l_decidableGetElem_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_term_____x5b___x5d___x3f___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_10, x_15);
lean_dec(x_10);
x_17 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
x_18 = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1);
x_19 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2));
x_20 = l_Lean_addMacroScope(x_8, x_19, x_9);
x_21 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6));
lean_inc(x_16);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
lean_inc(x_16);
x_24 = l_Lean_Syntax_node2(x_16, x_23, x_12, x_14);
x_25 = l_Lean_Syntax_node2(x_16, x_17, x_22, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_term_____x5b___x5d___x21___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_10, x_15);
lean_dec(x_10);
x_17 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
x_18 = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1);
x_19 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2));
x_20 = l_Lean_addMacroScope(x_8, x_19, x_9);
x_21 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5));
lean_inc(x_16);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
lean_inc(x_16);
x_24 = l_Lean_Syntax_node2(x_16, x_23, x_12, x_14);
x_25 = l_Lean_Syntax_node2(x_16, x_17, x_22, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_3(x_2, x_3, x_4, lean_box(0));
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_outOfBounds___redArg(x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
lean_inc_ref(x_3);
x_4 = lean_alloc_closure((void*)(l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1), 4, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_instGetElem_x3fOfGetElemOfDecidable___redArg(x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6);
x_2 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23);
x_2 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_term_____x5b___x5d___closed__7));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37);
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2));
x_3 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38);
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40);
x_2 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_term_____x5b___x5d___closed__17));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49);
x_2 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59);
x_2 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61);
x_2 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69);
x_2 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76);
return x_1;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2));
x_3 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__1, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__1_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__1);
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__2, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__2_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__3, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__3_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3);
x_2 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__4, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__4_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__6));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__7, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__5, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__5_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__8, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__8_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__7, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__11));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__12, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__12_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__12);
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__11));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__14));
x_3 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__13, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__13_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__13);
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__15, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__15_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__16, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__16_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16);
x_2 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__17, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__17_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__10, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__10);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__18, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__18_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__19, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__19_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__20, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__20_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__21, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__21_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__22, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__22_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__24, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__24_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24);
x_2 = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__25, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__25_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__26, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__26_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__27, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__27_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__28, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__28_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__29, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__29_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29);
x_2 = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__30, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__30_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__30);
x_2 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__31, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__31_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__31);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_instGetElemFinVal(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_alloc_closure((void*)(l_Fin_instGetElem_x3fFinVal___redArg___lam__0), 3, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_alloc_closure((void*)(l_Fin_instGetElem_x3fFinVal___redArg___lam__1), 4, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(x_8, 0, x_3);
lean_ctor_set(x_1, 2, x_7);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_12 = lean_alloc_closure((void*)(l_Fin_instGetElem_x3fFinVal___redArg___lam__0), 3, 1);
lean_closure_set(x_12, 0, x_10);
x_13 = lean_alloc_closure((void*)(l_Fin_instGetElem_x3fFinVal___redArg___lam__1), 4, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_instGetElem_x3fFinVal___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Fin_instGetElem_x3fFinVal(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3));
x_14 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
x_15 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4));
x_16 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18));
lean_inc(x_12);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
x_19 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
x_20 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6));
x_21 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7));
lean_inc(x_12);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8));
x_24 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9));
lean_inc(x_12);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_obj_once(&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11, &l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_once, _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11);
x_27 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14));
x_28 = l_Lean_addMacroScope(x_8, x_27, x_9);
x_29 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16));
lean_inc(x_12);
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_29);
lean_inc(x_12);
x_31 = l_Lean_Syntax_node2(x_12, x_24, x_25, x_30);
lean_inc(x_12);
x_32 = l_Lean_Syntax_node1(x_12, x_14, x_31);
lean_inc(x_12);
x_33 = l_Lean_Syntax_node1(x_12, x_19, x_32);
lean_inc(x_12);
x_34 = l_Lean_Syntax_node1(x_12, x_18, x_33);
lean_inc(x_12);
x_35 = l_Lean_Syntax_node2(x_12, x_20, x_22, x_34);
lean_inc(x_12);
x_36 = l_Lean_Syntax_node1(x_12, x_14, x_35);
lean_inc(x_12);
x_37 = l_Lean_Syntax_node1(x_12, x_19, x_36);
lean_inc(x_12);
x_38 = l_Lean_Syntax_node1(x_12, x_18, x_37);
x_39 = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36));
lean_inc(x_12);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_12);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_12);
x_41 = l_Lean_Syntax_node3(x_12, x_15, x_17, x_38, x_40);
x_42 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17));
lean_inc(x_12);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_42);
x_44 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18));
lean_inc(x_12);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_12);
x_46 = l_Lean_Syntax_node1(x_12, x_4, x_45);
x_47 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19));
x_48 = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20));
lean_inc(x_12);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_47);
lean_inc(x_12);
x_50 = l_Lean_Syntax_node1(x_12, x_48, x_49);
lean_inc_ref(x_43);
lean_inc(x_12);
x_51 = l_Lean_Syntax_node5(x_12, x_14, x_41, x_43, x_46, x_43, x_50);
x_52 = l_Lean_Syntax_node1(x_12, x_13, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
return x_53;
}
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_get___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_instGetElemNatLtLength___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_List_instGetElemNatLtLength___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_object* x_7; 
lean_dec(x_2);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_1 = x_4;
x_2 = x_9;
goto _start;
}
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_get_x3fInternal___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_get_x3fInternal___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_get_x3fInternal(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 1)
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_2 = x_5;
x_3 = x_9;
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_11 = ((lean_object*)(l_outOfBounds___redArg___closed__0));
x_12 = ((lean_object*)(l_List_get_x21Internal___redArg___closed__0));
x_13 = lean_unsigned_to_nat(335u);
x_14 = lean_unsigned_to_nat(18u);
x_15 = ((lean_object*)(l_List_get_x21Internal___redArg___closed__1));
x_16 = l_mkPanicMessageWithDecl(x_11, x_12, x_13, x_14, x_15);
x_17 = l_panic___redArg(x_1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_get_x21Internal___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_get_x21Internal___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_get_x21Internal(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instGetElem_x3fNatLtLength(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_List_instGetElem_x3fNatLtLength___closed__2));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_fget_borrowed(x_1, x_2);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_instGetElemNatLtSize___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Array_instGetElemNatLtSize___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_instGetElem_x3fNatLtSize___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_get_borrowed(x_1, x_2, x_3);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_instGetElem_x3fNatLtSize___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Array_instGetElem_x3fNatLtSize___closed__2));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instGetElemNatTrue___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instGetElemNatTrue___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_instGetElemNatTrue___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_Util(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GetElem(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_LawfulGetElem_getElem_x3f__def___autoParam = _init_l_LawfulGetElem_getElem_x3f__def___autoParam();
lean_mark_persistent(l_LawfulGetElem_getElem_x3f__def___autoParam);
l_LawfulGetElem_getElem_x21__def___autoParam = _init_l_LawfulGetElem_getElem_x21__def___autoParam();
lean_mark_persistent(l_LawfulGetElem_getElem_x21__def___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
