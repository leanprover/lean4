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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_outOfBounds___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Init.GetElem"};
static const lean_object* l_outOfBounds___redArg___closed__0 = (const lean_object*)&l_outOfBounds___redArg___closed__0_value;
static const lean_string_object l_outOfBounds___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "outOfBounds"};
static const lean_object* l_outOfBounds___redArg___closed__1 = (const lean_object*)&l_outOfBounds___redArg___closed__1_value;
static const lean_string_object l_outOfBounds___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "index out of bounds"};
static const lean_object* l_outOfBounds___redArg___closed__2 = (const lean_object*)&l_outOfBounds___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_outOfBounds___redArg(lean_object*);
LEAN_EXPORT lean_object* l_outOfBounds(lean_object*, lean_object*);
static const lean_string_object l_term_____x5b___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term__[_]"};
static const lean_object* l_term_____x5b___x5d___closed__0 = (const lean_object*)&l_term_____x5b___x5d___closed__0_value;
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
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getElem"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value;
static lean_once_cell_t l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6;
static const lean_ctor_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(134, 42, 44, 29, 5, 206, 236, 250)}};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7_value;
static const lean_string_object l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "GetElem"};
static const lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8 = (const lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8_value;
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
static const lean_array_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_value;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "intros"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_2),((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 175, 18, 116, 252, 50, 128, 45)}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4;
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13_value),((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_value)}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_value;
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
LEAN_EXPORT lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_instGetElemNatLtLength___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instGetElemNatLtLength___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instGetElemNatLtLength___closed__0 = (const lean_object*)&l_List_instGetElemNatLtLength___closed__0_value;
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength(lean_object*);
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
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instGetElemNatLtSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instGetElemNatLtSize___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instGetElemNatLtSize___closed__0 = (const lean_object*)&l_Array_instGetElemNatLtSize___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize(lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_outOfBounds___redArg(lean_object* v_inst_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_5_ = ((lean_object*)(l_outOfBounds___redArg___closed__0));
v___x_6_ = ((lean_object*)(l_outOfBounds___redArg___closed__1));
v___x_7_ = lean_unsigned_to_nat(18u);
v___x_8_ = lean_unsigned_to_nat(2u);
v___x_9_ = ((lean_object*)(l_outOfBounds___redArg___closed__2));
v___x_10_ = l_mkPanicMessageWithDecl(v___x_5_, v___x_6_, v___x_7_, v___x_8_, v___x_9_);
v___x_11_ = l_panic___redArg(v_inst_4_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_outOfBounds(lean_object* v_00_u03b1_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_outOfBounds___redArg(v_inst_13_);
return v___x_14_;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5));
v___x_73_ = l_String_toRawSubstring_x27(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21));
v___x_107_ = l_String_toRawSubstring_x27(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1(lean_object* v_x_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = ((lean_object*)(l_term_____x5b___x5d___closed__1));
lean_inc(v_x_138_);
v___x_142_ = l_Lean_Syntax_isOfKind(v_x_138_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec_ref(v_a_139_);
lean_dec(v_x_138_);
v___x_143_ = lean_box(1);
v___x_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_a_140_);
return v___x_144_;
}
else
{
lean_object* v_quotContext_145_; lean_object* v_currMacroScope_146_; lean_object* v_ref_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_quotContext_145_ = lean_ctor_get(v_a_139_, 1);
lean_inc(v_quotContext_145_);
v_currMacroScope_146_ = lean_ctor_get(v_a_139_, 2);
lean_inc(v_currMacroScope_146_);
v_ref_147_ = lean_ctor_get(v_a_139_, 5);
lean_inc(v_ref_147_);
lean_dec_ref(v_a_139_);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = l_Lean_Syntax_getArg(v_x_138_, v___x_148_);
v___x_150_ = lean_unsigned_to_nat(2u);
v___x_151_ = l_Lean_Syntax_getArg(v_x_138_, v___x_150_);
lean_dec(v_x_138_);
v___x_152_ = 0;
v___x_153_ = l_Lean_SourceInfo_fromRef(v_ref_147_, v___x_152_);
lean_dec(v_ref_147_);
v___x_154_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
v___x_155_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6);
v___x_156_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7));
lean_inc(v_currMacroScope_146_);
lean_inc(v_quotContext_145_);
v___x_157_ = l_Lean_addMacroScope(v_quotContext_145_, v___x_156_, v_currMacroScope_146_);
v___x_158_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11));
lean_inc(v___x_153_);
v___x_159_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_159_, 0, v___x_153_);
lean_ctor_set(v___x_159_, 1, v___x_155_);
lean_ctor_set(v___x_159_, 2, v___x_157_);
lean_ctor_set(v___x_159_, 3, v___x_158_);
v___x_160_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_161_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15));
v___x_162_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17));
v___x_163_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18));
lean_inc(v___x_153_);
v___x_164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_153_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20));
v___x_166_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22);
v___x_167_ = lean_box(0);
v___x_168_ = l_Lean_addMacroScope(v_quotContext_145_, v___x_167_, v_currMacroScope_146_);
v___x_169_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24));
lean_inc(v___x_153_);
v___x_170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_170_, 0, v___x_153_);
lean_ctor_set(v___x_170_, 1, v___x_166_);
lean_ctor_set(v___x_170_, 2, v___x_168_);
lean_ctor_set(v___x_170_, 3, v___x_169_);
lean_inc(v___x_153_);
v___x_171_ = l_Lean_Syntax_node1(v___x_153_, v___x_165_, v___x_170_);
lean_inc(v___x_153_);
v___x_172_ = l_Lean_Syntax_node2(v___x_153_, v___x_162_, v___x_164_, v___x_171_);
v___x_173_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26));
v___x_174_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27));
lean_inc(v___x_153_);
v___x_175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_153_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_177_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_178_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34));
v___x_179_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35));
lean_inc(v___x_153_);
v___x_180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_153_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
lean_inc(v___x_153_);
v___x_181_ = l_Lean_Syntax_node1(v___x_153_, v___x_178_, v___x_180_);
lean_inc(v___x_153_);
v___x_182_ = l_Lean_Syntax_node1(v___x_153_, v___x_160_, v___x_181_);
lean_inc(v___x_153_);
v___x_183_ = l_Lean_Syntax_node1(v___x_153_, v___x_177_, v___x_182_);
lean_inc(v___x_153_);
v___x_184_ = l_Lean_Syntax_node1(v___x_153_, v___x_176_, v___x_183_);
lean_inc(v___x_153_);
v___x_185_ = l_Lean_Syntax_node2(v___x_153_, v___x_173_, v___x_175_, v___x_184_);
v___x_186_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36));
lean_inc(v___x_153_);
v___x_187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_153_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
lean_inc(v___x_153_);
v___x_188_ = l_Lean_Syntax_node3(v___x_153_, v___x_161_, v___x_172_, v___x_185_, v___x_187_);
lean_inc(v___x_153_);
v___x_189_ = l_Lean_Syntax_node3(v___x_153_, v___x_160_, v___x_149_, v___x_151_, v___x_188_);
v___x_190_ = l_Lean_Syntax_node2(v___x_153_, v___x_154_, v___x_159_, v___x_189_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_a_140_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1(lean_object* v_x_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = ((lean_object*)(l_term_____x5b___x5d_x27___00__closed__1));
lean_inc(v_x_215_);
v___x_219_ = l_Lean_Syntax_isOfKind(v_x_215_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec_ref(v_a_216_);
lean_dec(v_x_215_);
v___x_220_ = lean_box(1);
v___x_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v_a_217_);
return v___x_221_;
}
else
{
lean_object* v_quotContext_222_; lean_object* v_currMacroScope_223_; lean_object* v_ref_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_quotContext_222_ = lean_ctor_get(v_a_216_, 1);
lean_inc(v_quotContext_222_);
v_currMacroScope_223_ = lean_ctor_get(v_a_216_, 2);
lean_inc(v_currMacroScope_223_);
v_ref_224_ = lean_ctor_get(v_a_216_, 5);
lean_inc(v_ref_224_);
lean_dec_ref(v_a_216_);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = l_Lean_Syntax_getArg(v_x_215_, v___x_225_);
v___x_227_ = lean_unsigned_to_nat(2u);
v___x_228_ = l_Lean_Syntax_getArg(v_x_215_, v___x_227_);
v___x_229_ = lean_unsigned_to_nat(4u);
v___x_230_ = l_Lean_Syntax_getArg(v_x_215_, v___x_229_);
lean_dec(v_x_215_);
v___x_231_ = 0;
v___x_232_ = l_Lean_SourceInfo_fromRef(v_ref_224_, v___x_231_);
lean_dec(v_ref_224_);
v___x_233_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
v___x_234_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6);
v___x_235_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7));
v___x_236_ = l_Lean_addMacroScope(v_quotContext_222_, v___x_235_, v_currMacroScope_223_);
v___x_237_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11));
lean_inc(v___x_232_);
v___x_238_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_238_, 0, v___x_232_);
lean_ctor_set(v___x_238_, 1, v___x_234_);
lean_ctor_set(v___x_238_, 2, v___x_236_);
lean_ctor_set(v___x_238_, 3, v___x_237_);
v___x_239_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
lean_inc(v___x_232_);
v___x_240_ = l_Lean_Syntax_node3(v___x_232_, v___x_239_, v___x_226_, v___x_228_, v___x_230_);
v___x_241_ = l_Lean_Syntax_node2(v___x_232_, v___x_233_, v___x_238_, v___x_240_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v_a_217_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___redArg(lean_object* v_inst_243_, lean_object* v_xs_244_, lean_object* v_i_245_, uint8_t v_inst_246_){
_start:
{
if (v_inst_246_ == 0)
{
lean_object* v___x_247_; 
lean_dec(v_i_245_);
lean_dec(v_xs_244_);
lean_dec(v_inst_243_);
v___x_247_ = lean_box(0);
return v___x_247_;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_apply_3(v_inst_243_, v_xs_244_, v_i_245_, lean_box(0));
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___redArg___boxed(lean_object* v_inst_250_, lean_object* v_xs_251_, lean_object* v_i_252_, lean_object* v_inst_253_){
_start:
{
uint8_t v_inst_16__boxed_254_; lean_object* v_res_255_; 
v_inst_16__boxed_254_ = lean_unbox(v_inst_253_);
v_res_255_ = l_decidableGetElem_x3f___redArg(v_inst_250_, v_xs_251_, v_i_252_, v_inst_16__boxed_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f(lean_object* v_coll_256_, lean_object* v_idx_257_, lean_object* v_elem_258_, lean_object* v_valid_259_, lean_object* v_inst_260_, lean_object* v_xs_261_, lean_object* v_i_262_, uint8_t v_inst_263_){
_start:
{
if (v_inst_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec(v_i_262_);
lean_dec(v_xs_261_);
lean_dec(v_inst_260_);
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_apply_3(v_inst_260_, v_xs_261_, v_i_262_, lean_box(0));
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___boxed(lean_object* v_coll_267_, lean_object* v_idx_268_, lean_object* v_elem_269_, lean_object* v_valid_270_, lean_object* v_inst_271_, lean_object* v_xs_272_, lean_object* v_i_273_, lean_object* v_inst_274_){
_start:
{
uint8_t v_inst_28__boxed_275_; lean_object* v_res_276_; 
v_inst_28__boxed_275_ = lean_unbox(v_inst_274_);
v_res_276_ = l_decidableGetElem_x3f(v_coll_267_, v_idx_268_, v_elem_269_, v_valid_270_, v_inst_271_, v_xs_272_, v_i_273_, v_inst_28__boxed_275_);
return v_res_276_;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0));
v___x_317_ = l_String_toRawSubstring_x27(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1(lean_object* v_x_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l_term_____x5b___x5d___x3f___closed__1));
lean_inc(v_x_330_);
v___x_334_ = l_Lean_Syntax_isOfKind(v_x_330_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec_ref(v_a_331_);
lean_dec(v_x_330_);
v___x_335_ = lean_box(1);
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_a_332_);
return v___x_336_;
}
else
{
lean_object* v_quotContext_337_; lean_object* v_currMacroScope_338_; lean_object* v_ref_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_quotContext_337_ = lean_ctor_get(v_a_331_, 1);
lean_inc(v_quotContext_337_);
v_currMacroScope_338_ = lean_ctor_get(v_a_331_, 2);
lean_inc(v_currMacroScope_338_);
v_ref_339_ = lean_ctor_get(v_a_331_, 5);
lean_inc(v_ref_339_);
lean_dec_ref(v_a_331_);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = l_Lean_Syntax_getArg(v_x_330_, v___x_340_);
v___x_342_ = lean_unsigned_to_nat(3u);
v___x_343_ = l_Lean_Syntax_getArg(v_x_330_, v___x_342_);
lean_dec(v_x_330_);
v___x_344_ = 0;
v___x_345_ = l_Lean_SourceInfo_fromRef(v_ref_339_, v___x_344_);
lean_dec(v_ref_339_);
v___x_346_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
v___x_347_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1);
v___x_348_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2));
v___x_349_ = l_Lean_addMacroScope(v_quotContext_337_, v___x_348_, v_currMacroScope_338_);
v___x_350_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6));
lean_inc(v___x_345_);
v___x_351_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_351_, 0, v___x_345_);
lean_ctor_set(v___x_351_, 1, v___x_347_);
lean_ctor_set(v___x_351_, 2, v___x_349_);
lean_ctor_set(v___x_351_, 3, v___x_350_);
v___x_352_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
lean_inc(v___x_345_);
v___x_353_ = l_Lean_Syntax_node2(v___x_345_, v___x_352_, v___x_341_, v___x_343_);
v___x_354_ = l_Lean_Syntax_node2(v___x_345_, v___x_346_, v___x_351_, v___x_353_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v_a_332_);
return v___x_355_;
}
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0));
v___x_374_ = l_String_toRawSubstring_x27(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1(lean_object* v_x_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l_term_____x5b___x5d___x21___closed__1));
lean_inc(v_x_386_);
v___x_390_ = l_Lean_Syntax_isOfKind(v_x_386_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec_ref(v_a_387_);
lean_dec(v_x_386_);
v___x_391_ = lean_box(1);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_a_388_);
return v___x_392_;
}
else
{
lean_object* v_quotContext_393_; lean_object* v_currMacroScope_394_; lean_object* v_ref_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_quotContext_393_ = lean_ctor_get(v_a_387_, 1);
lean_inc(v_quotContext_393_);
v_currMacroScope_394_ = lean_ctor_get(v_a_387_, 2);
lean_inc(v_currMacroScope_394_);
v_ref_395_ = lean_ctor_get(v_a_387_, 5);
lean_inc(v_ref_395_);
lean_dec_ref(v_a_387_);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = l_Lean_Syntax_getArg(v_x_386_, v___x_396_);
v___x_398_ = lean_unsigned_to_nat(3u);
v___x_399_ = l_Lean_Syntax_getArg(v_x_386_, v___x_398_);
lean_dec(v_x_386_);
v___x_400_ = 0;
v___x_401_ = l_Lean_SourceInfo_fromRef(v_ref_395_, v___x_400_);
lean_dec(v_ref_395_);
v___x_402_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
v___x_403_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1);
v___x_404_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2));
v___x_405_ = l_Lean_addMacroScope(v_quotContext_393_, v___x_404_, v_currMacroScope_394_);
v___x_406_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5));
lean_inc(v___x_401_);
v___x_407_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_407_, 0, v___x_401_);
lean_ctor_set(v___x_407_, 1, v___x_403_);
lean_ctor_set(v___x_407_, 2, v___x_405_);
lean_ctor_set(v___x_407_, 3, v___x_406_);
v___x_408_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
lean_inc(v___x_401_);
v___x_409_ = l_Lean_Syntax_node2(v___x_401_, v___x_408_, v___x_397_, v___x_399_);
v___x_410_ = l_Lean_Syntax_node2(v___x_401_, v___x_402_, v___x_407_, v___x_409_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_a_388_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0(lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_xs_414_, lean_object* v_i_415_){
_start:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
lean_inc(v_i_415_);
lean_inc(v_xs_414_);
v___x_416_ = lean_apply_2(v_inst_412_, v_xs_414_, v_i_415_);
v___x_417_ = lean_unbox(v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
lean_dec(v_i_415_);
lean_dec(v_xs_414_);
lean_dec(v_inst_413_);
v___x_418_ = lean_box(0);
return v___x_418_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_apply_3(v_inst_413_, v_xs_414_, v_i_415_, lean_box(0));
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(lean_object* v___f_421_, lean_object* v_inst_422_, lean_object* v_xs_423_, lean_object* v_i_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = lean_apply_2(v___f_421_, v_xs_423_, v_i_424_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v___x_426_; 
v___x_426_ = l_outOfBounds___redArg(v_inst_422_);
return v___x_426_;
}
else
{
lean_object* v_val_427_; 
lean_dec(v_inst_422_);
v_val_427_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_val_427_);
lean_dec_ref(v___x_425_);
return v_val_427_;
}
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg(lean_object* v_inst_428_, lean_object* v_inst_429_){
_start:
{
lean_object* v___f_430_; lean_object* v___f_431_; lean_object* v___x_432_; 
lean_inc(v_inst_428_);
v___f_430_ = lean_alloc_closure((void*)(l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_430_, 0, v_inst_429_);
lean_closure_set(v___f_430_, 1, v_inst_428_);
lean_inc_ref(v___f_430_);
v___f_431_ = lean_alloc_closure((void*)(l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1), 4, 1);
lean_closure_set(v___f_431_, 0, v___f_430_);
v___x_432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_432_, 0, v_inst_428_);
lean_ctor_set(v___x_432_, 1, v___f_430_);
lean_ctor_set(v___x_432_, 2, v___f_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable(lean_object* v_coll_433_, lean_object* v_idx_434_, lean_object* v_elem_435_, lean_object* v_valid_436_, lean_object* v_inst_437_, lean_object* v_inst_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_instGetElem_x3fOfGetElemOfDecidable___redArg(v_inst_437_, v_inst_438_);
return v___x_439_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1));
v___x_449_ = l_Lean_mkAtom(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3);
v___x_451_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_452_ = lean_array_push(v___x_451_, v___x_450_);
return v___x_452_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_458_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4);
v___x_459_ = lean_array_push(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_460_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6);
v___x_461_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2));
v___x_462_ = lean_box(2);
v___x_463_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
lean_ctor_set(v___x_463_, 2, v___x_460_);
return v___x_463_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7);
v___x_465_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_466_ = lean_array_push(v___x_465_, v___x_464_);
return v___x_466_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_468_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8);
v___x_469_ = lean_array_push(v___x_468_, v___x_467_);
return v___x_469_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12));
v___x_478_ = l_Lean_mkAtom(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13);
v___x_480_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_481_ = lean_array_push(v___x_480_, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17));
v___x_495_ = l_Lean_mkAtom(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19);
v___x_497_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_498_ = lean_array_push(v___x_497_, v___x_496_);
return v___x_498_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_506_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_507_ = lean_array_push(v___x_506_, v___x_505_);
return v___x_507_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_508_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23);
v___x_509_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22));
v___x_510_ = lean_box(2);
v___x_511_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v___x_509_);
lean_ctor_set(v___x_511_, 2, v___x_508_);
return v___x_511_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24);
v___x_513_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20);
v___x_514_ = lean_array_push(v___x_513_, v___x_512_);
return v___x_514_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_516_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25);
v___x_517_ = lean_array_push(v___x_516_, v___x_515_);
return v___x_517_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27));
v___x_520_ = l_Lean_mkAtom(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28);
v___x_522_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_523_ = lean_array_push(v___x_522_, v___x_521_);
return v___x_523_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29);
v___x_525_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_526_ = lean_box(2);
v___x_527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_525_);
lean_ctor_set(v___x_527_, 2, v___x_524_);
return v___x_527_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30);
v___x_529_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26);
v___x_530_ = lean_array_push(v___x_529_, v___x_528_);
return v___x_530_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l_term_____x5b___x5d___closed__7));
v___x_532_ = l_Lean_mkAtom(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32);
v___x_534_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_535_ = lean_array_push(v___x_534_, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_543_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23);
v___x_544_ = lean_array_push(v___x_543_, v___x_542_);
return v___x_544_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0));
v___x_546_ = lean_string_utf8_byte_size(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_547_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0));
v___x_550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_548_);
lean_ctor_set(v___x_550_, 2, v___x_547_);
return v___x_550_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_551_ = lean_box(0);
v___x_552_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2));
v___x_553_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38);
v___x_554_ = lean_box(2);
v___x_555_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v___x_553_);
lean_ctor_set(v___x_555_, 2, v___x_552_);
lean_ctor_set(v___x_555_, 3, v___x_551_);
return v___x_555_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39);
v___x_557_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
v___x_558_ = lean_array_push(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_559_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40);
v___x_560_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
v___x_561_ = lean_box(2);
v___x_562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
lean_ctor_set(v___x_562_, 2, v___x_559_);
return v___x_562_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41);
v___x_564_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_565_ = lean_array_push(v___x_564_, v___x_563_);
return v___x_565_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_566_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42);
v___x_567_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_568_ = lean_box(2);
v___x_569_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
lean_ctor_set(v___x_569_, 2, v___x_566_);
return v___x_569_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43);
v___x_571_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33);
v___x_572_ = lean_array_push(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_term_____x5b___x5d___closed__17));
v___x_574_ = l_Lean_mkAtom(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45);
v___x_576_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44);
v___x_577_ = lean_array_push(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46);
v___x_579_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_580_ = lean_box(2);
v___x_581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_578_);
return v___x_581_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47);
v___x_583_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31);
v___x_584_ = lean_array_push(v___x_583_, v___x_582_);
return v___x_584_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_586_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48);
v___x_587_ = lean_array_push(v___x_586_, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49);
v___x_589_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18));
v___x_590_ = lean_box(2);
v___x_591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v___x_589_);
lean_ctor_set(v___x_591_, 2, v___x_588_);
return v___x_591_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50);
v___x_593_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_594_ = lean_array_push(v___x_593_, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52));
v___x_597_ = l_Lean_mkAtom(v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53);
v___x_599_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51);
v___x_600_ = lean_array_push(v___x_599_, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55));
v___x_608_ = l_Lean_mkAtom(v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57);
v___x_610_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_611_ = lean_array_push(v___x_610_, v___x_609_);
return v___x_611_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_613_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58);
v___x_614_ = lean_array_push(v___x_613_, v___x_612_);
return v___x_614_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_615_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59);
v___x_616_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56));
v___x_617_ = lean_box(2);
v___x_618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_616_);
lean_ctor_set(v___x_618_, 2, v___x_615_);
return v___x_618_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60);
v___x_620_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54);
v___x_621_ = lean_array_push(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_622_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61);
v___x_623_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16));
v___x_624_ = lean_box(2);
v___x_625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
lean_ctor_set(v___x_625_, 2, v___x_622_);
return v___x_625_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62);
v___x_627_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_628_ = lean_array_push(v___x_627_, v___x_626_);
return v___x_628_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_629_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63);
v___x_630_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_631_ = lean_box(2);
v___x_632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___x_630_);
lean_ctor_set(v___x_632_, 2, v___x_629_);
return v___x_632_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64);
v___x_634_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_635_ = lean_array_push(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_636_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65);
v___x_637_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_638_ = lean_box(2);
v___x_639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_636_);
return v___x_639_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66);
v___x_641_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_642_ = lean_array_push(v___x_641_, v___x_640_);
return v___x_642_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_643_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67);
v___x_644_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_645_ = lean_box(2);
v___x_646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
lean_ctor_set(v___x_646_, 2, v___x_643_);
return v___x_646_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68);
v___x_648_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14);
v___x_649_ = lean_array_push(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_650_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69);
v___x_651_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11));
v___x_652_ = lean_box(2);
v___x_653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
lean_ctor_set(v___x_653_, 2, v___x_650_);
return v___x_653_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_654_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70);
v___x_655_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9);
v___x_656_ = lean_array_push(v___x_655_, v___x_654_);
return v___x_656_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_657_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71);
v___x_658_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_659_ = lean_box(2);
v___x_660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___x_658_);
lean_ctor_set(v___x_660_, 2, v___x_657_);
return v___x_660_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72);
v___x_662_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_663_ = lean_array_push(v___x_662_, v___x_661_);
return v___x_663_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_664_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73);
v___x_665_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_666_ = lean_box(2);
v___x_667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v___x_665_);
lean_ctor_set(v___x_667_, 2, v___x_664_);
return v___x_667_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74);
v___x_669_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_670_ = lean_array_push(v___x_669_, v___x_668_);
return v___x_670_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_671_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75);
v___x_672_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_673_ = lean_box(2);
v___x_674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_672_);
lean_ctor_set(v___x_674_, 2, v___x_671_);
return v___x_674_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam(void){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76);
return v___x_675_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__0(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0));
v___x_677_ = lean_string_utf8_byte_size(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__1(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_678_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__0);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0));
v___x_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
lean_ctor_set(v___x_681_, 2, v___x_678_);
return v___x_681_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_682_ = lean_box(0);
v___x_683_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2));
v___x_684_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__1, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__1_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__1);
v___x_685_ = lean_box(2);
v___x_686_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_684_);
lean_ctor_set(v___x_686_, 2, v___x_683_);
lean_ctor_set(v___x_686_, 3, v___x_682_);
return v___x_686_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__2, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__2_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2);
v___x_688_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
v___x_689_ = lean_array_push(v___x_688_, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__3, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__3_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3);
v___x_691_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
v___x_692_ = lean_box(2);
v___x_693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___x_691_);
lean_ctor_set(v___x_693_, 2, v___x_690_);
return v___x_693_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__5(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__4, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__4_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4);
v___x_695_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_696_ = lean_array_push(v___x_695_, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__6));
v___x_699_ = l_Lean_mkAtom(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__7, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7);
v___x_701_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__5, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__5_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__5);
v___x_702_ = lean_array_push(v___x_701_, v___x_700_);
return v___x_702_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41);
v___x_704_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__8, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__8_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8);
v___x_705_ = lean_array_push(v___x_704_, v___x_703_);
return v___x_705_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__10(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__7, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7);
v___x_707_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9);
v___x_708_ = lean_array_push(v___x_707_, v___x_706_);
return v___x_708_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__12(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__11));
v___x_711_ = lean_string_utf8_byte_size(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__13(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_712_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__12, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__12_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__12);
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__11));
v___x_715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
lean_ctor_set(v___x_715_, 2, v___x_712_);
return v___x_715_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_718_ = lean_box(0);
v___x_719_ = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__14));
v___x_720_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__13, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__13_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__13);
v___x_721_ = lean_box(2);
v___x_722_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_720_);
lean_ctor_set(v___x_722_, 2, v___x_719_);
lean_ctor_set(v___x_722_, 3, v___x_718_);
return v___x_722_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__15, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__15_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15);
v___x_724_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
v___x_725_ = lean_array_push(v___x_724_, v___x_723_);
return v___x_725_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__16, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__16_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16);
v___x_727_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
v___x_728_ = lean_box(2);
v___x_729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
lean_ctor_set(v___x_729_, 2, v___x_726_);
return v___x_729_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__17, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__17_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17);
v___x_731_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__10, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__10);
v___x_732_ = lean_array_push(v___x_731_, v___x_730_);
return v___x_732_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_733_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__18, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__18_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18);
v___x_734_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_735_ = lean_box(2);
v___x_736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___x_734_);
lean_ctor_set(v___x_736_, 2, v___x_733_);
return v___x_736_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__19, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__19_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19);
v___x_738_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33);
v___x_739_ = lean_array_push(v___x_738_, v___x_737_);
return v___x_739_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45);
v___x_741_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__20, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__20_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20);
v___x_742_ = lean_array_push(v___x_741_, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__21, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__21_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21);
v___x_744_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_745_ = lean_box(2);
v___x_746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
lean_ctor_set(v___x_746_, 2, v___x_743_);
return v___x_746_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__22, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__22_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22);
v___x_748_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31);
v___x_749_ = lean_array_push(v___x_748_, v___x_747_);
return v___x_749_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_751_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23);
v___x_752_ = lean_array_push(v___x_751_, v___x_750_);
return v___x_752_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_753_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__24, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__24_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24);
v___x_754_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18));
v___x_755_ = lean_box(2);
v___x_756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_754_);
lean_ctor_set(v___x_756_, 2, v___x_753_);
return v___x_756_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__25, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__25_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25);
v___x_758_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9);
v___x_759_ = lean_array_push(v___x_758_, v___x_757_);
return v___x_759_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_760_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__26, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__26_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26);
v___x_761_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_762_ = lean_box(2);
v___x_763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___x_761_);
lean_ctor_set(v___x_763_, 2, v___x_760_);
return v___x_763_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__27, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__27_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27);
v___x_765_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_766_ = lean_array_push(v___x_765_, v___x_764_);
return v___x_766_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_767_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__28, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__28_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28);
v___x_768_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_769_ = lean_box(2);
v___x_770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_768_);
lean_ctor_set(v___x_770_, 2, v___x_767_);
return v___x_770_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__30(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__29, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__29_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29);
v___x_772_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_773_ = lean_array_push(v___x_772_, v___x_771_);
return v___x_773_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__31(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_774_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__30, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__30_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__30);
v___x_775_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_776_ = lean_box(2);
v___x_777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v___x_775_);
lean_ctor_set(v___x_777_, 2, v___x_774_);
return v___x_777_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam(void){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__31, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__31_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__31);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_779_, lean_object* v_h__1_780_, lean_object* v_h__2_781_){
_start:
{
if (lean_obj_tag(v_x_779_) == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec(v_h__1_780_);
v___x_782_ = lean_box(0);
v___x_783_ = lean_apply_1(v_h__2_781_, v___x_782_);
return v___x_783_;
}
else
{
lean_object* v_val_784_; lean_object* v___x_785_; 
lean_dec(v_h__2_781_);
v_val_784_ = lean_ctor_get(v_x_779_, 0);
lean_inc(v_val_784_);
lean_dec_ref(v_x_779_);
v___x_785_ = lean_apply_1(v_h__1_780_, v_val_784_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_786_, lean_object* v_motive_787_, lean_object* v_x_788_, lean_object* v_h__1_789_, lean_object* v_h__2_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter___redArg(v_x_788_, v_h__1_789_, v_h__2_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___redArg___lam__0(lean_object* v_inst_792_, lean_object* v_xs_793_, lean_object* v_i_794_, lean_object* v_h_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = lean_apply_3(v_inst_792_, v_xs_793_, v_i_794_, lean_box(0));
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___redArg(lean_object* v_inst_797_){
_start:
{
lean_object* v___f_798_; 
v___f_798_ = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(v___f_798_, 0, v_inst_797_);
return v___f_798_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal(lean_object* v_cont_799_, lean_object* v_elem_800_, lean_object* v_dom_801_, lean_object* v_n_802_, lean_object* v_inst_803_){
_start:
{
lean_object* v___f_804_; 
v___f_804_ = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(v___f_804_, 0, v_inst_803_);
return v___f_804_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___boxed(lean_object* v_cont_805_, lean_object* v_elem_806_, lean_object* v_dom_807_, lean_object* v_n_808_, lean_object* v_inst_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Fin_instGetElemFinVal(v_cont_805_, v_elem_806_, v_dom_807_, v_n_808_, v_inst_809_);
lean_dec(v_n_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg___lam__0(lean_object* v_getElem_x3f_811_, lean_object* v_xs_812_, lean_object* v_i_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = lean_apply_2(v_getElem_x3f_811_, v_xs_812_, v_i_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg___lam__1(lean_object* v_getElem_x21_815_, lean_object* v_inst_816_, lean_object* v_xs_817_, lean_object* v_i_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = lean_apply_3(v_getElem_x21_815_, v_inst_816_, v_xs_817_, v_i_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg(lean_object* v_inst_820_){
_start:
{
lean_object* v_toGetElem_821_; lean_object* v_getElem_x3f_822_; lean_object* v_getElem_x21_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_833_; 
v_toGetElem_821_ = lean_ctor_get(v_inst_820_, 0);
v_getElem_x3f_822_ = lean_ctor_get(v_inst_820_, 1);
v_getElem_x21_823_ = lean_ctor_get(v_inst_820_, 2);
v_isSharedCheck_833_ = !lean_is_exclusive(v_inst_820_);
if (v_isSharedCheck_833_ == 0)
{
v___x_825_ = v_inst_820_;
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_getElem_x21_823_);
lean_inc(v_getElem_x3f_822_);
lean_inc(v_toGetElem_821_);
lean_dec(v_inst_820_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___f_827_; lean_object* v___f_828_; lean_object* v___f_829_; lean_object* v___x_831_; 
v___f_827_ = lean_alloc_closure((void*)(l_Fin_instGetElem_x3fFinVal___redArg___lam__0), 3, 1);
lean_closure_set(v___f_827_, 0, v_getElem_x3f_822_);
v___f_828_ = lean_alloc_closure((void*)(l_Fin_instGetElem_x3fFinVal___redArg___lam__1), 4, 1);
lean_closure_set(v___f_828_, 0, v_getElem_x21_823_);
v___f_829_ = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(v___f_829_, 0, v_toGetElem_821_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 2, v___f_828_);
lean_ctor_set(v___x_825_, 1, v___f_827_);
lean_ctor_set(v___x_825_, 0, v___f_829_);
v___x_831_ = v___x_825_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___f_829_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___f_827_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v___f_828_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal(lean_object* v_cont_834_, lean_object* v_elem_835_, lean_object* v_dom_836_, lean_object* v_n_837_, lean_object* v_inst_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Fin_instGetElem_x3fFinVal___redArg(v_inst_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___boxed(lean_object* v_cont_840_, lean_object* v_elem_841_, lean_object* v_dom_842_, lean_object* v_n_843_, lean_object* v_inst_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Fin_instGetElem_x3fFinVal(v_cont_840_, v_elem_841_, v_dom_842_, v_n_843_, v_inst_844_);
lean_dec(v_n_843_);
return v_res_845_;
}
}
static lean_object* _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10));
v___x_875_ = l_String_toRawSubstring_x27(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(lean_object* v_x_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1));
v___x_899_ = l_Lean_Syntax_isOfKind(v_x_895_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec_ref(v_a_896_);
v___x_900_ = lean_box(1);
v___x_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v_a_897_);
return v___x_901_;
}
else
{
lean_object* v_quotContext_902_; lean_object* v_currMacroScope_903_; lean_object* v_ref_904_; uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_quotContext_902_ = lean_ctor_get(v_a_896_, 1);
lean_inc(v_quotContext_902_);
v_currMacroScope_903_ = lean_ctor_get(v_a_896_, 2);
lean_inc(v_currMacroScope_903_);
v_ref_904_ = lean_ctor_get(v_a_896_, 5);
lean_inc(v_ref_904_);
lean_dec_ref(v_a_896_);
v___x_905_ = 0;
v___x_906_ = l_Lean_SourceInfo_fromRef(v_ref_904_, v___x_905_);
lean_dec(v_ref_904_);
v___x_907_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3));
v___x_908_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_909_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4));
v___x_910_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18));
lean_inc(v___x_906_);
v___x_911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_906_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_913_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_914_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6));
v___x_915_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7));
lean_inc(v___x_906_);
v___x_916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_906_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8));
v___x_918_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9));
lean_inc(v___x_906_);
v___x_919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_906_);
lean_ctor_set(v___x_919_, 1, v___x_917_);
v___x_920_ = lean_obj_once(&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11, &l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_once, _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11);
v___x_921_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14));
v___x_922_ = l_Lean_addMacroScope(v_quotContext_902_, v___x_921_, v_currMacroScope_903_);
v___x_923_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16));
lean_inc(v___x_906_);
v___x_924_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_924_, 0, v___x_906_);
lean_ctor_set(v___x_924_, 1, v___x_920_);
lean_ctor_set(v___x_924_, 2, v___x_922_);
lean_ctor_set(v___x_924_, 3, v___x_923_);
lean_inc(v___x_906_);
v___x_925_ = l_Lean_Syntax_node2(v___x_906_, v___x_918_, v___x_919_, v___x_924_);
lean_inc(v___x_906_);
v___x_926_ = l_Lean_Syntax_node1(v___x_906_, v___x_908_, v___x_925_);
lean_inc(v___x_906_);
v___x_927_ = l_Lean_Syntax_node1(v___x_906_, v___x_913_, v___x_926_);
lean_inc(v___x_906_);
v___x_928_ = l_Lean_Syntax_node1(v___x_906_, v___x_912_, v___x_927_);
lean_inc(v___x_906_);
v___x_929_ = l_Lean_Syntax_node2(v___x_906_, v___x_914_, v___x_916_, v___x_928_);
lean_inc(v___x_906_);
v___x_930_ = l_Lean_Syntax_node1(v___x_906_, v___x_908_, v___x_929_);
lean_inc(v___x_906_);
v___x_931_ = l_Lean_Syntax_node1(v___x_906_, v___x_913_, v___x_930_);
lean_inc(v___x_906_);
v___x_932_ = l_Lean_Syntax_node1(v___x_906_, v___x_912_, v___x_931_);
v___x_933_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36));
lean_inc(v___x_906_);
v___x_934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_906_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
lean_inc(v___x_906_);
v___x_935_ = l_Lean_Syntax_node3(v___x_906_, v___x_909_, v___x_911_, v___x_932_, v___x_934_);
v___x_936_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17));
lean_inc(v___x_906_);
v___x_937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_906_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18));
lean_inc(v___x_906_);
v___x_939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_906_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
lean_inc(v___x_906_);
v___x_940_ = l_Lean_Syntax_node1(v___x_906_, v___x_898_, v___x_939_);
v___x_941_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19));
v___x_942_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20));
lean_inc(v___x_906_);
v___x_943_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_906_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
lean_inc(v___x_906_);
v___x_944_ = l_Lean_Syntax_node1(v___x_906_, v___x_942_, v___x_943_);
lean_inc_ref(v___x_937_);
lean_inc(v___x_906_);
v___x_945_ = l_Lean_Syntax_node5(v___x_906_, v___x_908_, v___x_935_, v___x_937_, v___x_940_, v___x_937_, v___x_944_);
v___x_946_ = l_Lean_Syntax_node1(v___x_906_, v___x_907_, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_a_897_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___lam__0(lean_object* v_as_948_, lean_object* v_i_949_, lean_object* v_h_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_List_get___redArg(v_as_948_, v_i_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___lam__0___boxed(lean_object* v_as_952_, lean_object* v_i_953_, lean_object* v_h_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_List_instGetElemNatLtLength___lam__0(v_as_952_, v_i_953_, v_h_954_);
lean_dec(v_as_952_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength(lean_object* v_00_u03b1_957_){
_start:
{
lean_object* v___f_958_; 
v___f_958_ = ((lean_object*)(l_List_instGetElemNatLtLength___closed__0));
return v___f_958_;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___redArg(lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
if (lean_obj_tag(v_x_959_) == 1)
{
lean_object* v_head_961_; lean_object* v_tail_962_; lean_object* v_zero_963_; uint8_t v_isZero_964_; 
v_head_961_ = lean_ctor_get(v_x_959_, 0);
v_tail_962_ = lean_ctor_get(v_x_959_, 1);
v_zero_963_ = lean_unsigned_to_nat(0u);
v_isZero_964_ = lean_nat_dec_eq(v_x_960_, v_zero_963_);
if (v_isZero_964_ == 1)
{
lean_object* v___x_965_; 
lean_dec(v_x_960_);
lean_inc(v_head_961_);
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v_head_961_);
return v___x_965_;
}
else
{
lean_object* v_one_966_; lean_object* v_n_967_; 
v_one_966_ = lean_unsigned_to_nat(1u);
v_n_967_ = lean_nat_sub(v_x_960_, v_one_966_);
lean_dec(v_x_960_);
v_x_959_ = v_tail_962_;
v_x_960_ = v_n_967_;
goto _start;
}
}
else
{
lean_object* v___x_969_; 
lean_dec(v_x_960_);
v___x_969_ = lean_box(0);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___redArg___boxed(lean_object* v_x_970_, lean_object* v_x_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_List_get_x3fInternal___redArg(v_x_970_, v_x_971_);
lean_dec(v_x_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal(lean_object* v_00_u03b1_973_, lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_List_get_x3fInternal___redArg(v_x_974_, v_x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___boxed(lean_object* v_00_u03b1_977_, lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_List_get_x3fInternal(v_00_u03b1_977_, v_x_978_, v_x_979_);
lean_dec(v_x_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___redArg(lean_object* v_inst_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
if (lean_obj_tag(v_x_984_) == 1)
{
lean_object* v_head_986_; lean_object* v_tail_987_; lean_object* v_zero_988_; uint8_t v_isZero_989_; 
v_head_986_ = lean_ctor_get(v_x_984_, 0);
v_tail_987_ = lean_ctor_get(v_x_984_, 1);
v_zero_988_ = lean_unsigned_to_nat(0u);
v_isZero_989_ = lean_nat_dec_eq(v_x_985_, v_zero_988_);
if (v_isZero_989_ == 1)
{
lean_dec(v_x_985_);
lean_dec(v_inst_983_);
lean_inc(v_head_986_);
return v_head_986_;
}
else
{
lean_object* v_one_990_; lean_object* v_n_991_; 
v_one_990_ = lean_unsigned_to_nat(1u);
v_n_991_ = lean_nat_sub(v_x_985_, v_one_990_);
lean_dec(v_x_985_);
v_x_984_ = v_tail_987_;
v_x_985_ = v_n_991_;
goto _start;
}
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v_x_985_);
v___x_993_ = ((lean_object*)(l_outOfBounds___redArg___closed__0));
v___x_994_ = ((lean_object*)(l_List_get_x21Internal___redArg___closed__0));
v___x_995_ = lean_unsigned_to_nat(335u);
v___x_996_ = lean_unsigned_to_nat(18u);
v___x_997_ = ((lean_object*)(l_List_get_x21Internal___redArg___closed__1));
v___x_998_ = l_mkPanicMessageWithDecl(v___x_993_, v___x_994_, v___x_995_, v___x_996_, v___x_997_);
v___x_999_ = l_panic___redArg(v_inst_983_, v___x_998_);
return v___x_999_;
}
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___redArg___boxed(lean_object* v_inst_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_List_get_x21Internal___redArg(v_inst_1000_, v_x_1001_, v_x_1002_);
lean_dec(v_x_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal(lean_object* v_00_u03b1_1004_, lean_object* v_inst_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_List_get_x21Internal___redArg(v_inst_1005_, v_x_1006_, v_x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___boxed(lean_object* v_00_u03b1_1009_, lean_object* v_inst_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_List_get_x21Internal(v_00_u03b1_1009_, v_inst_1010_, v_x_1011_, v_x_1012_);
lean_dec(v_x_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_List_instGetElem_x3fNatLtLength(lean_object* v_00_u03b1_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = ((lean_object*)(l_List_instGetElem_x3fNatLtLength___closed__2));
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___lam__0(lean_object* v_xs_1022_, lean_object* v_i_1023_, lean_object* v_h_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_array_fget_borrowed(v_xs_1022_, v_i_1023_);
lean_inc(v___x_1025_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___lam__0___boxed(lean_object* v_xs_1026_, lean_object* v_i_1027_, lean_object* v_h_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Array_instGetElemNatLtSize___lam__0(v_xs_1026_, v_i_1027_, v_h_1028_);
lean_dec(v_i_1027_);
lean_dec_ref(v_xs_1026_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize(lean_object* v_00_u03b1_1031_){
_start:
{
lean_object* v___f_1032_; 
v___f_1032_ = ((lean_object*)(l_Array_instGetElemNatLtSize___closed__0));
return v___f_1032_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__0(lean_object* v_xs_1033_, lean_object* v_i_1034_){
_start:
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = lean_array_get_size(v_xs_1033_);
v___x_1036_ = lean_nat_dec_lt(v_i_1034_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_array_fget_borrowed(v_xs_1033_, v_i_1034_);
lean_inc(v___x_1038_);
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__0___boxed(lean_object* v_xs_1040_, lean_object* v_i_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Array_instGetElem_x3fNatLtSize___lam__0(v_xs_1040_, v_i_1041_);
lean_dec(v_i_1041_);
lean_dec_ref(v_xs_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__1(lean_object* v_inst_1043_, lean_object* v_xs_1044_, lean_object* v_i_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_array_get_borrowed(v_inst_1043_, v_xs_1044_, v_i_1045_);
lean_inc(v___x_1046_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__1___boxed(lean_object* v_inst_1047_, lean_object* v_xs_1048_, lean_object* v_i_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Array_instGetElem_x3fNatLtSize___lam__1(v_inst_1047_, v_xs_1048_, v_i_1049_);
lean_dec(v_i_1049_);
lean_dec_ref(v_xs_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize(lean_object* v_00_u03b1_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = ((lean_object*)(l_Array_instGetElem_x3fNatLtSize___closed__2));
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instGetElemNatTrue___lam__0(lean_object* v_stx_1059_, lean_object* v_i_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Syntax_getArg(v_stx_1059_, v_i_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instGetElemNatTrue___lam__0___boxed(lean_object* v_stx_1063_, lean_object* v_i_1064_, lean_object* v_x_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Syntax_instGetElemNatTrue___lam__0(v_stx_1063_, v_i_1064_, v_x_1065_);
lean_dec(v_i_1064_);
lean_dec(v_stx_1063_);
return v_res_1066_;
}
}
lean_object* runtime_initialize_Init_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_GetElem(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_GetElem(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_LawfulGetElem_getElem_x3f__def___autoParam = _init_l_LawfulGetElem_getElem_x3f__def___autoParam();
lean_mark_persistent(l_LawfulGetElem_getElem_x3f__def___autoParam);
l_LawfulGetElem_getElem_x21__def___autoParam = _init_l_LawfulGetElem_getElem_x21__def___autoParam();
lean_mark_persistent(l_LawfulGetElem_getElem_x21__def___autoParam);
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_GetElem(builtin);
}
#ifdef __cplusplus
}
#endif
