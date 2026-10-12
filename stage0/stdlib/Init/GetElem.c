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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_outOfBounds___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_outOfBounds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_outOfBounds___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37_value),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38_value;
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
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53;
static const lean_string_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value_aux_0),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value_aux_1),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value_aux_2),((lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54_value),LEAN_SCALAR_PTR_LITERAL(41, 88, 242, 177, 210, 111, 166, 107)}};
static const lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55 = (const lean_object*)&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56;
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
LEAN_EXPORT lean_object* l_LawfulGetElem_getElem_x3f__def___autoParam;
static const lean_ctor_object l_LawfulGetElem_getElem_x21__def___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__0 = (const lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__0_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x21__def___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__0_value),((lean_object*)&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__1 = (const lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__1_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__2;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__3;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__4;
static const lean_string_object l_LawfulGetElem_getElem_x21__def___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__5 = (const lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__5_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__6;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__7;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__8;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__9;
static const lean_string_object l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "outOfBounds_eq_default"};
static const lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__10 = (const lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(22) << 1) | 1))}};
static const lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__11 = (const lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x21__def___autoParam___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(243, 130, 123, 167, 75, 248, 230, 65)}};
static const lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__12 = (const lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__12_value;
static const lean_ctor_object l_LawfulGetElem_getElem_x21__def___autoParam___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value),((lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__13 = (const lean_object*)&l_LawfulGetElem_getElem_x21__def___autoParam___closed__13_value;
static lean_once_cell_t l_LawfulGetElem_getElem_x21__def___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulGetElem_getElem_x21__def___autoParam___closed__14;
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
LEAN_EXPORT lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_instGetElemNatLtLength___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instGetElemNatLtLength___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instGetElemNatLtLength___redArg___closed__0 = (const lean_object*)&l_List_instGetElemNatLtLength___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___redArg();
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___redArg___boxed(lean_object*);
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
static const lean_closure_object l_List_instGetElem_x3fNatLtLength___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_get_x3fInternal___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instGetElem_x3fNatLtLength___redArg___closed__0 = (const lean_object*)&l_List_instGetElem_x3fNatLtLength___redArg___closed__0_value;
static const lean_closure_object l_List_instGetElem_x3fNatLtLength___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_get_x21Internal___redArg___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_instGetElem_x3fNatLtLength___redArg___closed__1 = (const lean_object*)&l_List_instGetElem_x3fNatLtLength___redArg___closed__1_value;
static const lean_ctor_object l_List_instGetElem_x3fNatLtLength___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_instGetElemNatLtLength___redArg___closed__0_value),((lean_object*)&l_List_instGetElem_x3fNatLtLength___redArg___closed__0_value),((lean_object*)&l_List_instGetElem_x3fNatLtLength___redArg___closed__1_value)}};
static const lean_object* l_List_instGetElem_x3fNatLtLength___redArg___closed__2 = (const lean_object*)&l_List_instGetElem_x3fNatLtLength___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_instGetElem_x3fNatLtLength___redArg();
LEAN_EXPORT lean_object* l_List_instGetElem_x3fNatLtLength___redArg___boxed(lean_object*);
static lean_once_cell_t l_List_instGetElem_x3fNatLtLength___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_instGetElem_x3fNatLtLength___closed__0;
LEAN_EXPORT lean_object* l_List_instGetElem_x3fNatLtLength(lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instGetElemNatLtSize___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instGetElemNatLtSize___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instGetElemNatLtSize___redArg___closed__0 = (const lean_object*)&l_Array_instGetElemNatLtSize___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___redArg();
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize(lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_instGetElem_x3fNatLtSize___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instGetElem_x3fNatLtSize___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___closed__0 = (const lean_object*)&l_Array_instGetElem_x3fNatLtSize___redArg___closed__0_value;
static const lean_closure_object l_Array_instGetElem_x3fNatLtSize___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instGetElem_x3fNatLtSize___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___closed__1 = (const lean_object*)&l_Array_instGetElem_x3fNatLtSize___redArg___closed__1_value;
static const lean_ctor_object l_Array_instGetElem_x3fNatLtSize___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_instGetElemNatLtSize___redArg___closed__0_value),((lean_object*)&l_Array_instGetElem_x3fNatLtSize___redArg___closed__0_value),((lean_object*)&l_Array_instGetElem_x3fNatLtSize___redArg___closed__1_value)}};
static const lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___closed__2 = (const lean_object*)&l_Array_instGetElem_x3fNatLtSize___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___redArg();
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___boxed(lean_object*);
static lean_once_cell_t l_Array_instGetElem_x3fNatLtSize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_instGetElem_x3fNatLtSize___closed__0;
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
LEAN_EXPORT lean_object* l_outOfBounds___redArg___boxed(lean_object* v_inst_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_outOfBounds___redArg(v_inst_12_);
lean_dec(v_inst_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_outOfBounds(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_outOfBounds___redArg(v_inst_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_outOfBounds___boxed(lean_object* v_00_u03b1_17_, lean_object* v_inst_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_outOfBounds(v_00_u03b1_17_, v_inst_18_);
lean_dec(v_inst_18_);
return v_res_19_;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5));
v___x_78_ = l_String_toRawSubstring_x27(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21));
v___x_112_ = l_String_toRawSubstring_x27(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1(lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = ((lean_object*)(l_term_____x5b___x5d___closed__1));
lean_inc(v_x_143_);
v___x_147_ = l_Lean_Syntax_isOfKind(v_x_143_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_x_143_);
v___x_148_ = lean_box(1);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_a_145_);
return v___x_149_;
}
else
{
lean_object* v_quotContext_150_; lean_object* v_currMacroScope_151_; lean_object* v_ref_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_quotContext_150_ = lean_ctor_get(v_a_144_, 1);
v_currMacroScope_151_ = lean_ctor_get(v_a_144_, 2);
v_ref_152_ = lean_ctor_get(v_a_144_, 5);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Lean_Syntax_getArg(v_x_143_, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(2u);
v___x_156_ = l_Lean_Syntax_getArg(v_x_143_, v___x_155_);
lean_dec(v_x_143_);
v___x_157_ = 0;
v___x_158_ = l_Lean_SourceInfo_fromRef(v_ref_152_, v___x_157_);
v___x_159_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
v___x_160_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6);
v___x_161_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7));
lean_inc_n(v_currMacroScope_151_, 2);
lean_inc_n(v_quotContext_150_, 2);
v___x_162_ = l_Lean_addMacroScope(v_quotContext_150_, v___x_161_, v_currMacroScope_151_);
v___x_163_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11));
lean_inc_n(v___x_158_, 15);
v___x_164_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_164_, 0, v___x_158_);
lean_ctor_set(v___x_164_, 1, v___x_160_);
lean_ctor_set(v___x_164_, 2, v___x_162_);
lean_ctor_set(v___x_164_, 3, v___x_163_);
v___x_165_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_166_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15));
v___x_167_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17));
v___x_168_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18));
v___x_169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_158_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20));
v___x_171_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22);
v___x_172_ = lean_box(0);
v___x_173_ = l_Lean_addMacroScope(v_quotContext_150_, v___x_172_, v_currMacroScope_151_);
v___x_174_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24));
v___x_175_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_175_, 0, v___x_158_);
lean_ctor_set(v___x_175_, 1, v___x_171_);
lean_ctor_set(v___x_175_, 2, v___x_173_);
lean_ctor_set(v___x_175_, 3, v___x_174_);
v___x_176_ = l_Lean_Syntax_node1(v___x_158_, v___x_170_, v___x_175_);
v___x_177_ = l_Lean_Syntax_node2(v___x_158_, v___x_167_, v___x_169_, v___x_176_);
v___x_178_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26));
v___x_179_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27));
v___x_180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_158_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_182_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_183_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34));
v___x_184_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35));
v___x_185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_158_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = l_Lean_Syntax_node1(v___x_158_, v___x_183_, v___x_185_);
v___x_187_ = l_Lean_Syntax_node1(v___x_158_, v___x_165_, v___x_186_);
v___x_188_ = l_Lean_Syntax_node1(v___x_158_, v___x_182_, v___x_187_);
v___x_189_ = l_Lean_Syntax_node1(v___x_158_, v___x_181_, v___x_188_);
v___x_190_ = l_Lean_Syntax_node2(v___x_158_, v___x_178_, v___x_180_, v___x_189_);
v___x_191_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36));
v___x_192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_158_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = l_Lean_Syntax_node3(v___x_158_, v___x_166_, v___x_177_, v___x_190_, v___x_192_);
v___x_194_ = l_Lean_Syntax_node3(v___x_158_, v___x_165_, v___x_154_, v___x_156_, v___x_193_);
v___x_195_ = l_Lean_Syntax_node2(v___x_158_, v___x_159_, v___x_164_, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_145_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___boxed(lean_object* v_x_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1(v_x_197_, v_a_198_, v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1(lean_object* v_x_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = ((lean_object*)(l_term_____x5b___x5d_x27___00__closed__1));
lean_inc(v_x_224_);
v___x_228_ = l_Lean_Syntax_isOfKind(v_x_224_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v_x_224_);
v___x_229_ = lean_box(1);
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v_a_226_);
return v___x_230_;
}
else
{
lean_object* v_quotContext_231_; lean_object* v_currMacroScope_232_; lean_object* v_ref_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_quotContext_231_ = lean_ctor_get(v_a_225_, 1);
v_currMacroScope_232_ = lean_ctor_get(v_a_225_, 2);
v_ref_233_ = lean_ctor_get(v_a_225_, 5);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = l_Lean_Syntax_getArg(v_x_224_, v___x_234_);
v___x_236_ = lean_unsigned_to_nat(2u);
v___x_237_ = l_Lean_Syntax_getArg(v_x_224_, v___x_236_);
v___x_238_ = lean_unsigned_to_nat(4u);
v___x_239_ = l_Lean_Syntax_getArg(v_x_224_, v___x_238_);
lean_dec(v_x_224_);
v___x_240_ = 0;
v___x_241_ = l_Lean_SourceInfo_fromRef(v_ref_233_, v___x_240_);
v___x_242_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
v___x_243_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6);
v___x_244_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7));
lean_inc(v_currMacroScope_232_);
lean_inc(v_quotContext_231_);
v___x_245_ = l_Lean_addMacroScope(v_quotContext_231_, v___x_244_, v_currMacroScope_232_);
v___x_246_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11));
lean_inc_n(v___x_241_, 2);
v___x_247_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_247_, 0, v___x_241_);
lean_ctor_set(v___x_247_, 1, v___x_243_);
lean_ctor_set(v___x_247_, 2, v___x_245_);
lean_ctor_set(v___x_247_, 3, v___x_246_);
v___x_248_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_249_ = l_Lean_Syntax_node3(v___x_241_, v___x_248_, v___x_235_, v___x_237_, v___x_239_);
v___x_250_ = l_Lean_Syntax_node2(v___x_241_, v___x_242_, v___x_247_, v___x_249_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v_a_226_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1___boxed(lean_object* v_x_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1(v_x_252_, v_a_253_, v_a_254_);
lean_dec_ref(v_a_253_);
return v_res_255_;
}
}
lean_object* l_decidableGetElem_x3f___redArg(lean_object* v_inst_256_, lean_object* v_xs_257_, lean_object* v_i_258_, uint8_t v_inst_259_){
_start:
{
if (v_inst_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v_i_258_);
lean_dec(v_xs_257_);
lean_dec(v_inst_256_);
v___x_260_ = lean_box(0);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_apply_3(v_inst_256_, v_xs_257_, v_i_258_, lean_box(0));
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT void l_decidableGetElem_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_256_ = stack[0].m_obj;
lean_object* v_xs_257_ = stack[1].m_obj;
lean_object* v_i_258_ = stack[2].m_obj;
uint8_t v_inst_259_ = stack[3].m_num;
lean_object* v_res_263_;
v_res_263_ = l_decidableGetElem_x3f___redArg(v_inst_256_, v_xs_257_, v_i_258_, v_inst_259_);
stack->m_obj
 = v_res_263_;
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___redArg___boxed(lean_object* v_inst_264_, lean_object* v_xs_265_, lean_object* v_i_266_, lean_object* v_inst_267_){
_start:
{
uint8_t v_inst_17__boxed_268_; lean_object* v_res_269_; 
v_inst_17__boxed_268_ = lean_unbox(v_inst_267_);
v_res_269_ = l_decidableGetElem_x3f___redArg(v_inst_264_, v_xs_265_, v_i_266_, v_inst_17__boxed_268_);
return v_res_269_;
}
}
lean_object* l_decidableGetElem_x3f(lean_object* v_coll_270_, lean_object* v_idx_271_, lean_object* v_elem_272_, lean_object* v_valid_273_, lean_object* v_inst_274_, lean_object* v_xs_275_, lean_object* v_i_276_, uint8_t v_inst_277_){
_start:
{
if (v_inst_277_ == 0)
{
lean_object* v___x_278_; 
lean_dec(v_i_276_);
lean_dec(v_xs_275_);
lean_dec(v_inst_274_);
v___x_278_ = lean_box(0);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_apply_3(v_inst_274_, v_xs_275_, v_i_276_, lean_box(0));
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT void l_decidableGetElem_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_274_ = stack[4].m_obj;
lean_object* v_xs_275_ = stack[5].m_obj;
lean_object* v_i_276_ = stack[6].m_obj;
uint8_t v_inst_277_ = stack[7].m_num;
lean_object* v_res_281_;
v_res_281_ = l_decidableGetElem_x3f(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_274_, v_xs_275_, v_i_276_, v_inst_277_);
stack->m_obj
 = v_res_281_;
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___boxed(lean_object* v_coll_282_, lean_object* v_idx_283_, lean_object* v_elem_284_, lean_object* v_valid_285_, lean_object* v_inst_286_, lean_object* v_xs_287_, lean_object* v_i_288_, lean_object* v_inst_289_){
_start:
{
uint8_t v_inst_36__boxed_290_; lean_object* v_res_291_; 
v_inst_36__boxed_290_ = lean_unbox(v_inst_289_);
v_res_291_ = l_decidableGetElem_x3f(v_coll_282_, v_idx_283_, v_elem_284_, v_valid_285_, v_inst_286_, v_xs_287_, v_i_288_, v_inst_36__boxed_290_);
return v_res_291_;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0));
v___x_332_ = l_String_toRawSubstring_x27(v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1(lean_object* v_x_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l_term_____x5b___x5d___x3f___closed__1));
lean_inc(v_x_345_);
v___x_349_ = l_Lean_Syntax_isOfKind(v_x_345_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_x_345_);
v___x_350_ = lean_box(1);
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_a_347_);
return v___x_351_;
}
else
{
lean_object* v_quotContext_352_; lean_object* v_currMacroScope_353_; lean_object* v_ref_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_quotContext_352_ = lean_ctor_get(v_a_346_, 1);
v_currMacroScope_353_ = lean_ctor_get(v_a_346_, 2);
v_ref_354_ = lean_ctor_get(v_a_346_, 5);
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = l_Lean_Syntax_getArg(v_x_345_, v___x_355_);
v___x_357_ = lean_unsigned_to_nat(3u);
v___x_358_ = l_Lean_Syntax_getArg(v_x_345_, v___x_357_);
lean_dec(v_x_345_);
v___x_359_ = 0;
v___x_360_ = l_Lean_SourceInfo_fromRef(v_ref_354_, v___x_359_);
v___x_361_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
v___x_362_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1);
v___x_363_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2));
lean_inc(v_currMacroScope_353_);
lean_inc(v_quotContext_352_);
v___x_364_ = l_Lean_addMacroScope(v_quotContext_352_, v___x_363_, v_currMacroScope_353_);
v___x_365_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6));
lean_inc_n(v___x_360_, 2);
v___x_366_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_366_, 0, v___x_360_);
lean_ctor_set(v___x_366_, 1, v___x_362_);
lean_ctor_set(v___x_366_, 2, v___x_364_);
lean_ctor_set(v___x_366_, 3, v___x_365_);
v___x_367_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_368_ = l_Lean_Syntax_node2(v___x_360_, v___x_367_, v___x_356_, v___x_358_);
v___x_369_ = l_Lean_Syntax_node2(v___x_360_, v___x_361_, v___x_366_, v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v_a_347_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___boxed(lean_object* v_x_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1(v_x_371_, v_a_372_, v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_374_;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0));
v___x_393_ = l_String_toRawSubstring_x27(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1(lean_object* v_x_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_term_____x5b___x5d___x21___closed__1));
lean_inc(v_x_405_);
v___x_409_ = l_Lean_Syntax_isOfKind(v_x_405_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v_x_405_);
v___x_410_ = lean_box(1);
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_a_407_);
return v___x_411_;
}
else
{
lean_object* v_quotContext_412_; lean_object* v_currMacroScope_413_; lean_object* v_ref_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_quotContext_412_ = lean_ctor_get(v_a_406_, 1);
v_currMacroScope_413_ = lean_ctor_get(v_a_406_, 2);
v_ref_414_ = lean_ctor_get(v_a_406_, 5);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = l_Lean_Syntax_getArg(v_x_405_, v___x_415_);
v___x_417_ = lean_unsigned_to_nat(3u);
v___x_418_ = l_Lean_Syntax_getArg(v_x_405_, v___x_417_);
lean_dec(v_x_405_);
v___x_419_ = 0;
v___x_420_ = l_Lean_SourceInfo_fromRef(v_ref_414_, v___x_419_);
v___x_421_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
v___x_422_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1);
v___x_423_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2));
lean_inc(v_currMacroScope_413_);
lean_inc(v_quotContext_412_);
v___x_424_ = l_Lean_addMacroScope(v_quotContext_412_, v___x_423_, v_currMacroScope_413_);
v___x_425_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5));
lean_inc_n(v___x_420_, 2);
v___x_426_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_426_, 0, v___x_420_);
lean_ctor_set(v___x_426_, 1, v___x_422_);
lean_ctor_set(v___x_426_, 2, v___x_424_);
lean_ctor_set(v___x_426_, 3, v___x_425_);
v___x_427_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_428_ = l_Lean_Syntax_node2(v___x_420_, v___x_427_, v___x_416_, v___x_418_);
v___x_429_ = l_Lean_Syntax_node2(v___x_420_, v___x_421_, v___x_426_, v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_a_407_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___boxed(lean_object* v_x_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1(v_x_431_, v_a_432_, v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0(lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_xs_437_, lean_object* v_i_438_){
_start:
{
lean_object* v___x_439_; uint8_t v___x_440_; 
lean_inc(v_i_438_);
lean_inc(v_xs_437_);
v___x_439_ = lean_apply_2(v_inst_435_, v_xs_437_, v_i_438_);
v___x_440_ = lean_unbox(v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
lean_dec(v_i_438_);
lean_dec(v_xs_437_);
lean_dec(v_inst_436_);
v___x_441_ = lean_box(0);
return v___x_441_;
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_apply_3(v_inst_436_, v_xs_437_, v_i_438_, lean_box(0));
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(lean_object* v___f_444_, lean_object* v_inst_445_, lean_object* v_xs_446_, lean_object* v_i_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_apply_2(v___f_444_, v_xs_446_, v_i_447_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_449_; 
v___x_449_ = l_outOfBounds___redArg(v_inst_445_);
return v___x_449_;
}
else
{
lean_object* v_val_450_; 
v_val_450_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v___x_448_, 1);
return v_val_450_;
}
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1___boxed(lean_object* v___f_451_, lean_object* v_inst_452_, lean_object* v_xs_453_, lean_object* v_i_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(v___f_451_, v_inst_452_, v_xs_453_, v_i_454_);
lean_dec(v_inst_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg(lean_object* v_inst_456_, lean_object* v_inst_457_){
_start:
{
lean_object* v___f_458_; lean_object* v___f_459_; lean_object* v___x_460_; 
lean_inc(v_inst_456_);
v___f_458_ = lean_alloc_closure((void*)(l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_458_, 0, v_inst_457_);
lean_closure_set(v___f_458_, 1, v_inst_456_);
lean_inc_ref(v___f_458_);
v___f_459_ = lean_alloc_closure((void*)(l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_459_, 0, v___f_458_);
v___x_460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_460_, 0, v_inst_456_);
lean_ctor_set(v___x_460_, 1, v___f_458_);
lean_ctor_set(v___x_460_, 2, v___f_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable(lean_object* v_coll_461_, lean_object* v_idx_462_, lean_object* v_elem_463_, lean_object* v_valid_464_, lean_object* v_inst_465_, lean_object* v_inst_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_instGetElem_x3fOfGetElemOfDecidable___redArg(v_inst_465_, v_inst_466_);
return v___x_467_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1));
v___x_477_ = l_Lean_mkAtom(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3);
v___x_479_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_480_ = lean_array_push(v___x_479_, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_486_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4);
v___x_487_ = lean_array_push(v___x_486_, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_488_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6);
v___x_489_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2));
v___x_490_ = lean_box(2);
v___x_491_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v___x_489_);
lean_ctor_set(v___x_491_, 2, v___x_488_);
return v___x_491_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7);
v___x_493_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_494_ = lean_array_push(v___x_493_, v___x_492_);
return v___x_494_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_496_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8);
v___x_497_ = lean_array_push(v___x_496_, v___x_495_);
return v___x_497_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12));
v___x_506_ = l_Lean_mkAtom(v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13);
v___x_508_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_509_ = lean_array_push(v___x_508_, v___x_507_);
return v___x_509_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17));
v___x_523_ = l_Lean_mkAtom(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19);
v___x_525_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_526_ = lean_array_push(v___x_525_, v___x_524_);
return v___x_526_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_534_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_535_ = lean_array_push(v___x_534_, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_536_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23);
v___x_537_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22));
v___x_538_ = lean_box(2);
v___x_539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v___x_537_);
lean_ctor_set(v___x_539_, 2, v___x_536_);
return v___x_539_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24);
v___x_541_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20);
v___x_542_ = lean_array_push(v___x_541_, v___x_540_);
return v___x_542_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_544_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25);
v___x_545_ = lean_array_push(v___x_544_, v___x_543_);
return v___x_545_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27));
v___x_548_ = l_Lean_mkAtom(v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28);
v___x_550_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_551_ = lean_array_push(v___x_550_, v___x_549_);
return v___x_551_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29);
v___x_553_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_554_ = lean_box(2);
v___x_555_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v___x_553_);
lean_ctor_set(v___x_555_, 2, v___x_552_);
return v___x_555_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30);
v___x_557_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26);
v___x_558_ = lean_array_push(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = ((lean_object*)(l_term_____x5b___x5d___closed__7));
v___x_560_ = l_Lean_mkAtom(v___x_559_);
return v___x_560_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32);
v___x_562_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_563_ = lean_array_push(v___x_562_, v___x_561_);
return v___x_563_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_571_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23);
v___x_572_ = lean_array_push(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38));
v___x_583_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
v___x_584_ = lean_array_push(v___x_583_, v___x_582_);
return v___x_584_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39);
v___x_586_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
v___x_587_ = lean_box(2);
v___x_588_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_586_);
lean_ctor_set(v___x_588_, 2, v___x_585_);
return v___x_588_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40);
v___x_590_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_591_ = lean_array_push(v___x_590_, v___x_589_);
return v___x_591_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_592_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41);
v___x_593_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_594_ = lean_box(2);
v___x_595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
lean_ctor_set(v___x_595_, 2, v___x_592_);
return v___x_595_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42);
v___x_597_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33);
v___x_598_ = lean_array_push(v___x_597_, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l_term_____x5b___x5d___closed__17));
v___x_600_ = l_Lean_mkAtom(v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44);
v___x_602_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43);
v___x_603_ = lean_array_push(v___x_602_, v___x_601_);
return v___x_603_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_604_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45);
v___x_605_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_606_ = lean_box(2);
v___x_607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
lean_ctor_set(v___x_607_, 2, v___x_604_);
return v___x_607_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46);
v___x_609_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31);
v___x_610_ = lean_array_push(v___x_609_, v___x_608_);
return v___x_610_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_612_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47);
v___x_613_ = lean_array_push(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_614_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48);
v___x_615_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18));
v___x_616_ = lean_box(2);
v___x_617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
lean_ctor_set(v___x_617_, 2, v___x_614_);
return v___x_617_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49);
v___x_619_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_620_ = lean_array_push(v___x_619_, v___x_618_);
return v___x_620_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51));
v___x_623_ = l_Lean_mkAtom(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52);
v___x_625_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50);
v___x_626_ = lean_array_push(v___x_625_, v___x_624_);
return v___x_626_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54));
v___x_634_ = l_Lean_mkAtom(v___x_633_);
return v___x_634_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56);
v___x_636_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_637_ = lean_array_push(v___x_636_, v___x_635_);
return v___x_637_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_639_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57);
v___x_640_ = lean_array_push(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_641_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58);
v___x_642_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55));
v___x_643_ = lean_box(2);
v___x_644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_642_);
lean_ctor_set(v___x_644_, 2, v___x_641_);
return v___x_644_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59);
v___x_646_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53);
v___x_647_ = lean_array_push(v___x_646_, v___x_645_);
return v___x_647_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60);
v___x_649_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16));
v___x_650_ = lean_box(2);
v___x_651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
lean_ctor_set(v___x_651_, 2, v___x_648_);
return v___x_651_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61);
v___x_653_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_654_ = lean_array_push(v___x_653_, v___x_652_);
return v___x_654_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_655_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62);
v___x_656_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_657_ = lean_box(2);
v___x_658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___x_656_);
lean_ctor_set(v___x_658_, 2, v___x_655_);
return v___x_658_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63);
v___x_660_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_661_ = lean_array_push(v___x_660_, v___x_659_);
return v___x_661_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64);
v___x_663_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_664_ = lean_box(2);
v___x_665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_663_);
lean_ctor_set(v___x_665_, 2, v___x_662_);
return v___x_665_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65);
v___x_667_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_668_ = lean_array_push(v___x_667_, v___x_666_);
return v___x_668_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66);
v___x_670_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_671_ = lean_box(2);
v___x_672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_670_);
lean_ctor_set(v___x_672_, 2, v___x_669_);
return v___x_672_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67);
v___x_674_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14);
v___x_675_ = lean_array_push(v___x_674_, v___x_673_);
return v___x_675_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68);
v___x_677_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11));
v___x_678_ = lean_box(2);
v___x_679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_677_);
lean_ctor_set(v___x_679_, 2, v___x_676_);
return v___x_679_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69);
v___x_681_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9);
v___x_682_ = lean_array_push(v___x_681_, v___x_680_);
return v___x_682_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70);
v___x_684_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_685_ = lean_box(2);
v___x_686_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_684_);
lean_ctor_set(v___x_686_, 2, v___x_683_);
return v___x_686_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71);
v___x_688_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_689_ = lean_array_push(v___x_688_, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72);
v___x_691_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_692_ = lean_box(2);
v___x_693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___x_691_);
lean_ctor_set(v___x_693_, 2, v___x_690_);
return v___x_693_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73);
v___x_695_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_696_ = lean_array_push(v___x_695_, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_697_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74);
v___x_698_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_699_ = lean_box(2);
v___x_700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_698_);
lean_ctor_set(v___x_700_, 2, v___x_697_);
return v___x_700_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam(void){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75);
return v___x_701_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__1));
v___x_712_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
v___x_713_ = lean_array_push(v___x_712_, v___x_711_);
return v___x_713_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_714_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__2, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__2_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2);
v___x_715_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
v___x_716_ = lean_box(2);
v___x_717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___x_715_);
lean_ctor_set(v___x_717_, 2, v___x_714_);
return v___x_717_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__3, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__3_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3);
v___x_719_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_720_ = lean_array_push(v___x_719_, v___x_718_);
return v___x_720_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__6(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__5));
v___x_723_ = l_Lean_mkAtom(v___x_722_);
return v___x_723_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__6, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__6_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__6);
v___x_725_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__4, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__4_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4);
v___x_726_ = lean_array_push(v___x_725_, v___x_724_);
return v___x_726_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40);
v___x_728_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__7, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7);
v___x_729_ = lean_array_push(v___x_728_, v___x_727_);
return v___x_729_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__6, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__6_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__6);
v___x_731_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__8, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__8_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8);
v___x_732_ = lean_array_push(v___x_731_, v___x_730_);
return v___x_732_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__14(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__13));
v___x_746_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
v___x_747_ = lean_array_push(v___x_746_, v___x_745_);
return v___x_747_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_748_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__14, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__14_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__14);
v___x_749_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
v___x_750_ = lean_box(2);
v___x_751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
lean_ctor_set(v___x_751_, 2, v___x_748_);
return v___x_751_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__15, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__15_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15);
v___x_753_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9);
v___x_754_ = lean_array_push(v___x_753_, v___x_752_);
return v___x_754_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__16, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__16_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16);
v___x_756_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_757_ = lean_box(2);
v___x_758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v___x_756_);
lean_ctor_set(v___x_758_, 2, v___x_755_);
return v___x_758_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__17, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__17_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17);
v___x_760_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33);
v___x_761_ = lean_array_push(v___x_760_, v___x_759_);
return v___x_761_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44);
v___x_763_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__18, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__18_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18);
v___x_764_ = lean_array_push(v___x_763_, v___x_762_);
return v___x_764_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_765_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__19, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__19_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19);
v___x_766_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_767_ = lean_box(2);
v___x_768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v___x_766_);
lean_ctor_set(v___x_768_, 2, v___x_765_);
return v___x_768_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__20, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__20_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20);
v___x_770_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31);
v___x_771_ = lean_array_push(v___x_770_, v___x_769_);
return v___x_771_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_773_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__21, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__21_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21);
v___x_774_ = lean_array_push(v___x_773_, v___x_772_);
return v___x_774_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__22, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__22_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22);
v___x_776_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18));
v___x_777_ = lean_box(2);
v___x_778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_776_);
lean_ctor_set(v___x_778_, 2, v___x_775_);
return v___x_778_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23);
v___x_780_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9);
v___x_781_ = lean_array_push(v___x_780_, v___x_779_);
return v___x_781_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_782_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__24, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__24_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24);
v___x_783_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_784_ = lean_box(2);
v___x_785_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v___x_783_);
lean_ctor_set(v___x_785_, 2, v___x_782_);
return v___x_785_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__25, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__25_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25);
v___x_787_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_788_ = lean_array_push(v___x_787_, v___x_786_);
return v___x_788_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_789_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__26, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__26_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26);
v___x_790_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_791_ = lean_box(2);
v___x_792_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___x_790_);
lean_ctor_set(v___x_792_, 2, v___x_789_);
return v___x_792_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_793_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__27, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__27_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27);
v___x_794_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_795_ = lean_array_push(v___x_794_, v___x_793_);
return v___x_795_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_796_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__28, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__28_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28);
v___x_797_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_798_ = lean_box(2);
v___x_799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v___x_797_);
lean_ctor_set(v___x_799_, 2, v___x_796_);
return v___x_799_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam(void){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__29, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__29_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_801_, lean_object* v_h__1_802_, lean_object* v_h__2_803_){
_start:
{
if (lean_obj_tag(v_x_801_) == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec(v_h__1_802_);
v___x_804_ = lean_box(0);
v___x_805_ = lean_apply_1(v_h__2_803_, v___x_804_);
return v___x_805_;
}
else
{
lean_object* v_val_806_; lean_object* v___x_807_; 
lean_dec(v_h__2_803_);
v_val_806_ = lean_ctor_get(v_x_801_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v_x_801_, 1);
v___x_807_ = lean_apply_1(v_h__1_802_, v_val_806_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_808_, lean_object* v_motive_809_, lean_object* v_x_810_, lean_object* v_h__1_811_, lean_object* v_h__2_812_){
_start:
{
if (lean_obj_tag(v_x_810_) == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v_h__1_811_);
v___x_813_ = lean_box(0);
v___x_814_ = lean_apply_1(v_h__2_812_, v___x_813_);
return v___x_814_;
}
else
{
lean_object* v_val_815_; lean_object* v___x_816_; 
lean_dec(v_h__2_812_);
v_val_815_ = lean_ctor_get(v_x_810_, 0);
lean_inc(v_val_815_);
lean_dec_ref_known(v_x_810_, 1);
v___x_816_ = lean_apply_1(v_h__1_811_, v_val_815_);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___redArg___lam__0(lean_object* v_inst_817_, lean_object* v_xs_818_, lean_object* v_i_819_, lean_object* v_h_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = lean_apply_3(v_inst_817_, v_xs_818_, v_i_819_, lean_box(0));
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___redArg(lean_object* v_inst_822_){
_start:
{
lean_object* v___f_823_; 
v___f_823_ = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(v___f_823_, 0, v_inst_822_);
return v___f_823_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal(lean_object* v_cont_824_, lean_object* v_elem_825_, lean_object* v_dom_826_, lean_object* v_n_827_, lean_object* v_inst_828_){
_start:
{
lean_object* v___f_829_; 
v___f_829_ = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(v___f_829_, 0, v_inst_828_);
return v___f_829_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___boxed(lean_object* v_cont_830_, lean_object* v_elem_831_, lean_object* v_dom_832_, lean_object* v_n_833_, lean_object* v_inst_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Fin_instGetElemFinVal(v_cont_830_, v_elem_831_, v_dom_832_, v_n_833_, v_inst_834_);
lean_dec(v_n_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg___lam__0(lean_object* v_getElem_x3f_836_, lean_object* v_xs_837_, lean_object* v_i_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = lean_apply_2(v_getElem_x3f_836_, v_xs_837_, v_i_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg___lam__1(lean_object* v_getElem_x21_840_, lean_object* v_inst_841_, lean_object* v_xs_842_, lean_object* v_i_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = lean_apply_3(v_getElem_x21_840_, v_inst_841_, v_xs_842_, v_i_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg(lean_object* v_inst_845_){
_start:
{
lean_object* v_toGetElem_846_; lean_object* v_getElem_x3f_847_; lean_object* v_getElem_x21_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_858_; 
v_toGetElem_846_ = lean_ctor_get(v_inst_845_, 0);
v_getElem_x3f_847_ = lean_ctor_get(v_inst_845_, 1);
v_getElem_x21_848_ = lean_ctor_get(v_inst_845_, 2);
v_isSharedCheck_858_ = !lean_is_exclusive(v_inst_845_);
if (v_isSharedCheck_858_ == 0)
{
v___x_850_ = v_inst_845_;
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_getElem_x21_848_);
lean_inc(v_getElem_x3f_847_);
lean_inc(v_toGetElem_846_);
lean_dec(v_inst_845_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___f_854_; lean_object* v___x_856_; 
v___f_852_ = lean_alloc_closure((void*)(l_Fin_instGetElem_x3fFinVal___redArg___lam__0), 3, 1);
lean_closure_set(v___f_852_, 0, v_getElem_x3f_847_);
v___f_853_ = lean_alloc_closure((void*)(l_Fin_instGetElem_x3fFinVal___redArg___lam__1), 4, 1);
lean_closure_set(v___f_853_, 0, v_getElem_x21_848_);
v___f_854_ = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(v___f_854_, 0, v_toGetElem_846_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 2, v___f_853_);
lean_ctor_set(v___x_850_, 1, v___f_852_);
lean_ctor_set(v___x_850_, 0, v___f_854_);
v___x_856_ = v___x_850_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___f_854_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___f_852_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v___f_853_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal(lean_object* v_cont_859_, lean_object* v_elem_860_, lean_object* v_dom_861_, lean_object* v_n_862_, lean_object* v_inst_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Fin_instGetElem_x3fFinVal___redArg(v_inst_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___boxed(lean_object* v_cont_865_, lean_object* v_elem_866_, lean_object* v_dom_867_, lean_object* v_n_868_, lean_object* v_inst_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Fin_instGetElem_x3fFinVal(v_cont_865_, v_elem_866_, v_dom_867_, v_n_868_, v_inst_869_);
lean_dec(v_n_868_);
return v_res_870_;
}
}
static lean_object* _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10));
v___x_900_ = l_String_toRawSubstring_x27(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(lean_object* v_x_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1));
v___x_924_ = l_Lean_Syntax_isOfKind(v_x_920_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_box(1);
v___x_926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v_a_922_);
return v___x_926_;
}
else
{
lean_object* v_quotContext_927_; lean_object* v_currMacroScope_928_; lean_object* v_ref_929_; uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_quotContext_927_ = lean_ctor_get(v_a_921_, 1);
v_currMacroScope_928_ = lean_ctor_get(v_a_921_, 2);
v_ref_929_ = lean_ctor_get(v_a_921_, 5);
v___x_930_ = 0;
v___x_931_ = l_Lean_SourceInfo_fromRef(v_ref_929_, v___x_930_);
v___x_932_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3));
v___x_933_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_934_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4));
v___x_935_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18));
lean_inc_n(v___x_931_, 20);
v___x_936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_931_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_938_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_939_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6));
v___x_940_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7));
v___x_941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_931_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8));
v___x_943_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9));
v___x_944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_931_);
lean_ctor_set(v___x_944_, 1, v___x_942_);
v___x_945_ = lean_obj_once(&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11, &l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_once, _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11);
v___x_946_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14));
lean_inc(v_currMacroScope_928_);
lean_inc(v_quotContext_927_);
v___x_947_ = l_Lean_addMacroScope(v_quotContext_927_, v___x_946_, v_currMacroScope_928_);
v___x_948_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16));
v___x_949_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_949_, 0, v___x_931_);
lean_ctor_set(v___x_949_, 1, v___x_945_);
lean_ctor_set(v___x_949_, 2, v___x_947_);
lean_ctor_set(v___x_949_, 3, v___x_948_);
v___x_950_ = l_Lean_Syntax_node2(v___x_931_, v___x_943_, v___x_944_, v___x_949_);
v___x_951_ = l_Lean_Syntax_node1(v___x_931_, v___x_933_, v___x_950_);
v___x_952_ = l_Lean_Syntax_node1(v___x_931_, v___x_938_, v___x_951_);
v___x_953_ = l_Lean_Syntax_node1(v___x_931_, v___x_937_, v___x_952_);
v___x_954_ = l_Lean_Syntax_node2(v___x_931_, v___x_939_, v___x_941_, v___x_953_);
v___x_955_ = l_Lean_Syntax_node1(v___x_931_, v___x_933_, v___x_954_);
v___x_956_ = l_Lean_Syntax_node1(v___x_931_, v___x_938_, v___x_955_);
v___x_957_ = l_Lean_Syntax_node1(v___x_931_, v___x_937_, v___x_956_);
v___x_958_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36));
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_931_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Lean_Syntax_node3(v___x_931_, v___x_934_, v___x_936_, v___x_957_, v___x_959_);
v___x_961_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17));
v___x_962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_931_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18));
v___x_964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_931_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l_Lean_Syntax_node1(v___x_931_, v___x_923_, v___x_964_);
v___x_966_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19));
v___x_967_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20));
v___x_968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_931_);
lean_ctor_set(v___x_968_, 1, v___x_966_);
v___x_969_ = l_Lean_Syntax_node1(v___x_931_, v___x_967_, v___x_968_);
lean_inc_ref(v___x_962_);
v___x_970_ = l_Lean_Syntax_node5(v___x_931_, v___x_933_, v___x_960_, v___x_962_, v___x_965_, v___x_962_, v___x_969_);
v___x_971_ = l_Lean_Syntax_node1(v___x_931_, v___x_932_, v___x_970_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v_a_922_);
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___boxed(lean_object* v_x_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(v_x_973_, v_a_974_, v_a_975_);
lean_dec_ref(v_a_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___redArg___lam__0(lean_object* v_as_977_, lean_object* v_i_978_, lean_object* v_h_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_List_get___redArg(v_as_977_, v_i_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___redArg___lam__0___boxed(lean_object* v_as_981_, lean_object* v_i_982_, lean_object* v_h_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_List_instGetElemNatLtLength___redArg___lam__0(v_as_981_, v_i_982_, v_h_983_);
lean_dec(v_as_981_);
return v_res_984_;
}
}
lean_object* l_List_instGetElemNatLtLength___redArg(){
_start:
{
lean_object* v___f_987_; 
v___f_987_ = ((lean_object*)(l_List_instGetElemNatLtLength___redArg___closed__0));
return v___f_987_;
}
}
LEAN_EXPORT void l_List_instGetElemNatLtLength___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_988_;
v_res_988_ = l_List_instGetElemNatLtLength___redArg();
stack->m_obj
 = v_res_988_;
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___redArg___boxed(lean_object* v___dummy_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_List_instGetElemNatLtLength___redArg();
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength(lean_object* v_00_u03b1_991_){
_start:
{
lean_object* v___f_992_; 
v___f_992_ = ((lean_object*)(l_List_instGetElemNatLtLength___redArg___closed__0));
return v___f_992_;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___redArg(lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
if (lean_obj_tag(v_x_993_) == 1)
{
lean_object* v_head_995_; lean_object* v_tail_996_; lean_object* v_zero_997_; uint8_t v_isZero_998_; 
v_head_995_ = lean_ctor_get(v_x_993_, 0);
v_tail_996_ = lean_ctor_get(v_x_993_, 1);
v_zero_997_ = lean_unsigned_to_nat(0u);
v_isZero_998_ = lean_nat_dec_eq(v_x_994_, v_zero_997_);
if (v_isZero_998_ == 1)
{
lean_object* v___x_999_; 
lean_dec(v_x_994_);
lean_inc(v_head_995_);
v___x_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_999_, 0, v_head_995_);
return v___x_999_;
}
else
{
lean_object* v_one_1000_; lean_object* v_n_1001_; 
v_one_1000_ = lean_unsigned_to_nat(1u);
v_n_1001_ = lean_nat_sub(v_x_994_, v_one_1000_);
lean_dec(v_x_994_);
v_x_993_ = v_tail_996_;
v_x_994_ = v_n_1001_;
goto _start;
}
}
else
{
lean_object* v___x_1003_; 
lean_dec(v_x_994_);
v___x_1003_ = lean_box(0);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___redArg___boxed(lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_List_get_x3fInternal___redArg(v_x_1004_, v_x_1005_);
lean_dec(v_x_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal(lean_object* v_00_u03b1_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_List_get_x3fInternal___redArg(v_x_1008_, v_x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___boxed(lean_object* v_00_u03b1_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_List_get_x3fInternal(v_00_u03b1_1011_, v_x_1012_, v_x_1013_);
lean_dec(v_x_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___redArg(lean_object* v_inst_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
if (lean_obj_tag(v_x_1018_) == 1)
{
lean_object* v_head_1020_; lean_object* v_tail_1021_; lean_object* v_zero_1022_; uint8_t v_isZero_1023_; 
v_head_1020_ = lean_ctor_get(v_x_1018_, 0);
v_tail_1021_ = lean_ctor_get(v_x_1018_, 1);
v_zero_1022_ = lean_unsigned_to_nat(0u);
v_isZero_1023_ = lean_nat_dec_eq(v_x_1019_, v_zero_1022_);
if (v_isZero_1023_ == 1)
{
lean_dec(v_x_1019_);
lean_inc(v_head_1020_);
return v_head_1020_;
}
else
{
lean_object* v_one_1024_; lean_object* v_n_1025_; 
v_one_1024_ = lean_unsigned_to_nat(1u);
v_n_1025_ = lean_nat_sub(v_x_1019_, v_one_1024_);
lean_dec(v_x_1019_);
v_x_1018_ = v_tail_1021_;
v_x_1019_ = v_n_1025_;
goto _start;
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec(v_x_1019_);
v___x_1027_ = ((lean_object*)(l_outOfBounds___redArg___closed__0));
v___x_1028_ = ((lean_object*)(l_List_get_x21Internal___redArg___closed__0));
v___x_1029_ = lean_unsigned_to_nat(333u);
v___x_1030_ = lean_unsigned_to_nat(18u);
v___x_1031_ = ((lean_object*)(l_List_get_x21Internal___redArg___closed__1));
v___x_1032_ = l_mkPanicMessageWithDecl(v___x_1027_, v___x_1028_, v___x_1029_, v___x_1030_, v___x_1031_);
v___x_1033_ = l_panic___redArg(v_inst_1017_, v___x_1032_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___redArg___boxed(lean_object* v_inst_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_List_get_x21Internal___redArg(v_inst_1034_, v_x_1035_, v_x_1036_);
lean_dec(v_x_1035_);
lean_dec(v_inst_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal(lean_object* v_00_u03b1_1038_, lean_object* v_inst_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_List_get_x21Internal___redArg(v_inst_1039_, v_x_1040_, v_x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_inst_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_List_get_x21Internal(v_00_u03b1_1043_, v_inst_1044_, v_x_1045_, v_x_1046_);
lean_dec(v_x_1045_);
lean_dec(v_inst_1044_);
return v_res_1047_;
}
}
lean_object* l_List_instGetElem_x3fNatLtLength___redArg(){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = ((lean_object*)(l_List_instGetElem_x3fNatLtLength___redArg___closed__2));
return v___x_1055_;
}
}
LEAN_EXPORT void l_List_instGetElem_x3fNatLtLength___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1056_;
v_res_1056_ = l_List_instGetElem_x3fNatLtLength___redArg();
stack->m_obj
 = v_res_1056_;
}
LEAN_EXPORT lean_object* l_List_instGetElem_x3fNatLtLength___redArg___boxed(lean_object* v___dummy_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_List_instGetElem_x3fNatLtLength___redArg();
return v_res_1058_;
}
}
static lean_object* _init_l_List_instGetElem_x3fNatLtLength___closed__0(void){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_List_instGetElem_x3fNatLtLength___redArg();
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_List_instGetElem_x3fNatLtLength(lean_object* v_00_u03b1_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_obj_once(&l_List_instGetElem_x3fNatLtLength___closed__0, &l_List_instGetElem_x3fNatLtLength___closed__0_once, _init_l_List_instGetElem_x3fNatLtLength___closed__0);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___redArg___lam__0(lean_object* v_xs_1062_, lean_object* v_i_1063_, lean_object* v_h_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_array_fget_borrowed(v_xs_1062_, v_i_1063_);
lean_inc(v___x_1065_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___redArg___lam__0___boxed(lean_object* v_xs_1066_, lean_object* v_i_1067_, lean_object* v_h_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Array_instGetElemNatLtSize___redArg___lam__0(v_xs_1066_, v_i_1067_, v_h_1068_);
lean_dec(v_i_1067_);
lean_dec_ref(v_xs_1066_);
return v_res_1069_;
}
}
lean_object* l_Array_instGetElemNatLtSize___redArg(){
_start:
{
lean_object* v___f_1072_; 
v___f_1072_ = ((lean_object*)(l_Array_instGetElemNatLtSize___redArg___closed__0));
return v___f_1072_;
}
}
LEAN_EXPORT void l_Array_instGetElemNatLtSize___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1073_;
v_res_1073_ = l_Array_instGetElemNatLtSize___redArg();
stack->m_obj
 = v_res_1073_;
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___redArg___boxed(lean_object* v___dummy_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Array_instGetElemNatLtSize___redArg();
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize(lean_object* v_00_u03b1_1076_){
_start:
{
lean_object* v___f_1077_; 
v___f_1077_ = ((lean_object*)(l_Array_instGetElemNatLtSize___redArg___closed__0));
return v___f_1077_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___lam__0(lean_object* v_xs_1078_, lean_object* v_i_1079_){
_start:
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_array_get_size(v_xs_1078_);
v___x_1081_ = lean_nat_dec_lt(v_i_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_box(0);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_array_fget_borrowed(v_xs_1078_, v_i_1079_);
lean_inc(v___x_1083_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___lam__0___boxed(lean_object* v_xs_1085_, lean_object* v_i_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Array_instGetElem_x3fNatLtSize___redArg___lam__0(v_xs_1085_, v_i_1086_);
lean_dec(v_i_1086_);
lean_dec_ref(v_xs_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___lam__1(lean_object* v_inst_1088_, lean_object* v_xs_1089_, lean_object* v_i_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_array_get_borrowed(v_inst_1088_, v_xs_1089_, v_i_1090_);
lean_inc(v___x_1091_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___lam__1___boxed(lean_object* v_inst_1092_, lean_object* v_xs_1093_, lean_object* v_i_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Array_instGetElem_x3fNatLtSize___redArg___lam__1(v_inst_1092_, v_xs_1093_, v_i_1094_);
lean_dec(v_i_1094_);
lean_dec_ref(v_xs_1093_);
lean_dec(v_inst_1092_);
return v_res_1095_;
}
}
lean_object* l_Array_instGetElem_x3fNatLtSize___redArg(){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = ((lean_object*)(l_Array_instGetElem_x3fNatLtSize___redArg___closed__2));
return v___x_1103_;
}
}
LEAN_EXPORT void l_Array_instGetElem_x3fNatLtSize___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1104_;
v_res_1104_ = l_Array_instGetElem_x3fNatLtSize___redArg();
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___redArg___boxed(lean_object* v___dummy_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Array_instGetElem_x3fNatLtSize___redArg();
return v_res_1106_;
}
}
static lean_object* _init_l_Array_instGetElem_x3fNatLtSize___closed__0(void){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Array_instGetElem_x3fNatLtSize___redArg();
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize(lean_object* v_00_u03b1_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_obj_once(&l_Array_instGetElem_x3fNatLtSize___closed__0, &l_Array_instGetElem_x3fNatLtSize___closed__0_once, _init_l_Array_instGetElem_x3fNatLtSize___closed__0);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instGetElemNatTrue___lam__0(lean_object* v_stx_1110_, lean_object* v_i_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_Syntax_getArg(v_stx_1110_, v_i_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instGetElemNatTrue___lam__0___boxed(lean_object* v_stx_1114_, lean_object* v_i_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Syntax_instGetElemNatTrue___lam__0(v_stx_1114_, v_i_1115_, v_x_1116_);
lean_dec(v_i_1115_);
lean_dec(v_stx_1114_);
return v_res_1117_;
}
}
lean_object* runtime_initialize_Init_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_GetElem(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
