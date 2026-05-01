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
LEAN_EXPORT lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___redArg(lean_object* v_inst_256_, lean_object* v_xs_257_, lean_object* v_i_258_, uint8_t v_inst_259_){
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
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___redArg___boxed(lean_object* v_inst_263_, lean_object* v_xs_264_, lean_object* v_i_265_, lean_object* v_inst_266_){
_start:
{
uint8_t v_inst_16__boxed_267_; lean_object* v_res_268_; 
v_inst_16__boxed_267_ = lean_unbox(v_inst_266_);
v_res_268_ = l_decidableGetElem_x3f___redArg(v_inst_263_, v_xs_264_, v_i_265_, v_inst_16__boxed_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f(lean_object* v_coll_269_, lean_object* v_idx_270_, lean_object* v_elem_271_, lean_object* v_valid_272_, lean_object* v_inst_273_, lean_object* v_xs_274_, lean_object* v_i_275_, uint8_t v_inst_276_){
_start:
{
if (v_inst_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec(v_i_275_);
lean_dec(v_xs_274_);
lean_dec(v_inst_273_);
v___x_277_ = lean_box(0);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_apply_3(v_inst_273_, v_xs_274_, v_i_275_, lean_box(0));
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_decidableGetElem_x3f___boxed(lean_object* v_coll_280_, lean_object* v_idx_281_, lean_object* v_elem_282_, lean_object* v_valid_283_, lean_object* v_inst_284_, lean_object* v_xs_285_, lean_object* v_i_286_, lean_object* v_inst_287_){
_start:
{
uint8_t v_inst_28__boxed_288_; lean_object* v_res_289_; 
v_inst_28__boxed_288_ = lean_unbox(v_inst_287_);
v_res_289_ = l_decidableGetElem_x3f(v_coll_280_, v_idx_281_, v_elem_282_, v_valid_283_, v_inst_284_, v_xs_285_, v_i_286_, v_inst_28__boxed_288_);
return v_res_289_;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0));
v___x_330_ = l_String_toRawSubstring_x27(v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1(lean_object* v_x_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = ((lean_object*)(l_term_____x5b___x5d___x3f___closed__1));
lean_inc(v_x_343_);
v___x_347_ = l_Lean_Syntax_isOfKind(v_x_343_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_x_343_);
v___x_348_ = lean_box(1);
v___x_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_a_345_);
return v___x_349_;
}
else
{
lean_object* v_quotContext_350_; lean_object* v_currMacroScope_351_; lean_object* v_ref_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_quotContext_350_ = lean_ctor_get(v_a_344_, 1);
v_currMacroScope_351_ = lean_ctor_get(v_a_344_, 2);
v_ref_352_ = lean_ctor_get(v_a_344_, 5);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = l_Lean_Syntax_getArg(v_x_343_, v___x_353_);
v___x_355_ = lean_unsigned_to_nat(3u);
v___x_356_ = l_Lean_Syntax_getArg(v_x_343_, v___x_355_);
lean_dec(v_x_343_);
v___x_357_ = 0;
v___x_358_ = l_Lean_SourceInfo_fromRef(v_ref_352_, v___x_357_);
v___x_359_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
v___x_360_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1);
v___x_361_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2));
lean_inc(v_currMacroScope_351_);
lean_inc(v_quotContext_350_);
v___x_362_ = l_Lean_addMacroScope(v_quotContext_350_, v___x_361_, v_currMacroScope_351_);
v___x_363_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6));
lean_inc_n(v___x_358_, 2);
v___x_364_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_364_, 0, v___x_358_);
lean_ctor_set(v___x_364_, 1, v___x_360_);
lean_ctor_set(v___x_364_, 2, v___x_362_);
lean_ctor_set(v___x_364_, 3, v___x_363_);
v___x_365_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_366_ = l_Lean_Syntax_node2(v___x_358_, v___x_365_, v___x_354_, v___x_356_);
v___x_367_ = l_Lean_Syntax_node2(v___x_358_, v___x_359_, v___x_364_, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v_a_345_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___boxed(lean_object* v_x_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1(v_x_369_, v_a_370_, v_a_371_);
lean_dec_ref(v_a_370_);
return v_res_372_;
}
}
static lean_object* _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0));
v___x_391_ = l_String_toRawSubstring_x27(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1(lean_object* v_x_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l_term_____x5b___x5d___x21___closed__1));
lean_inc(v_x_403_);
v___x_407_ = l_Lean_Syntax_isOfKind(v_x_403_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v_x_403_);
v___x_408_ = lean_box(1);
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_a_405_);
return v___x_409_;
}
else
{
lean_object* v_quotContext_410_; lean_object* v_currMacroScope_411_; lean_object* v_ref_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_quotContext_410_ = lean_ctor_get(v_a_404_, 1);
v_currMacroScope_411_ = lean_ctor_get(v_a_404_, 2);
v_ref_412_ = lean_ctor_get(v_a_404_, 5);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = l_Lean_Syntax_getArg(v_x_403_, v___x_413_);
v___x_415_ = lean_unsigned_to_nat(3u);
v___x_416_ = l_Lean_Syntax_getArg(v_x_403_, v___x_415_);
lean_dec(v_x_403_);
v___x_417_ = 0;
v___x_418_ = l_Lean_SourceInfo_fromRef(v_ref_412_, v___x_417_);
v___x_419_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4));
v___x_420_ = lean_obj_once(&l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1, &l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1_once, _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1);
v___x_421_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2));
lean_inc(v_currMacroScope_411_);
lean_inc(v_quotContext_410_);
v___x_422_ = l_Lean_addMacroScope(v_quotContext_410_, v___x_421_, v_currMacroScope_411_);
v___x_423_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5));
lean_inc_n(v___x_418_, 2);
v___x_424_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_424_, 0, v___x_418_);
lean_ctor_set(v___x_424_, 1, v___x_420_);
lean_ctor_set(v___x_424_, 2, v___x_422_);
lean_ctor_set(v___x_424_, 3, v___x_423_);
v___x_425_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_426_ = l_Lean_Syntax_node2(v___x_418_, v___x_425_, v___x_414_, v___x_416_);
v___x_427_ = l_Lean_Syntax_node2(v___x_418_, v___x_419_, v___x_424_, v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_a_405_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___boxed(lean_object* v_x_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1(v_x_429_, v_a_430_, v_a_431_);
lean_dec_ref(v_a_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0(lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_xs_435_, lean_object* v_i_436_){
_start:
{
lean_object* v___x_437_; uint8_t v___x_438_; 
lean_inc(v_i_436_);
lean_inc(v_xs_435_);
v___x_437_ = lean_apply_2(v_inst_433_, v_xs_435_, v_i_436_);
v___x_438_ = lean_unbox(v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_dec(v_i_436_);
lean_dec(v_xs_435_);
lean_dec(v_inst_434_);
v___x_439_ = lean_box(0);
return v___x_439_;
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_apply_3(v_inst_434_, v_xs_435_, v_i_436_, lean_box(0));
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(lean_object* v___f_442_, lean_object* v_inst_443_, lean_object* v_xs_444_, lean_object* v_i_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = lean_apply_2(v___f_442_, v_xs_444_, v_i_445_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v___x_447_; 
v___x_447_ = l_outOfBounds___redArg(v_inst_443_);
return v___x_447_;
}
else
{
lean_object* v_val_448_; 
v_val_448_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_val_448_);
lean_dec_ref(v___x_446_);
return v_val_448_;
}
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1___boxed(lean_object* v___f_449_, lean_object* v_inst_450_, lean_object* v_xs_451_, lean_object* v_i_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(v___f_449_, v_inst_450_, v_xs_451_, v_i_452_);
lean_dec(v_inst_450_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable___redArg(lean_object* v_inst_454_, lean_object* v_inst_455_){
_start:
{
lean_object* v___f_456_; lean_object* v___f_457_; lean_object* v___x_458_; 
lean_inc(v_inst_454_);
v___f_456_ = lean_alloc_closure((void*)(l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_456_, 0, v_inst_455_);
lean_closure_set(v___f_456_, 1, v_inst_454_);
lean_inc_ref(v___f_456_);
v___f_457_ = lean_alloc_closure((void*)(l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_457_, 0, v___f_456_);
v___x_458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_458_, 0, v_inst_454_);
lean_ctor_set(v___x_458_, 1, v___f_456_);
lean_ctor_set(v___x_458_, 2, v___f_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_instGetElem_x3fOfGetElemOfDecidable(lean_object* v_coll_459_, lean_object* v_idx_460_, lean_object* v_elem_461_, lean_object* v_valid_462_, lean_object* v_inst_463_, lean_object* v_inst_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_instGetElem_x3fOfGetElemOfDecidable___redArg(v_inst_463_, v_inst_464_);
return v___x_465_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1));
v___x_475_ = l_Lean_mkAtom(v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3);
v___x_477_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_478_ = lean_array_push(v___x_477_, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_484_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4);
v___x_485_ = lean_array_push(v___x_484_, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6);
v___x_487_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2));
v___x_488_ = lean_box(2);
v___x_489_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
lean_ctor_set(v___x_489_, 2, v___x_486_);
return v___x_489_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7);
v___x_491_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_492_ = lean_array_push(v___x_491_, v___x_490_);
return v___x_492_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_494_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8);
v___x_495_ = lean_array_push(v___x_494_, v___x_493_);
return v___x_495_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12));
v___x_504_ = l_Lean_mkAtom(v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13);
v___x_506_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_507_ = lean_array_push(v___x_506_, v___x_505_);
return v___x_507_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17));
v___x_521_ = l_Lean_mkAtom(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19);
v___x_523_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_524_ = lean_array_push(v___x_523_, v___x_522_);
return v___x_524_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_532_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_533_ = lean_array_push(v___x_532_, v___x_531_);
return v___x_533_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_534_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23);
v___x_535_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22));
v___x_536_ = lean_box(2);
v___x_537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
lean_ctor_set(v___x_537_, 2, v___x_534_);
return v___x_537_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24);
v___x_539_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20);
v___x_540_ = lean_array_push(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_542_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25);
v___x_543_ = lean_array_push(v___x_542_, v___x_541_);
return v___x_543_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27));
v___x_546_ = l_Lean_mkAtom(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28);
v___x_548_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_549_ = lean_array_push(v___x_548_, v___x_547_);
return v___x_549_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_550_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29);
v___x_551_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_552_ = lean_box(2);
v___x_553_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v___x_551_);
lean_ctor_set(v___x_553_, 2, v___x_550_);
return v___x_553_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30);
v___x_555_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26);
v___x_556_ = lean_array_push(v___x_555_, v___x_554_);
return v___x_556_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = ((lean_object*)(l_term_____x5b___x5d___closed__7));
v___x_558_ = l_Lean_mkAtom(v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32);
v___x_560_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_561_ = lean_array_push(v___x_560_, v___x_559_);
return v___x_561_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_569_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23);
v___x_570_ = lean_array_push(v___x_569_, v___x_568_);
return v___x_570_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0));
v___x_572_ = lean_string_utf8_byte_size(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0));
v___x_576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_574_);
lean_ctor_set(v___x_576_, 2, v___x_573_);
return v___x_576_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_577_ = lean_box(0);
v___x_578_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2));
v___x_579_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38);
v___x_580_ = lean_box(2);
v___x_581_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_578_);
lean_ctor_set(v___x_581_, 3, v___x_577_);
return v___x_581_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39);
v___x_583_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
v___x_584_ = lean_array_push(v___x_583_, v___x_582_);
return v___x_584_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40);
v___x_586_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
v___x_587_ = lean_box(2);
v___x_588_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_586_);
lean_ctor_set(v___x_588_, 2, v___x_585_);
return v___x_588_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41);
v___x_590_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_591_ = lean_array_push(v___x_590_, v___x_589_);
return v___x_591_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_592_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42);
v___x_593_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_594_ = lean_box(2);
v___x_595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
lean_ctor_set(v___x_595_, 2, v___x_592_);
return v___x_595_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43);
v___x_597_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33);
v___x_598_ = lean_array_push(v___x_597_, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l_term_____x5b___x5d___closed__17));
v___x_600_ = l_Lean_mkAtom(v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45);
v___x_602_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44);
v___x_603_ = lean_array_push(v___x_602_, v___x_601_);
return v___x_603_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_604_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46);
v___x_605_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_606_ = lean_box(2);
v___x_607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
lean_ctor_set(v___x_607_, 2, v___x_604_);
return v___x_607_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47);
v___x_609_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31);
v___x_610_ = lean_array_push(v___x_609_, v___x_608_);
return v___x_610_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_612_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48);
v___x_613_ = lean_array_push(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_614_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49);
v___x_615_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18));
v___x_616_ = lean_box(2);
v___x_617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
lean_ctor_set(v___x_617_, 2, v___x_614_);
return v___x_617_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50);
v___x_619_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_620_ = lean_array_push(v___x_619_, v___x_618_);
return v___x_620_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52));
v___x_623_ = l_Lean_mkAtom(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53);
v___x_625_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51);
v___x_626_ = lean_array_push(v___x_625_, v___x_624_);
return v___x_626_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55));
v___x_634_ = l_Lean_mkAtom(v___x_633_);
return v___x_634_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57);
v___x_636_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_637_ = lean_array_push(v___x_636_, v___x_635_);
return v___x_637_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_639_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58);
v___x_640_ = lean_array_push(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_641_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59);
v___x_642_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56));
v___x_643_ = lean_box(2);
v___x_644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_642_);
lean_ctor_set(v___x_644_, 2, v___x_641_);
return v___x_644_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60);
v___x_646_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54);
v___x_647_ = lean_array_push(v___x_646_, v___x_645_);
return v___x_647_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61);
v___x_649_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16));
v___x_650_ = lean_box(2);
v___x_651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
lean_ctor_set(v___x_651_, 2, v___x_648_);
return v___x_651_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62);
v___x_653_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_654_ = lean_array_push(v___x_653_, v___x_652_);
return v___x_654_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_655_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63);
v___x_656_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_657_ = lean_box(2);
v___x_658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___x_656_);
lean_ctor_set(v___x_658_, 2, v___x_655_);
return v___x_658_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64);
v___x_660_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_661_ = lean_array_push(v___x_660_, v___x_659_);
return v___x_661_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65);
v___x_663_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_664_ = lean_box(2);
v___x_665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_663_);
lean_ctor_set(v___x_665_, 2, v___x_662_);
return v___x_665_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66);
v___x_667_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_668_ = lean_array_push(v___x_667_, v___x_666_);
return v___x_668_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67);
v___x_670_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_671_ = lean_box(2);
v___x_672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_670_);
lean_ctor_set(v___x_672_, 2, v___x_669_);
return v___x_672_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68);
v___x_674_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14);
v___x_675_ = lean_array_push(v___x_674_, v___x_673_);
return v___x_675_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69);
v___x_677_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11));
v___x_678_ = lean_box(2);
v___x_679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_677_);
lean_ctor_set(v___x_679_, 2, v___x_676_);
return v___x_679_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70);
v___x_681_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9);
v___x_682_ = lean_array_push(v___x_681_, v___x_680_);
return v___x_682_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71);
v___x_684_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_685_ = lean_box(2);
v___x_686_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_684_);
lean_ctor_set(v___x_686_, 2, v___x_683_);
return v___x_686_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72);
v___x_688_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_689_ = lean_array_push(v___x_688_, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73);
v___x_691_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_692_ = lean_box(2);
v___x_693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___x_691_);
lean_ctor_set(v___x_693_, 2, v___x_690_);
return v___x_693_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74);
v___x_695_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_696_ = lean_array_push(v___x_695_, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_697_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75);
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
v___x_701_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76);
return v___x_701_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__0(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0));
v___x_703_ = lean_string_utf8_byte_size(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__1(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__0, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__0_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__0);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0));
v___x_707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___x_705_);
lean_ctor_set(v___x_707_, 2, v___x_704_);
return v___x_707_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_708_ = lean_box(0);
v___x_709_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2));
v___x_710_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__1, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__1_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__1);
v___x_711_ = lean_box(2);
v___x_712_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_710_);
lean_ctor_set(v___x_712_, 2, v___x_709_);
lean_ctor_set(v___x_712_, 3, v___x_708_);
return v___x_712_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__2, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__2_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2);
v___x_714_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
v___x_715_ = lean_array_push(v___x_714_, v___x_713_);
return v___x_715_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__3, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__3_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3);
v___x_717_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
v___x_718_ = lean_box(2);
v___x_719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
lean_ctor_set(v___x_719_, 2, v___x_716_);
return v___x_719_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__5(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__4, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__4_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4);
v___x_721_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_722_ = lean_array_push(v___x_721_, v___x_720_);
return v___x_722_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__6));
v___x_725_ = l_Lean_mkAtom(v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__7, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7);
v___x_727_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__5, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__5_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__5);
v___x_728_ = lean_array_push(v___x_727_, v___x_726_);
return v___x_728_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41);
v___x_730_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__8, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__8_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8);
v___x_731_ = lean_array_push(v___x_730_, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__10(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__7, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7);
v___x_733_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9);
v___x_734_ = lean_array_push(v___x_733_, v___x_732_);
return v___x_734_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__12(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__11));
v___x_737_ = lean_string_utf8_byte_size(v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__13(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_738_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__12, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__12_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__12);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__11));
v___x_741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
lean_ctor_set(v___x_741_, 2, v___x_738_);
return v___x_741_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_744_ = lean_box(0);
v___x_745_ = ((lean_object*)(l_LawfulGetElem_getElem_x21__def___autoParam___closed__14));
v___x_746_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__13, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__13_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__13);
v___x_747_ = lean_box(2);
v___x_748_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v___x_746_);
lean_ctor_set(v___x_748_, 2, v___x_745_);
lean_ctor_set(v___x_748_, 3, v___x_744_);
return v___x_748_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__15, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__15_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15);
v___x_750_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36);
v___x_751_ = lean_array_push(v___x_750_, v___x_749_);
return v___x_751_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_752_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__16, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__16_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16);
v___x_753_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35));
v___x_754_ = lean_box(2);
v___x_755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___x_753_);
lean_ctor_set(v___x_755_, 2, v___x_752_);
return v___x_755_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__17, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__17_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17);
v___x_757_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__10, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__10);
v___x_758_ = lean_array_push(v___x_757_, v___x_756_);
return v___x_758_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_759_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__18, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__18_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18);
v___x_760_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_761_ = lean_box(2);
v___x_762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v___x_760_);
lean_ctor_set(v___x_762_, 2, v___x_759_);
return v___x_762_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__19, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__19_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19);
v___x_764_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33);
v___x_765_ = lean_array_push(v___x_764_, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45);
v___x_767_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__20, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__20_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20);
v___x_768_ = lean_array_push(v___x_767_, v___x_766_);
return v___x_768_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_769_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__21, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__21_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21);
v___x_770_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_771_ = lean_box(2);
v___x_772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v___x_770_);
lean_ctor_set(v___x_772_, 2, v___x_769_);
return v___x_772_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__22, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__22_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22);
v___x_774_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31);
v___x_775_ = lean_array_push(v___x_774_, v___x_773_);
return v___x_775_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5));
v___x_777_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__23, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__23_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23);
v___x_778_ = lean_array_push(v___x_777_, v___x_776_);
return v___x_778_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_779_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__24, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__24_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24);
v___x_780_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18));
v___x_781_ = lean_box(2);
v___x_782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v___x_780_);
lean_ctor_set(v___x_782_, 2, v___x_779_);
return v___x_782_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__25, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__25_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25);
v___x_784_ = lean_obj_once(&l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9, &l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once, _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9);
v___x_785_ = lean_array_push(v___x_784_, v___x_783_);
return v___x_785_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_786_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__26, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__26_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26);
v___x_787_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_788_ = lean_box(2);
v___x_789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___x_787_);
lean_ctor_set(v___x_789_, 2, v___x_786_);
return v___x_789_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__27, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__27_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27);
v___x_791_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_792_ = lean_array_push(v___x_791_, v___x_790_);
return v___x_792_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_793_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__28, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__28_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28);
v___x_794_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_795_ = lean_box(2);
v___x_796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___x_794_);
lean_ctor_set(v___x_796_, 2, v___x_793_);
return v___x_796_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__30(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__29, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__29_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29);
v___x_798_ = ((lean_object*)(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0));
v___x_799_ = lean_array_push(v___x_798_, v___x_797_);
return v___x_799_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__31(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_800_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__30, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__30_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__30);
v___x_801_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_802_ = lean_box(2);
v___x_803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
lean_ctor_set(v___x_803_, 2, v___x_800_);
return v___x_803_;
}
}
static lean_object* _init_l_LawfulGetElem_getElem_x21__def___autoParam(void){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = lean_obj_once(&l_LawfulGetElem_getElem_x21__def___autoParam___closed__31, &l_LawfulGetElem_getElem_x21__def___autoParam___closed__31_once, _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__31);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter___redArg(lean_object* v_x_805_, lean_object* v_h__1_806_, lean_object* v_h__2_807_){
_start:
{
if (lean_obj_tag(v_x_805_) == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_h__1_806_);
v___x_808_ = lean_box(0);
v___x_809_ = lean_apply_1(v_h__2_807_, v___x_808_);
return v___x_809_;
}
else
{
lean_object* v_val_810_; lean_object* v___x_811_; 
lean_dec(v_h__2_807_);
v_val_810_ = lean_ctor_get(v_x_805_, 0);
lean_inc(v_val_810_);
lean_dec_ref(v_x_805_);
v___x_811_ = lean_apply_1(v_h__1_806_, v_val_810_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter(lean_object* v_elem_812_, lean_object* v_motive_813_, lean_object* v_x_814_, lean_object* v_h__1_815_, lean_object* v_h__2_816_){
_start:
{
if (lean_obj_tag(v_x_814_) == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec(v_h__1_815_);
v___x_817_ = lean_box(0);
v___x_818_ = lean_apply_1(v_h__2_816_, v___x_817_);
return v___x_818_;
}
else
{
lean_object* v_val_819_; lean_object* v___x_820_; 
lean_dec(v_h__2_816_);
v_val_819_ = lean_ctor_get(v_x_814_, 0);
lean_inc(v_val_819_);
lean_dec_ref(v_x_814_);
v___x_820_ = lean_apply_1(v_h__1_815_, v_val_819_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___redArg___lam__0(lean_object* v_inst_821_, lean_object* v_xs_822_, lean_object* v_i_823_, lean_object* v_h_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = lean_apply_3(v_inst_821_, v_xs_822_, v_i_823_, lean_box(0));
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___redArg(lean_object* v_inst_826_){
_start:
{
lean_object* v___f_827_; 
v___f_827_ = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(v___f_827_, 0, v_inst_826_);
return v___f_827_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal(lean_object* v_cont_828_, lean_object* v_elem_829_, lean_object* v_dom_830_, lean_object* v_n_831_, lean_object* v_inst_832_){
_start:
{
lean_object* v___f_833_; 
v___f_833_ = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(v___f_833_, 0, v_inst_832_);
return v___f_833_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElemFinVal___boxed(lean_object* v_cont_834_, lean_object* v_elem_835_, lean_object* v_dom_836_, lean_object* v_n_837_, lean_object* v_inst_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Fin_instGetElemFinVal(v_cont_834_, v_elem_835_, v_dom_836_, v_n_837_, v_inst_838_);
lean_dec(v_n_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg___lam__0(lean_object* v_getElem_x3f_840_, lean_object* v_xs_841_, lean_object* v_i_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = lean_apply_2(v_getElem_x3f_840_, v_xs_841_, v_i_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg___lam__1(lean_object* v_getElem_x21_844_, lean_object* v_inst_845_, lean_object* v_xs_846_, lean_object* v_i_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = lean_apply_3(v_getElem_x21_844_, v_inst_845_, v_xs_846_, v_i_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___redArg(lean_object* v_inst_849_){
_start:
{
lean_object* v_toGetElem_850_; lean_object* v_getElem_x3f_851_; lean_object* v_getElem_x21_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_862_; 
v_toGetElem_850_ = lean_ctor_get(v_inst_849_, 0);
v_getElem_x3f_851_ = lean_ctor_get(v_inst_849_, 1);
v_getElem_x21_852_ = lean_ctor_get(v_inst_849_, 2);
v_isSharedCheck_862_ = !lean_is_exclusive(v_inst_849_);
if (v_isSharedCheck_862_ == 0)
{
v___x_854_ = v_inst_849_;
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_getElem_x21_852_);
lean_inc(v_getElem_x3f_851_);
lean_inc(v_toGetElem_850_);
lean_dec(v_inst_849_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___f_856_; lean_object* v___f_857_; lean_object* v___f_858_; lean_object* v___x_860_; 
v___f_856_ = lean_alloc_closure((void*)(l_Fin_instGetElem_x3fFinVal___redArg___lam__0), 3, 1);
lean_closure_set(v___f_856_, 0, v_getElem_x3f_851_);
v___f_857_ = lean_alloc_closure((void*)(l_Fin_instGetElem_x3fFinVal___redArg___lam__1), 4, 1);
lean_closure_set(v___f_857_, 0, v_getElem_x21_852_);
v___f_858_ = lean_alloc_closure((void*)(l_Fin_instGetElemFinVal___redArg___lam__0), 4, 1);
lean_closure_set(v___f_858_, 0, v_toGetElem_850_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 2, v___f_857_);
lean_ctor_set(v___x_854_, 1, v___f_856_);
lean_ctor_set(v___x_854_, 0, v___f_858_);
v___x_860_ = v___x_854_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___f_858_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___f_856_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v___f_857_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal(lean_object* v_cont_863_, lean_object* v_elem_864_, lean_object* v_dom_865_, lean_object* v_n_866_, lean_object* v_inst_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Fin_instGetElem_x3fFinVal___redArg(v_inst_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Fin_instGetElem_x3fFinVal___boxed(lean_object* v_cont_869_, lean_object* v_elem_870_, lean_object* v_dom_871_, lean_object* v_n_872_, lean_object* v_inst_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Fin_instGetElem_x3fFinVal(v_cont_869_, v_elem_870_, v_dom_871_, v_n_872_, v_inst_873_);
lean_dec(v_n_872_);
return v_res_874_;
}
}
static lean_object* _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10));
v___x_904_ = l_String_toRawSubstring_x27(v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(lean_object* v_x_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1));
v___x_928_ = l_Lean_Syntax_isOfKind(v_x_924_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_box(1);
v___x_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v_a_926_);
return v___x_930_;
}
else
{
lean_object* v_quotContext_931_; lean_object* v_currMacroScope_932_; lean_object* v_ref_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_quotContext_931_ = lean_ctor_get(v_a_925_, 1);
v_currMacroScope_932_ = lean_ctor_get(v_a_925_, 2);
v_ref_933_ = lean_ctor_get(v_a_925_, 5);
v___x_934_ = 0;
v___x_935_ = l_Lean_SourceInfo_fromRef(v_ref_933_, v___x_934_);
v___x_936_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3));
v___x_937_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13));
v___x_938_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4));
v___x_939_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18));
lean_inc_n(v___x_935_, 20);
v___x_940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_935_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30));
v___x_942_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32));
v___x_943_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6));
v___x_944_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7));
v___x_945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_935_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8));
v___x_947_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9));
v___x_948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_935_);
lean_ctor_set(v___x_948_, 1, v___x_946_);
v___x_949_ = lean_obj_once(&l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11, &l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_once, _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11);
v___x_950_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14));
lean_inc(v_currMacroScope_932_);
lean_inc(v_quotContext_931_);
v___x_951_ = l_Lean_addMacroScope(v_quotContext_931_, v___x_950_, v_currMacroScope_932_);
v___x_952_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16));
v___x_953_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_953_, 0, v___x_935_);
lean_ctor_set(v___x_953_, 1, v___x_949_);
lean_ctor_set(v___x_953_, 2, v___x_951_);
lean_ctor_set(v___x_953_, 3, v___x_952_);
v___x_954_ = l_Lean_Syntax_node2(v___x_935_, v___x_947_, v___x_948_, v___x_953_);
v___x_955_ = l_Lean_Syntax_node1(v___x_935_, v___x_937_, v___x_954_);
v___x_956_ = l_Lean_Syntax_node1(v___x_935_, v___x_942_, v___x_955_);
v___x_957_ = l_Lean_Syntax_node1(v___x_935_, v___x_941_, v___x_956_);
v___x_958_ = l_Lean_Syntax_node2(v___x_935_, v___x_943_, v___x_945_, v___x_957_);
v___x_959_ = l_Lean_Syntax_node1(v___x_935_, v___x_937_, v___x_958_);
v___x_960_ = l_Lean_Syntax_node1(v___x_935_, v___x_942_, v___x_959_);
v___x_961_ = l_Lean_Syntax_node1(v___x_935_, v___x_941_, v___x_960_);
v___x_962_ = ((lean_object*)(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36));
v___x_963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_935_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Lean_Syntax_node3(v___x_935_, v___x_938_, v___x_940_, v___x_961_, v___x_963_);
v___x_965_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17));
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_935_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18));
v___x_968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_935_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_Syntax_node1(v___x_935_, v___x_927_, v___x_968_);
v___x_970_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19));
v___x_971_ = ((lean_object*)(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20));
v___x_972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_935_);
lean_ctor_set(v___x_972_, 1, v___x_970_);
v___x_973_ = l_Lean_Syntax_node1(v___x_935_, v___x_971_, v___x_972_);
lean_inc_ref(v___x_966_);
v___x_974_ = l_Lean_Syntax_node5(v___x_935_, v___x_937_, v___x_964_, v___x_966_, v___x_969_, v___x_966_, v___x_973_);
v___x_975_ = l_Lean_Syntax_node1(v___x_935_, v___x_936_, v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v_a_926_);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___boxed(lean_object* v_x_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(v_x_977_, v_a_978_, v_a_979_);
lean_dec_ref(v_a_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___lam__0(lean_object* v_as_981_, lean_object* v_i_982_, lean_object* v_h_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_List_get___redArg(v_as_981_, v_i_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength___lam__0___boxed(lean_object* v_as_985_, lean_object* v_i_986_, lean_object* v_h_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_List_instGetElemNatLtLength___lam__0(v_as_985_, v_i_986_, v_h_987_);
lean_dec(v_as_985_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_List_instGetElemNatLtLength(lean_object* v_00_u03b1_990_){
_start:
{
lean_object* v___f_991_; 
v___f_991_ = ((lean_object*)(l_List_instGetElemNatLtLength___closed__0));
return v___f_991_;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___redArg(lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
if (lean_obj_tag(v_x_992_) == 1)
{
lean_object* v_head_994_; lean_object* v_tail_995_; lean_object* v_zero_996_; uint8_t v_isZero_997_; 
v_head_994_ = lean_ctor_get(v_x_992_, 0);
v_tail_995_ = lean_ctor_get(v_x_992_, 1);
v_zero_996_ = lean_unsigned_to_nat(0u);
v_isZero_997_ = lean_nat_dec_eq(v_x_993_, v_zero_996_);
if (v_isZero_997_ == 1)
{
lean_object* v___x_998_; 
lean_dec(v_x_993_);
lean_inc(v_head_994_);
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v_head_994_);
return v___x_998_;
}
else
{
lean_object* v_one_999_; lean_object* v_n_1000_; 
v_one_999_ = lean_unsigned_to_nat(1u);
v_n_1000_ = lean_nat_sub(v_x_993_, v_one_999_);
lean_dec(v_x_993_);
v_x_992_ = v_tail_995_;
v_x_993_ = v_n_1000_;
goto _start;
}
}
else
{
lean_object* v___x_1002_; 
lean_dec(v_x_993_);
v___x_1002_ = lean_box(0);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___redArg___boxed(lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_List_get_x3fInternal___redArg(v_x_1003_, v_x_1004_);
lean_dec(v_x_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal(lean_object* v_00_u03b1_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_List_get_x3fInternal___redArg(v_x_1007_, v_x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_List_get_x3fInternal___boxed(lean_object* v_00_u03b1_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_List_get_x3fInternal(v_00_u03b1_1010_, v_x_1011_, v_x_1012_);
lean_dec(v_x_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___redArg(lean_object* v_inst_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_){
_start:
{
if (lean_obj_tag(v_x_1017_) == 1)
{
lean_object* v_head_1019_; lean_object* v_tail_1020_; lean_object* v_zero_1021_; uint8_t v_isZero_1022_; 
v_head_1019_ = lean_ctor_get(v_x_1017_, 0);
v_tail_1020_ = lean_ctor_get(v_x_1017_, 1);
v_zero_1021_ = lean_unsigned_to_nat(0u);
v_isZero_1022_ = lean_nat_dec_eq(v_x_1018_, v_zero_1021_);
if (v_isZero_1022_ == 1)
{
lean_dec(v_x_1018_);
lean_inc(v_head_1019_);
return v_head_1019_;
}
else
{
lean_object* v_one_1023_; lean_object* v_n_1024_; 
v_one_1023_ = lean_unsigned_to_nat(1u);
v_n_1024_ = lean_nat_sub(v_x_1018_, v_one_1023_);
lean_dec(v_x_1018_);
v_x_1017_ = v_tail_1020_;
v_x_1018_ = v_n_1024_;
goto _start;
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec(v_x_1018_);
v___x_1026_ = ((lean_object*)(l_outOfBounds___redArg___closed__0));
v___x_1027_ = ((lean_object*)(l_List_get_x21Internal___redArg___closed__0));
v___x_1028_ = lean_unsigned_to_nat(335u);
v___x_1029_ = lean_unsigned_to_nat(18u);
v___x_1030_ = ((lean_object*)(l_List_get_x21Internal___redArg___closed__1));
v___x_1031_ = l_mkPanicMessageWithDecl(v___x_1026_, v___x_1027_, v___x_1028_, v___x_1029_, v___x_1030_);
v___x_1032_ = l_panic___redArg(v_inst_1016_, v___x_1031_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___redArg___boxed(lean_object* v_inst_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_List_get_x21Internal___redArg(v_inst_1033_, v_x_1034_, v_x_1035_);
lean_dec(v_x_1034_);
lean_dec(v_inst_1033_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal(lean_object* v_00_u03b1_1037_, lean_object* v_inst_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_List_get_x21Internal___redArg(v_inst_1038_, v_x_1039_, v_x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_List_get_x21Internal___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_inst_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_List_get_x21Internal(v_00_u03b1_1042_, v_inst_1043_, v_x_1044_, v_x_1045_);
lean_dec(v_x_1044_);
lean_dec(v_inst_1043_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_List_instGetElem_x3fNatLtLength(lean_object* v_00_u03b1_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = ((lean_object*)(l_List_instGetElem_x3fNatLtLength___closed__2));
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___lam__0(lean_object* v_xs_1055_, lean_object* v_i_1056_, lean_object* v_h_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_array_fget_borrowed(v_xs_1055_, v_i_1056_);
lean_inc(v___x_1058_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize___lam__0___boxed(lean_object* v_xs_1059_, lean_object* v_i_1060_, lean_object* v_h_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Array_instGetElemNatLtSize___lam__0(v_xs_1059_, v_i_1060_, v_h_1061_);
lean_dec(v_i_1060_);
lean_dec_ref(v_xs_1059_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemNatLtSize(lean_object* v_00_u03b1_1064_){
_start:
{
lean_object* v___f_1065_; 
v___f_1065_ = ((lean_object*)(l_Array_instGetElemNatLtSize___closed__0));
return v___f_1065_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__0(lean_object* v_xs_1066_, lean_object* v_i_1067_){
_start:
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = lean_array_get_size(v_xs_1066_);
v___x_1069_ = lean_nat_dec_lt(v_i_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_box(0);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_array_fget_borrowed(v_xs_1066_, v_i_1067_);
lean_inc(v___x_1071_);
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__0___boxed(lean_object* v_xs_1073_, lean_object* v_i_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Array_instGetElem_x3fNatLtSize___lam__0(v_xs_1073_, v_i_1074_);
lean_dec(v_i_1074_);
lean_dec_ref(v_xs_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__1(lean_object* v_inst_1076_, lean_object* v_xs_1077_, lean_object* v_i_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_array_get_borrowed(v_inst_1076_, v_xs_1077_, v_i_1078_);
lean_inc(v___x_1079_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize___lam__1___boxed(lean_object* v_inst_1080_, lean_object* v_xs_1081_, lean_object* v_i_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Array_instGetElem_x3fNatLtSize___lam__1(v_inst_1080_, v_xs_1081_, v_i_1082_);
lean_dec(v_i_1082_);
lean_dec_ref(v_xs_1081_);
lean_dec(v_inst_1080_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElem_x3fNatLtSize(lean_object* v_00_u03b1_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = ((lean_object*)(l_Array_instGetElem_x3fNatLtSize___closed__2));
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instGetElemNatTrue___lam__0(lean_object* v_stx_1092_, lean_object* v_i_1093_, lean_object* v_x_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Syntax_getArg(v_stx_1092_, v_i_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instGetElemNatTrue___lam__0___boxed(lean_object* v_stx_1096_, lean_object* v_i_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Syntax_instGetElemNatTrue___lam__0(v_stx_1096_, v_i_1097_, v_x_1098_);
lean_dec(v_i_1097_);
lean_dec(v_stx_1096_);
return v_res_1099_;
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
