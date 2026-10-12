// Lean compiler output
// Module: Std.Do.SPred.Notation.Basic
// Imports: public import Std.Do.SPred.SPred
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
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_termSpred_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__0 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__0_value;
static const lean_string_object l_Std_Do_termSpred_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__1 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__1_value;
static const lean_string_object l_Std_Do_termSpred_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termSpred(_)"};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__2 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__2_value;
static const lean_ctor_object l_Std_Do_termSpred_x28___x29___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_termSpred_x28___x29___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__3_value_aux_0),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_termSpred_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__3_value_aux_1),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 240, 91, 148, 237, 191, 255, 193)}};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__3 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__3_value;
static const lean_string_object l_Std_Do_termSpred_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__4 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__4_value;
static const lean_ctor_object l_Std_Do_termSpred_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__5 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__5_value;
static const lean_string_object l_Std_Do_termSpred_x28___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "spred("};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__6 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__6_value;
static const lean_ctor_object l_Std_Do_termSpred_x28___x29___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__6_value)}};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__7 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__7_value;
static const lean_string_object l_Std_Do_termSpred_x28___x29___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__8 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__8_value;
static const lean_ctor_object l_Std_Do_termSpred_x28___x29___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__9 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__9_value;
static const lean_ctor_object l_Std_Do_termSpred_x28___x29___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__10 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__10_value;
static const lean_ctor_object l_Std_Do_termSpred_x28___x29___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__5_value),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__7_value),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__10_value)}};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__11 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__11_value;
static const lean_string_object l_Std_Do_termSpred_x28___x29___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__12 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__12_value;
static const lean_ctor_object l_Std_Do_termSpred_x28___x29___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__12_value)}};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__13 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__13_value;
static const lean_ctor_object l_Std_Do_termSpred_x28___x29___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__5_value),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__11_value),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__13_value)}};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__14 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__14_value;
static const lean_ctor_object l_Std_Do_termSpred_x28___x29___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__3_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__14_value)}};
static const lean_object* l_Std_Do_termSpred_x28___x29___closed__15 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__15_value;
LEAN_EXPORT const lean_object* l_Std_Do_termSpred_x28___x29 = (const lean_object*)&l_Std_Do_termSpred_x28___x29___closed__15_value;
static const lean_string_object l_Std_Do_termTerm_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "termTerm(_)"};
static const lean_object* l_Std_Do_termTerm_x28___x29___closed__0 = (const lean_object*)&l_Std_Do_termTerm_x28___x29___closed__0_value;
static const lean_ctor_object l_Std_Do_termTerm_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_termTerm_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_termTerm_x28___x29___closed__1_value_aux_0),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_termTerm_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_termTerm_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Std_Do_termTerm_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 176, 69, 25, 99, 246, 131, 165)}};
static const lean_object* l_Std_Do_termTerm_x28___x29___closed__1 = (const lean_object*)&l_Std_Do_termTerm_x28___x29___closed__1_value;
static const lean_string_object l_Std_Do_termTerm_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "term("};
static const lean_object* l_Std_Do_termTerm_x28___x29___closed__2 = (const lean_object*)&l_Std_Do_termTerm_x28___x29___closed__2_value;
static const lean_ctor_object l_Std_Do_termTerm_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_termTerm_x28___x29___closed__2_value)}};
static const lean_object* l_Std_Do_termTerm_x28___x29___closed__3 = (const lean_object*)&l_Std_Do_termTerm_x28___x29___closed__3_value;
static const lean_ctor_object l_Std_Do_termTerm_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__5_value),((lean_object*)&l_Std_Do_termTerm_x28___x29___closed__3_value),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__10_value)}};
static const lean_object* l_Std_Do_termTerm_x28___x29___closed__4 = (const lean_object*)&l_Std_Do_termTerm_x28___x29___closed__4_value;
static const lean_ctor_object l_Std_Do_termTerm_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__5_value),((lean_object*)&l_Std_Do_termTerm_x28___x29___closed__4_value),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__13_value)}};
static const lean_object* l_Std_Do_termTerm_x28___x29___closed__5 = (const lean_object*)&l_Std_Do_termTerm_x28___x29___closed__5_value;
static const lean_ctor_object l_Std_Do_termTerm_x28___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Do_termTerm_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Do_termTerm_x28___x29___closed__5_value)}};
static const lean_object* l_Std_Do_termTerm_x28___x29___closed__6 = (const lean_object*)&l_Std_Do_termTerm_x28___x29___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Do_termTerm_x28___x29 = (const lean_object*)&l_Std_Do_termTerm_x28___x29___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value_aux_0),((lean_object*)&l_Std_Do_termSpred_x28___x29___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19_value),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__3(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__0_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Notation"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__1 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1___redArg(lean_object* v_x_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__3));
lean_inc(v_x_57_);
v___x_60_ = l_Lean_Syntax_isOfKind(v_x_57_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_x_57_);
v___x_61_ = lean_box(1);
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v_a_58_);
return v___x_62_;
}
else
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = l_Lean_Syntax_getArg(v_x_57_, v___x_63_);
lean_dec(v_x_57_);
v___x_65_ = ((lean_object*)(l_Std_Do_termTerm_x28___x29___closed__1));
lean_inc(v___x_64_);
v___x_66_ = l_Lean_Syntax_isOfKind(v___x_64_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; 
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_64_);
lean_ctor_set(v___x_67_, 1, v_a_58_);
return v___x_67_;
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = l_Lean_Syntax_getArg(v___x_64_, v___x_63_);
lean_dec(v___x_64_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v_a_58_);
return v___x_69_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1(lean_object* v_x_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1___redArg(v_x_70_, v_a_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1___boxed(lean_object* v_x_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1(v_x_74_, v_a_75_, v_a_76_);
lean_dec_ref(v_a_75_);
return v_res_77_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16));
v___x_114_ = l_String_toRawSubstring_x27(v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43(void){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Array_mkArray0___redArg();
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2(lean_object* v_x_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__3));
lean_inc(v_x_171_);
v___x_175_ = l_Lean_Syntax_isOfKind(v_x_171_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_x_171_);
v___x_176_ = lean_box(1);
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v_a_173_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = l_Lean_Syntax_getArg(v_x_171_, v___x_179_);
lean_dec(v_x_171_);
v___x_181_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4));
lean_inc(v___x_180_);
v___x_182_ = l_Lean_Syntax_isOfKind(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_183_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5));
v___x_184_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6));
lean_inc(v___x_180_);
v___x_185_ = l_Lean_Syntax_isOfKind(v___x_180_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8));
lean_inc(v___x_180_);
v___x_187_ = l_Lean_Syntax_isOfKind(v___x_180_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10));
lean_inc(v___x_180_);
v___x_189_ = l_Lean_Syntax_isOfKind(v___x_180_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v___x_180_);
v___x_190_ = lean_box(1);
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_a_173_);
return v___x_191_;
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_192_ = l_Lean_Syntax_getArg(v___x_180_, v___x_178_);
v___x_193_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12));
lean_inc(v___x_192_);
v___x_194_ = l_Lean_Syntax_isOfKind(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v___x_192_);
lean_dec(v___x_180_);
v___x_195_ = lean_box(1);
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_173_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_197_ = l_Lean_Syntax_getArg(v___x_192_, v___x_179_);
lean_dec(v___x_192_);
v___x_198_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14));
lean_inc(v___x_197_);
v___x_199_ = l_Lean_Syntax_isOfKind(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v___x_197_);
lean_dec(v___x_180_);
v___x_200_ = lean_box(1);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_a_173_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_202_ = l_Lean_Syntax_getArg(v___x_197_, v___x_178_);
lean_dec(v___x_197_);
v___x_203_ = lean_box(0);
v___x_204_ = l_Lean_Syntax_matchesIdent(v___x_202_, v___x_203_);
lean_dec(v___x_202_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v___x_180_);
v___x_205_ = lean_box(1);
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v_a_173_);
return v___x_206_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_207_ = lean_unsigned_to_nat(3u);
v___x_208_ = l_Lean_Syntax_getArg(v___x_180_, v___x_207_);
lean_inc(v___x_208_);
v___x_209_ = l_Lean_Syntax_matchesNull(v___x_208_, v___x_179_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v___x_208_);
lean_dec(v___x_180_);
v___x_210_ = lean_box(1);
v___x_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v_a_173_);
return v___x_211_;
}
else
{
lean_object* v_quotContext_212_; lean_object* v_currMacroScope_213_; lean_object* v_ref_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_quotContext_212_ = lean_ctor_get(v_a_172_, 1);
v_currMacroScope_213_ = lean_ctor_get(v_a_172_, 2);
v_ref_214_ = lean_ctor_get(v_a_172_, 5);
v___x_215_ = l_Lean_Syntax_getArg(v___x_180_, v___x_179_);
lean_dec(v___x_180_);
v___x_216_ = l_Lean_Syntax_getArg(v___x_208_, v___x_178_);
lean_dec(v___x_208_);
v___x_217_ = l_Lean_SourceInfo_fromRef(v_ref_214_, v___x_187_);
v___x_218_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15));
lean_inc_n(v___x_217_, 9);
v___x_219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
lean_inc(v_currMacroScope_213_);
lean_inc(v_quotContext_212_);
v___x_221_ = l_Lean_addMacroScope(v_quotContext_212_, v___x_203_, v_currMacroScope_213_);
v___x_222_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34));
v___x_223_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_223_, 0, v___x_217_);
lean_ctor_set(v___x_223_, 1, v___x_220_);
lean_ctor_set(v___x_223_, 2, v___x_221_);
lean_ctor_set(v___x_223_, 3, v___x_222_);
v___x_224_ = l_Lean_Syntax_node1(v___x_217_, v___x_198_, v___x_223_);
v___x_225_ = l_Lean_Syntax_node2(v___x_217_, v___x_193_, v___x_219_, v___x_224_);
v___x_226_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__6));
v___x_227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_217_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
v___x_229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_217_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
lean_inc_ref(v___x_229_);
v___x_230_ = l_Lean_Syntax_node3(v___x_217_, v___x_174_, v___x_227_, v___x_215_, v___x_229_);
v___x_231_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35));
v___x_232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_217_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37));
v___x_234_ = l_Lean_Syntax_node1(v___x_217_, v___x_233_, v___x_216_);
v___x_235_ = l_Lean_Syntax_node5(v___x_217_, v___x_188_, v___x_225_, v___x_230_, v___x_232_, v___x_234_, v___x_229_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_a_173_);
return v___x_236_;
}
}
}
}
}
}
else
{
lean_object* v_ref_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_ref_237_ = lean_ctor_get(v_a_172_, 5);
v___x_238_ = l_Lean_Syntax_getArg(v___x_180_, v___x_179_);
v___x_239_ = lean_unsigned_to_nat(3u);
v___x_240_ = l_Lean_Syntax_getArg(v___x_180_, v___x_239_);
v___x_241_ = lean_unsigned_to_nat(5u);
v___x_242_ = l_Lean_Syntax_getArg(v___x_180_, v___x_241_);
lean_dec(v___x_180_);
v___x_243_ = l_Lean_SourceInfo_fromRef(v_ref_237_, v___x_185_);
v___x_244_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38));
lean_inc_n(v___x_243_, 7);
v___x_245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39));
v___x_247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_243_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__6));
v___x_249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_243_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
v___x_251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_243_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
lean_inc_ref(v___x_251_);
lean_inc_ref(v___x_249_);
v___x_252_ = l_Lean_Syntax_node3(v___x_243_, v___x_174_, v___x_249_, v___x_240_, v___x_251_);
v___x_253_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40));
v___x_254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_243_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = l_Lean_Syntax_node3(v___x_243_, v___x_174_, v___x_249_, v___x_242_, v___x_251_);
v___x_256_ = l_Lean_Syntax_node6(v___x_243_, v___x_186_, v___x_245_, v___x_238_, v___x_247_, v___x_252_, v___x_254_, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v_a_173_);
return v___x_257_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_258_ = l_Lean_Syntax_getArg(v___x_180_, v___x_179_);
lean_dec(v___x_180_);
v___x_259_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42));
lean_inc(v___x_258_);
v___x_260_ = l_Lean_Syntax_isOfKind(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec(v___x_258_);
v___x_261_ = lean_box(1);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v_a_173_);
return v___x_262_;
}
else
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = l_Lean_Syntax_getArg(v___x_258_, v___x_179_);
v___x_264_ = l_Lean_Syntax_matchesNull(v___x_263_, v___x_178_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v___x_258_);
v___x_265_ = lean_box(1);
v___x_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_a_173_);
return v___x_266_;
}
else
{
lean_object* v_ref_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_xs_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_ref_267_ = lean_ctor_get(v_a_172_, 5);
v___x_268_ = l_Lean_Syntax_getArg(v___x_258_, v___x_178_);
v___x_269_ = lean_unsigned_to_nat(3u);
v___x_270_ = l_Lean_Syntax_getArg(v___x_258_, v___x_269_);
lean_dec(v___x_258_);
v_xs_271_ = l_Lean_Syntax_getArgs(v___x_268_);
lean_dec(v___x_268_);
v___x_272_ = l_Lean_SourceInfo_fromRef(v_ref_267_, v___x_182_);
lean_inc_n(v___x_272_, 8);
v___x_273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_183_);
v___x_274_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37));
v___x_275_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43);
v___x_276_ = l_Array_append___redArg(v___x_275_, v_xs_271_);
lean_dec_ref(v_xs_271_);
v___x_277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_277_, 0, v___x_272_);
lean_ctor_set(v___x_277_, 1, v___x_274_);
lean_ctor_set(v___x_277_, 2, v___x_276_);
v___x_278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_278_, 0, v___x_272_);
lean_ctor_set(v___x_278_, 1, v___x_274_);
lean_ctor_set(v___x_278_, 2, v___x_275_);
v___x_279_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44));
v___x_280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_272_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__6));
v___x_282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_272_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
v___x_284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_272_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_Lean_Syntax_node3(v___x_272_, v___x_174_, v___x_282_, v___x_270_, v___x_284_);
v___x_286_ = l_Lean_Syntax_node4(v___x_272_, v___x_259_, v___x_277_, v___x_278_, v___x_280_, v___x_285_);
v___x_287_ = l_Lean_Syntax_node2(v___x_272_, v___x_184_, v___x_273_, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_a_173_);
return v___x_288_;
}
}
}
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = l_Lean_Syntax_getArg(v___x_180_, v___x_178_);
v___x_290_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12));
lean_inc(v___x_289_);
v___x_291_ = l_Lean_Syntax_isOfKind(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec(v___x_289_);
lean_dec(v___x_180_);
v___x_292_ = lean_box(1);
v___x_293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_a_173_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = l_Lean_Syntax_getArg(v___x_289_, v___x_179_);
lean_dec(v___x_289_);
v___x_295_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14));
lean_inc(v___x_294_);
v___x_296_ = l_Lean_Syntax_isOfKind(v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v___x_294_);
lean_dec(v___x_180_);
v___x_297_ = lean_box(1);
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_a_173_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_299_ = l_Lean_Syntax_getArg(v___x_294_, v___x_178_);
lean_dec(v___x_294_);
v___x_300_ = lean_box(0);
v___x_301_ = l_Lean_Syntax_matchesIdent(v___x_299_, v___x_300_);
lean_dec(v___x_299_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v___x_180_);
v___x_302_ = lean_box(1);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_a_173_);
return v___x_303_;
}
else
{
lean_object* v_quotContext_304_; lean_object* v_currMacroScope_305_; lean_object* v_ref_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_quotContext_304_ = lean_ctor_get(v_a_172_, 1);
v_currMacroScope_305_ = lean_ctor_get(v_a_172_, 2);
v_ref_306_ = lean_ctor_get(v_a_172_, 5);
v___x_307_ = l_Lean_Syntax_getArg(v___x_180_, v___x_179_);
lean_dec(v___x_180_);
v___x_308_ = 0;
v___x_309_ = l_Lean_SourceInfo_fromRef(v_ref_306_, v___x_308_);
v___x_310_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15));
lean_inc_n(v___x_309_, 7);
v___x_311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
lean_inc(v_currMacroScope_305_);
lean_inc(v_quotContext_304_);
v___x_313_ = l_Lean_addMacroScope(v_quotContext_304_, v___x_300_, v_currMacroScope_305_);
v___x_314_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34));
v___x_315_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_315_, 0, v___x_309_);
lean_ctor_set(v___x_315_, 1, v___x_312_);
lean_ctor_set(v___x_315_, 2, v___x_313_);
lean_ctor_set(v___x_315_, 3, v___x_314_);
v___x_316_ = l_Lean_Syntax_node1(v___x_309_, v___x_295_, v___x_315_);
v___x_317_ = l_Lean_Syntax_node2(v___x_309_, v___x_290_, v___x_311_, v___x_316_);
v___x_318_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__6));
v___x_319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_309_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
v___x_321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_309_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
lean_inc_ref(v___x_321_);
v___x_322_ = l_Lean_Syntax_node3(v___x_309_, v___x_174_, v___x_319_, v___x_307_, v___x_321_);
v___x_323_ = l_Lean_Syntax_node3(v___x_309_, v___x_181_, v___x_317_, v___x_322_, v___x_321_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_a_173_);
return v___x_324_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___boxed(lean_object* v_x_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2(v_x_325_, v_a_326_, v_a_327_);
lean_dec_ref(v_a_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__0(lean_object* v_toPure_329_, lean_object* v_x_330_, lean_object* v_quotCtx_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_apply_2(v_toPure_329_, lean_box(0), v_x_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed(lean_object* v_toPure_333_, lean_object* v_x_334_, lean_object* v_quotCtx_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__0(v_toPure_333_, v_x_334_, v_quotCtx_335_);
lean_dec(v_quotCtx_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__1(lean_object* v_inst_337_, lean_object* v_toBind_338_, lean_object* v___f_339_, lean_object* v_scp_340_){
_start:
{
lean_object* v_getContext_341_; lean_object* v___x_342_; 
v_getContext_341_ = lean_ctor_get(v_inst_337_, 2);
lean_inc(v_getContext_341_);
lean_dec_ref(v_inst_337_);
v___x_342_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v_getContext_341_, v___f_339_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed(lean_object* v_inst_343_, lean_object* v_toBind_344_, lean_object* v___f_345_, lean_object* v_scp_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__1(v_inst_343_, v_toBind_344_, v___f_345_, v_scp_346_);
lean_dec(v_scp_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__2(lean_object* v_inst_348_, lean_object* v_toBind_349_, lean_object* v___f_350_, lean_object* v_info_351_){
_start:
{
lean_object* v_getCurrMacroScope_352_; lean_object* v___x_353_; 
v_getCurrMacroScope_352_ = lean_ctor_get(v_inst_348_, 1);
lean_inc(v_getCurrMacroScope_352_);
lean_dec_ref(v_inst_348_);
v___x_353_ = lean_apply_4(v_toBind_349_, lean_box(0), lean_box(0), v_getCurrMacroScope_352_, v___f_350_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed(lean_object* v_inst_354_, lean_object* v_toBind_355_, lean_object* v___f_356_, lean_object* v_info_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__2(v_inst_354_, v_toBind_355_, v___f_356_, v_info_357_);
lean_dec(v_info_357_);
return v_res_358_;
}
}
lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__3(uint8_t v___x_359_, lean_object* v_toPure_360_, lean_object* v_____do__lift_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l_Lean_SourceInfo_fromRef(v_____do__lift_361_, v___x_359_);
v___x_363_ = lean_apply_2(v_toPure_360_, lean_box(0), v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT void l_Std_Do_SPred_Notation_unpack___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_359_ = stack[0].m_num;
lean_object* v_toPure_360_ = stack[1].m_obj;
lean_object* v_____do__lift_361_ = stack[2].m_obj;
lean_object* v_res_364_;
v_res_364_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__3(v___x_359_, v_toPure_360_, v_____do__lift_361_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed(lean_object* v___x_365_, lean_object* v_toPure_366_, lean_object* v_____do__lift_367_){
_start:
{
uint8_t v___x_1585__boxed_368_; lean_object* v_res_369_; 
v___x_1585__boxed_368_ = lean_unbox(v___x_365_);
v_res_369_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__3(v___x_1585__boxed_368_, v_toPure_366_, v_____do__lift_367_);
lean_dec(v_____do__lift_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__21(lean_object* v_info_372_, lean_object* v___x_373_, lean_object* v_scp_374_, lean_object* v___x_375_, lean_object* v___x_376_, lean_object* v___x_377_, lean_object* v___x_378_, lean_object* v___x_379_, lean_object* v___x_380_, lean_object* v___x_381_, lean_object* v___x_382_, lean_object* v_____do__lift_383_, lean_object* v_toPure_384_, lean_object* v_quotCtx_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_386_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15));
lean_inc_n(v_info_372_, 7);
v___x_387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_387_, 0, v_info_372_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
v___x_389_ = l_Lean_addMacroScope(v_quotCtx_385_, v___x_373_, v_scp_374_);
v___x_390_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__0));
v___x_391_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__1));
v___x_392_ = l_Lean_Name_mkStr4(v___x_375_, v___x_376_, v___x_390_, v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
v___x_394_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20));
lean_inc_ref_n(v___x_377_, 3);
v___x_395_ = l_Lean_Name_mkStr2(v___x_377_, v___x_394_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
v___x_397_ = l_Lean_Name_mkStr2(v___x_377_, v___x_378_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
v___x_399_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25));
v___x_400_ = l_Lean_Name_mkStr2(v___x_377_, v___x_399_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
v___x_402_ = l_Lean_Name_mkStr1(v___x_377_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_401_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_398_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_396_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_393_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_410_, 0, v_info_372_);
lean_ctor_set(v___x_410_, 1, v___x_388_);
lean_ctor_set(v___x_410_, 2, v___x_389_);
lean_ctor_set(v___x_410_, 3, v___x_409_);
v___x_411_ = l_Lean_Syntax_node1(v_info_372_, v___x_379_, v___x_410_);
v___x_412_ = l_Lean_Syntax_node2(v_info_372_, v___x_380_, v___x_387_, v___x_411_);
v___x_413_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35));
v___x_414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_414_, 0, v_info_372_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37));
v___x_416_ = l_Lean_Syntax_node1(v_info_372_, v___x_415_, v___x_381_);
v___x_417_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
v___x_418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_418_, 0, v_info_372_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = l_Lean_Syntax_node5(v_info_372_, v___x_382_, v___x_412_, v_____do__lift_383_, v___x_414_, v___x_416_, v___x_418_);
v___x_420_ = lean_apply_2(v_toPure_384_, lean_box(0), v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__4(lean_object* v_info_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v___x_426_, lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v_____do__lift_431_, lean_object* v_toPure_432_, lean_object* v_toBind_433_, lean_object* v_getContext_434_, lean_object* v_scp_435_){
_start:
{
lean_object* v___f_436_; lean_object* v___x_437_; 
v___f_436_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__21), 14, 13);
lean_closure_set(v___f_436_, 0, v_info_421_);
lean_closure_set(v___f_436_, 1, v___x_422_);
lean_closure_set(v___f_436_, 2, v_scp_435_);
lean_closure_set(v___f_436_, 3, v___x_423_);
lean_closure_set(v___f_436_, 4, v___x_424_);
lean_closure_set(v___f_436_, 5, v___x_425_);
lean_closure_set(v___f_436_, 6, v___x_426_);
lean_closure_set(v___f_436_, 7, v___x_427_);
lean_closure_set(v___f_436_, 8, v___x_428_);
lean_closure_set(v___f_436_, 9, v___x_429_);
lean_closure_set(v___f_436_, 10, v___x_430_);
lean_closure_set(v___f_436_, 11, v_____do__lift_431_);
lean_closure_set(v___f_436_, 12, v_toPure_432_);
v___x_437_ = lean_apply_4(v_toBind_433_, lean_box(0), lean_box(0), v_getContext_434_, v___f_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__5(lean_object* v_inst_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v___x_445_, lean_object* v___x_446_, lean_object* v___x_447_, lean_object* v_____do__lift_448_, lean_object* v_toPure_449_, lean_object* v_toBind_450_, lean_object* v_info_451_){
_start:
{
lean_object* v_getCurrMacroScope_452_; lean_object* v_getContext_453_; lean_object* v___f_454_; lean_object* v___x_455_; 
v_getCurrMacroScope_452_ = lean_ctor_get(v_inst_438_, 1);
lean_inc(v_getCurrMacroScope_452_);
v_getContext_453_ = lean_ctor_get(v_inst_438_, 2);
lean_inc(v_getContext_453_);
lean_dec_ref(v_inst_438_);
lean_inc(v_toBind_450_);
v___f_454_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__4), 15, 14);
lean_closure_set(v___f_454_, 0, v_info_451_);
lean_closure_set(v___f_454_, 1, v___x_439_);
lean_closure_set(v___f_454_, 2, v___x_440_);
lean_closure_set(v___f_454_, 3, v___x_441_);
lean_closure_set(v___f_454_, 4, v___x_442_);
lean_closure_set(v___f_454_, 5, v___x_443_);
lean_closure_set(v___f_454_, 6, v___x_444_);
lean_closure_set(v___f_454_, 7, v___x_445_);
lean_closure_set(v___f_454_, 8, v___x_446_);
lean_closure_set(v___f_454_, 9, v___x_447_);
lean_closure_set(v___f_454_, 10, v_____do__lift_448_);
lean_closure_set(v___f_454_, 11, v_toPure_449_);
lean_closure_set(v___f_454_, 12, v_toBind_450_);
lean_closure_set(v___f_454_, 13, v_getContext_453_);
v___x_455_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v_getCurrMacroScope_452_, v___f_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__6(lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v___x_458_, lean_object* v___x_459_, lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v___x_463_, lean_object* v___x_464_, lean_object* v___x_465_, lean_object* v___x_466_, lean_object* v_toPure_467_, lean_object* v_toBind_468_, lean_object* v___f_469_, lean_object* v_____do__lift_470_){
_start:
{
lean_object* v_getRef_471_; lean_object* v___f_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_getRef_471_ = lean_ctor_get(v_inst_456_, 0);
lean_inc(v_getRef_471_);
lean_dec_ref(v_inst_456_);
lean_inc_n(v_toBind_468_, 2);
v___f_472_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__5), 14, 13);
lean_closure_set(v___f_472_, 0, v_inst_457_);
lean_closure_set(v___f_472_, 1, v___x_458_);
lean_closure_set(v___f_472_, 2, v___x_459_);
lean_closure_set(v___f_472_, 3, v___x_460_);
lean_closure_set(v___f_472_, 4, v___x_461_);
lean_closure_set(v___f_472_, 5, v___x_462_);
lean_closure_set(v___f_472_, 6, v___x_463_);
lean_closure_set(v___f_472_, 7, v___x_464_);
lean_closure_set(v___f_472_, 8, v___x_465_);
lean_closure_set(v___f_472_, 9, v___x_466_);
lean_closure_set(v___f_472_, 10, v_____do__lift_470_);
lean_closure_set(v___f_472_, 11, v_toPure_467_);
lean_closure_set(v___f_472_, 12, v_toBind_468_);
v___x_473_ = lean_apply_4(v_toBind_468_, lean_box(0), lean_box(0), v_getRef_471_, v___f_469_);
v___x_474_ = lean_apply_4(v_toBind_468_, lean_box(0), lean_box(0), v___x_473_, v___f_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__16(lean_object* v_info_475_, lean_object* v___x_476_, lean_object* v_xs_477_, lean_object* v___x_478_, lean_object* v_b_479_, lean_object* v___x_480_, lean_object* v_toPure_481_, lean_object* v_quotCtx_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
lean_inc_n(v_info_475_, 5);
v___x_483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_483_, 0, v_info_475_);
lean_ctor_set(v___x_483_, 1, v___x_476_);
v___x_484_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37));
v___x_485_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43);
v___x_486_ = l_Array_append___redArg(v___x_485_, v_xs_477_);
v___x_487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_487_, 0, v_info_475_);
lean_ctor_set(v___x_487_, 1, v___x_484_);
lean_ctor_set(v___x_487_, 2, v___x_486_);
v___x_488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_488_, 0, v_info_475_);
lean_ctor_set(v___x_488_, 1, v___x_484_);
lean_ctor_set(v___x_488_, 2, v___x_485_);
v___x_489_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44));
v___x_490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_490_, 0, v_info_475_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = l_Lean_Syntax_node4(v_info_475_, v___x_478_, v___x_487_, v___x_488_, v___x_490_, v_b_479_);
v___x_492_ = l_Lean_Syntax_node2(v_info_475_, v___x_480_, v___x_483_, v___x_491_);
v___x_493_ = lean_apply_2(v_toPure_481_, lean_box(0), v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__16___boxed(lean_object* v_info_494_, lean_object* v___x_495_, lean_object* v_xs_496_, lean_object* v___x_497_, lean_object* v_b_498_, lean_object* v___x_499_, lean_object* v_toPure_500_, lean_object* v_quotCtx_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__16(v_info_494_, v___x_495_, v_xs_496_, v___x_497_, v_b_498_, v___x_499_, v_toPure_500_, v_quotCtx_501_);
lean_dec(v_quotCtx_501_);
lean_dec_ref(v_xs_496_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7(lean_object* v_toBind_503_, lean_object* v_getContext_504_, lean_object* v___f_505_, lean_object* v_scp_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_apply_4(v_toBind_503_, lean_box(0), lean_box(0), v_getContext_504_, v___f_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed(lean_object* v_toBind_508_, lean_object* v_getContext_509_, lean_object* v___f_510_, lean_object* v_scp_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__7(v_toBind_508_, v_getContext_509_, v___f_510_, v_scp_511_);
lean_dec(v_scp_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__8(lean_object* v_inst_513_, lean_object* v___x_514_, lean_object* v_xs_515_, lean_object* v___x_516_, lean_object* v_b_517_, lean_object* v___x_518_, lean_object* v_toPure_519_, lean_object* v_toBind_520_, lean_object* v_info_521_){
_start:
{
lean_object* v_getCurrMacroScope_522_; lean_object* v_getContext_523_; lean_object* v___f_524_; lean_object* v___f_525_; lean_object* v___x_526_; 
v_getCurrMacroScope_522_ = lean_ctor_get(v_inst_513_, 1);
lean_inc(v_getCurrMacroScope_522_);
v_getContext_523_ = lean_ctor_get(v_inst_513_, 2);
lean_inc(v_getContext_523_);
lean_dec_ref(v_inst_513_);
v___f_524_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__16___boxed), 8, 7);
lean_closure_set(v___f_524_, 0, v_info_521_);
lean_closure_set(v___f_524_, 1, v___x_514_);
lean_closure_set(v___f_524_, 2, v_xs_515_);
lean_closure_set(v___f_524_, 3, v___x_516_);
lean_closure_set(v___f_524_, 4, v_b_517_);
lean_closure_set(v___f_524_, 5, v___x_518_);
lean_closure_set(v___f_524_, 6, v_toPure_519_);
lean_inc(v_toBind_520_);
v___f_525_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_525_, 0, v_toBind_520_);
lean_closure_set(v___f_525_, 1, v_getContext_523_);
lean_closure_set(v___f_525_, 2, v___f_524_);
v___x_526_ = lean_apply_4(v_toBind_520_, lean_box(0), lean_box(0), v_getCurrMacroScope_522_, v___f_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__9(lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v___x_529_, lean_object* v_xs_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v_toPure_533_, lean_object* v_toBind_534_, lean_object* v___f_535_, lean_object* v_b_536_){
_start:
{
lean_object* v_getRef_537_; lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_getRef_537_ = lean_ctor_get(v_inst_527_, 0);
lean_inc(v_getRef_537_);
lean_dec_ref(v_inst_527_);
lean_inc_n(v_toBind_534_, 2);
v___f_538_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__8), 9, 8);
lean_closure_set(v___f_538_, 0, v_inst_528_);
lean_closure_set(v___f_538_, 1, v___x_529_);
lean_closure_set(v___f_538_, 2, v_xs_530_);
lean_closure_set(v___f_538_, 3, v___x_531_);
lean_closure_set(v___f_538_, 4, v_b_536_);
lean_closure_set(v___f_538_, 5, v___x_532_);
lean_closure_set(v___f_538_, 6, v_toPure_533_);
lean_closure_set(v___f_538_, 7, v_toBind_534_);
v___x_539_ = lean_apply_4(v_toBind_534_, lean_box(0), lean_box(0), v_getRef_537_, v___f_535_);
v___x_540_ = lean_apply_4(v_toBind_534_, lean_box(0), lean_box(0), v___x_539_, v___f_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11(lean_object* v_info_541_, lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v_t_544_, lean_object* v_e_545_, lean_object* v_toPure_546_, lean_object* v_quotCtx_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_548_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38));
lean_inc_n(v_info_541_, 3);
v___x_549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_549_, 0, v_info_541_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39));
v___x_551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_551_, 0, v_info_541_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40));
v___x_553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_553_, 0, v_info_541_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = l_Lean_Syntax_node6(v_info_541_, v___x_542_, v___x_549_, v___x_543_, v___x_551_, v_t_544_, v___x_553_, v_e_545_);
v___x_555_ = lean_apply_2(v_toPure_546_, lean_box(0), v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed(lean_object* v_info_556_, lean_object* v___x_557_, lean_object* v___x_558_, lean_object* v_t_559_, lean_object* v_e_560_, lean_object* v_toPure_561_, lean_object* v_quotCtx_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__11(v_info_556_, v___x_557_, v___x_558_, v_t_559_, v_e_560_, v_toPure_561_, v_quotCtx_562_);
lean_dec(v_quotCtx_562_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__12(lean_object* v_inst_564_, lean_object* v___x_565_, lean_object* v___x_566_, lean_object* v_t_567_, lean_object* v_e_568_, lean_object* v_toPure_569_, lean_object* v_toBind_570_, lean_object* v_info_571_){
_start:
{
lean_object* v_getCurrMacroScope_572_; lean_object* v_getContext_573_; lean_object* v___f_574_; lean_object* v___f_575_; lean_object* v___x_576_; 
v_getCurrMacroScope_572_ = lean_ctor_get(v_inst_564_, 1);
lean_inc(v_getCurrMacroScope_572_);
v_getContext_573_ = lean_ctor_get(v_inst_564_, 2);
lean_inc(v_getContext_573_);
lean_dec_ref(v_inst_564_);
v___f_574_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed), 7, 6);
lean_closure_set(v___f_574_, 0, v_info_571_);
lean_closure_set(v___f_574_, 1, v___x_565_);
lean_closure_set(v___f_574_, 2, v___x_566_);
lean_closure_set(v___f_574_, 3, v_t_567_);
lean_closure_set(v___f_574_, 4, v_e_568_);
lean_closure_set(v___f_574_, 5, v_toPure_569_);
lean_inc(v_toBind_570_);
v___f_575_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_575_, 0, v_toBind_570_);
lean_closure_set(v___f_575_, 1, v_getContext_573_);
lean_closure_set(v___f_575_, 2, v___f_574_);
v___x_576_ = lean_apply_4(v_toBind_570_, lean_box(0), lean_box(0), v_getCurrMacroScope_572_, v___f_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__10(lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v___x_579_, lean_object* v___x_580_, lean_object* v_t_581_, lean_object* v_toPure_582_, lean_object* v_toBind_583_, lean_object* v___f_584_, lean_object* v_e_585_){
_start:
{
lean_object* v_getRef_586_; lean_object* v___f_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_getRef_586_ = lean_ctor_get(v_inst_577_, 0);
lean_inc(v_getRef_586_);
lean_dec_ref(v_inst_577_);
lean_inc_n(v_toBind_583_, 2);
v___f_587_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__12), 8, 7);
lean_closure_set(v___f_587_, 0, v_inst_578_);
lean_closure_set(v___f_587_, 1, v___x_579_);
lean_closure_set(v___f_587_, 2, v___x_580_);
lean_closure_set(v___f_587_, 3, v_t_581_);
lean_closure_set(v___f_587_, 4, v_e_585_);
lean_closure_set(v___f_587_, 5, v_toPure_582_);
lean_closure_set(v___f_587_, 6, v_toBind_583_);
v___x_588_ = lean_apply_4(v_toBind_583_, lean_box(0), lean_box(0), v_getRef_586_, v___f_584_);
v___x_589_ = lean_apply_4(v_toBind_583_, lean_box(0), lean_box(0), v___x_588_, v___f_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__19(lean_object* v_toPure_590_, lean_object* v___x_591_, lean_object* v_quotCtx_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = lean_apply_2(v_toPure_590_, lean_box(0), v___x_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__19___boxed(lean_object* v_toPure_594_, lean_object* v___x_595_, lean_object* v_quotCtx_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__19(v_toPure_594_, v___x_595_, v_quotCtx_596_);
lean_dec(v_quotCtx_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18(lean_object* v_toPure_598_, lean_object* v_____do__lift_599_){
_start:
{
uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = 0;
v___x_601_ = l_Lean_SourceInfo_fromRef(v_____do__lift_599_, v___x_600_);
v___x_602_ = lean_apply_2(v_toPure_598_, lean_box(0), v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed(lean_object* v_toPure_603_, lean_object* v_____do__lift_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__18(v_toPure_603_, v_____do__lift_604_);
lean_dec(v_____do__lift_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__29(lean_object* v_info_606_, lean_object* v___x_607_, lean_object* v_scp_608_, lean_object* v___x_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v___x_613_, lean_object* v___x_614_, lean_object* v___x_615_, lean_object* v_____do__lift_616_, lean_object* v_toPure_617_, lean_object* v_quotCtx_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_619_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15));
lean_inc_n(v_info_606_, 5);
v___x_620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_620_, 0, v_info_606_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
v___x_622_ = l_Lean_addMacroScope(v_quotCtx_618_, v___x_607_, v_scp_608_);
v___x_623_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__0));
v___x_624_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__1));
v___x_625_ = l_Lean_Name_mkStr4(v___x_609_, v___x_610_, v___x_623_, v___x_624_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___x_627_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20));
lean_inc_ref_n(v___x_611_, 3);
v___x_628_ = l_Lean_Name_mkStr2(v___x_611_, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
v___x_630_ = l_Lean_Name_mkStr2(v___x_611_, v___x_612_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
v___x_632_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25));
v___x_633_ = l_Lean_Name_mkStr2(v___x_611_, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___x_635_ = l_Lean_Name_mkStr1(v___x_611_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_634_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_631_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_629_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_626_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_643_, 0, v_info_606_);
lean_ctor_set(v___x_643_, 1, v___x_621_);
lean_ctor_set(v___x_643_, 2, v___x_622_);
lean_ctor_set(v___x_643_, 3, v___x_642_);
v___x_644_ = l_Lean_Syntax_node1(v_info_606_, v___x_613_, v___x_643_);
v___x_645_ = l_Lean_Syntax_node2(v_info_606_, v___x_614_, v___x_620_, v___x_644_);
v___x_646_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
v___x_647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_647_, 0, v_info_606_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = l_Lean_Syntax_node3(v_info_606_, v___x_615_, v___x_645_, v_____do__lift_616_, v___x_647_);
v___x_649_ = lean_apply_2(v_toPure_617_, lean_box(0), v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__14(lean_object* v_info_650_, lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v___x_654_, lean_object* v___x_655_, lean_object* v___x_656_, lean_object* v___x_657_, lean_object* v___x_658_, lean_object* v_____do__lift_659_, lean_object* v_toPure_660_, lean_object* v_toBind_661_, lean_object* v_getContext_662_, lean_object* v_scp_663_){
_start:
{
lean_object* v___f_664_; lean_object* v___x_665_; 
v___f_664_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__29), 13, 12);
lean_closure_set(v___f_664_, 0, v_info_650_);
lean_closure_set(v___f_664_, 1, v___x_651_);
lean_closure_set(v___f_664_, 2, v_scp_663_);
lean_closure_set(v___f_664_, 3, v___x_652_);
lean_closure_set(v___f_664_, 4, v___x_653_);
lean_closure_set(v___f_664_, 5, v___x_654_);
lean_closure_set(v___f_664_, 6, v___x_655_);
lean_closure_set(v___f_664_, 7, v___x_656_);
lean_closure_set(v___f_664_, 8, v___x_657_);
lean_closure_set(v___f_664_, 9, v___x_658_);
lean_closure_set(v___f_664_, 10, v_____do__lift_659_);
lean_closure_set(v___f_664_, 11, v_toPure_660_);
v___x_665_ = lean_apply_4(v_toBind_661_, lean_box(0), lean_box(0), v_getContext_662_, v___f_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__15(lean_object* v_inst_666_, lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v___x_672_, lean_object* v___x_673_, lean_object* v___x_674_, lean_object* v_____do__lift_675_, lean_object* v_toPure_676_, lean_object* v_toBind_677_, lean_object* v_info_678_){
_start:
{
lean_object* v_getCurrMacroScope_679_; lean_object* v_getContext_680_; lean_object* v___f_681_; lean_object* v___x_682_; 
v_getCurrMacroScope_679_ = lean_ctor_get(v_inst_666_, 1);
lean_inc(v_getCurrMacroScope_679_);
v_getContext_680_ = lean_ctor_get(v_inst_666_, 2);
lean_inc(v_getContext_680_);
lean_dec_ref(v_inst_666_);
lean_inc(v_toBind_677_);
v___f_681_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__14), 14, 13);
lean_closure_set(v___f_681_, 0, v_info_678_);
lean_closure_set(v___f_681_, 1, v___x_667_);
lean_closure_set(v___f_681_, 2, v___x_668_);
lean_closure_set(v___f_681_, 3, v___x_669_);
lean_closure_set(v___f_681_, 4, v___x_670_);
lean_closure_set(v___f_681_, 5, v___x_671_);
lean_closure_set(v___f_681_, 6, v___x_672_);
lean_closure_set(v___f_681_, 7, v___x_673_);
lean_closure_set(v___f_681_, 8, v___x_674_);
lean_closure_set(v___f_681_, 9, v_____do__lift_675_);
lean_closure_set(v___f_681_, 10, v_toPure_676_);
lean_closure_set(v___f_681_, 11, v_toBind_677_);
lean_closure_set(v___f_681_, 12, v_getContext_680_);
v___x_682_ = lean_apply_4(v_toBind_677_, lean_box(0), lean_box(0), v_getCurrMacroScope_679_, v___f_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__17(lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v___x_685_, lean_object* v___x_686_, lean_object* v___x_687_, lean_object* v___x_688_, lean_object* v___x_689_, lean_object* v___x_690_, lean_object* v___x_691_, lean_object* v___x_692_, lean_object* v_toPure_693_, lean_object* v_toBind_694_, lean_object* v___f_695_, lean_object* v_____do__lift_696_){
_start:
{
lean_object* v_getRef_697_; lean_object* v___f_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_getRef_697_ = lean_ctor_get(v_inst_683_, 0);
lean_inc(v_getRef_697_);
lean_dec_ref(v_inst_683_);
lean_inc_n(v_toBind_694_, 2);
v___f_698_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__15), 13, 12);
lean_closure_set(v___f_698_, 0, v_inst_684_);
lean_closure_set(v___f_698_, 1, v___x_685_);
lean_closure_set(v___f_698_, 2, v___x_686_);
lean_closure_set(v___f_698_, 3, v___x_687_);
lean_closure_set(v___f_698_, 4, v___x_688_);
lean_closure_set(v___f_698_, 5, v___x_689_);
lean_closure_set(v___f_698_, 6, v___x_690_);
lean_closure_set(v___f_698_, 7, v___x_691_);
lean_closure_set(v___f_698_, 8, v___x_692_);
lean_closure_set(v___f_698_, 9, v_____do__lift_696_);
lean_closure_set(v___f_698_, 10, v_toPure_693_);
lean_closure_set(v___f_698_, 11, v_toBind_694_);
v___x_699_ = lean_apply_4(v_toBind_694_, lean_box(0), lean_box(0), v_getRef_697_, v___f_695_);
v___x_700_ = lean_apply_4(v_toBind_694_, lean_box(0), lean_box(0), v___x_699_, v___f_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg(lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_x_704_){
_start:
{
lean_object* v_toApplicative_705_; lean_object* v_toBind_706_; lean_object* v_toPure_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_toApplicative_705_ = lean_ctor_get(v_inst_701_, 0);
v_toBind_706_ = lean_ctor_get(v_inst_701_, 1);
lean_inc(v_toBind_706_);
v_toPure_707_ = lean_ctor_get(v_toApplicative_705_, 1);
v___x_708_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__0));
v___x_709_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__1));
v___x_710_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__3));
lean_inc(v_x_704_);
v___x_711_ = l_Lean_Syntax_isOfKind(v_x_704_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_712_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0));
v___x_713_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1));
v___x_714_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4));
lean_inc(v_x_704_);
v___x_715_ = l_Lean_Syntax_isOfKind(v_x_704_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8));
lean_inc(v_x_704_);
v___x_717_ = l_Lean_Syntax_isOfKind(v_x_704_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_718_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5));
v___x_719_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6));
lean_inc(v_x_704_);
v___x_720_ = l_Lean_Syntax_isOfKind(v_x_704_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10));
lean_inc(v_x_704_);
v___x_722_ = l_Lean_Syntax_isOfKind(v_x_704_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v_getRef_723_; lean_object* v___f_724_; lean_object* v___f_725_; lean_object* v___f_726_; lean_object* v___x_727_; lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_inc_n(v_toPure_707_, 2);
lean_dec_ref(v_inst_701_);
v_getRef_723_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_getRef_723_);
lean_dec_ref(v_inst_702_);
v___f_724_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_724_, 0, v_toPure_707_);
lean_closure_set(v___f_724_, 1, v_x_704_);
lean_inc_n(v_toBind_706_, 3);
lean_inc_ref(v_inst_703_);
v___f_725_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_725_, 0, v_inst_703_);
lean_closure_set(v___f_725_, 1, v_toBind_706_);
lean_closure_set(v___f_725_, 2, v___f_724_);
v___f_726_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_726_, 0, v_inst_703_);
lean_closure_set(v___f_726_, 1, v_toBind_706_);
lean_closure_set(v___f_726_, 2, v___f_725_);
v___x_727_ = lean_box(v___x_722_);
v___f_728_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_728_, 0, v___x_727_);
lean_closure_set(v___f_728_, 1, v_toPure_707_);
v___x_729_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v_getRef_723_, v___f_728_);
v___x_730_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_729_, v___f_726_);
return v___x_730_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = l_Lean_Syntax_getArg(v_x_704_, v___x_731_);
v___x_733_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12));
lean_inc(v___x_732_);
v___x_734_ = l_Lean_Syntax_isOfKind(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v_getRef_735_; lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v___f_738_; lean_object* v___x_739_; lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_inc_n(v_toPure_707_, 2);
lean_dec(v___x_732_);
lean_dec_ref(v_inst_701_);
v_getRef_735_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_getRef_735_);
lean_dec_ref(v_inst_702_);
v___f_736_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_736_, 0, v_toPure_707_);
lean_closure_set(v___f_736_, 1, v_x_704_);
lean_inc_n(v_toBind_706_, 3);
lean_inc_ref(v_inst_703_);
v___f_737_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_737_, 0, v_inst_703_);
lean_closure_set(v___f_737_, 1, v_toBind_706_);
lean_closure_set(v___f_737_, 2, v___f_736_);
v___f_738_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_738_, 0, v_inst_703_);
lean_closure_set(v___f_738_, 1, v_toBind_706_);
lean_closure_set(v___f_738_, 2, v___f_737_);
v___x_739_ = lean_box(v___x_734_);
v___f_740_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_740_, 0, v___x_739_);
lean_closure_set(v___f_740_, 1, v_toPure_707_);
v___x_741_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v_getRef_735_, v___f_740_);
v___x_742_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_741_, v___f_738_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = l_Lean_Syntax_getArg(v___x_732_, v___x_743_);
lean_dec(v___x_732_);
v___x_745_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14));
lean_inc(v___x_744_);
v___x_746_ = l_Lean_Syntax_isOfKind(v___x_744_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v_getRef_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_inc_n(v_toPure_707_, 2);
lean_dec(v___x_744_);
lean_dec_ref(v_inst_701_);
v_getRef_747_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_getRef_747_);
lean_dec_ref(v_inst_702_);
v___f_748_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_748_, 0, v_toPure_707_);
lean_closure_set(v___f_748_, 1, v_x_704_);
lean_inc_n(v_toBind_706_, 3);
lean_inc_ref(v_inst_703_);
v___f_749_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_749_, 0, v_inst_703_);
lean_closure_set(v___f_749_, 1, v_toBind_706_);
lean_closure_set(v___f_749_, 2, v___f_748_);
v___f_750_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_750_, 0, v_inst_703_);
lean_closure_set(v___f_750_, 1, v_toBind_706_);
lean_closure_set(v___f_750_, 2, v___f_749_);
v___x_751_ = lean_box(v___x_746_);
v___f_752_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_752_, 0, v___x_751_);
lean_closure_set(v___f_752_, 1, v_toPure_707_);
v___x_753_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v_getRef_747_, v___f_752_);
v___x_754_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_753_, v___f_750_);
return v___x_754_;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_755_ = l_Lean_Syntax_getArg(v___x_744_, v___x_731_);
lean_dec(v___x_744_);
v___x_756_ = lean_box(0);
v___x_757_ = l_Lean_Syntax_matchesIdent(v___x_755_, v___x_756_);
lean_dec(v___x_755_);
if (v___x_757_ == 0)
{
lean_object* v_getRef_758_; lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
lean_inc_n(v_toPure_707_, 2);
lean_dec_ref(v_inst_701_);
v_getRef_758_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_getRef_758_);
lean_dec_ref(v_inst_702_);
v___f_759_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_759_, 0, v_toPure_707_);
lean_closure_set(v___f_759_, 1, v_x_704_);
lean_inc_n(v_toBind_706_, 3);
lean_inc_ref(v_inst_703_);
v___f_760_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_760_, 0, v_inst_703_);
lean_closure_set(v___f_760_, 1, v_toBind_706_);
lean_closure_set(v___f_760_, 2, v___f_759_);
v___f_761_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_761_, 0, v_inst_703_);
lean_closure_set(v___f_761_, 1, v_toBind_706_);
lean_closure_set(v___f_761_, 2, v___f_760_);
v___x_762_ = lean_box(v___x_757_);
v___f_763_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_763_, 0, v___x_762_);
lean_closure_set(v___f_763_, 1, v_toPure_707_);
v___x_764_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v_getRef_758_, v___f_763_);
v___x_765_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_764_, v___f_761_);
return v___x_765_;
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(3u);
v___x_767_ = l_Lean_Syntax_getArg(v_x_704_, v___x_766_);
lean_inc(v___x_767_);
v___x_768_ = l_Lean_Syntax_matchesNull(v___x_767_, v___x_743_);
if (v___x_768_ == 0)
{
lean_object* v_getRef_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_inc_n(v_toPure_707_, 2);
lean_dec(v___x_767_);
lean_dec_ref(v_inst_701_);
v_getRef_769_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_getRef_769_);
lean_dec_ref(v_inst_702_);
v___f_770_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_770_, 0, v_toPure_707_);
lean_closure_set(v___f_770_, 1, v_x_704_);
lean_inc_n(v_toBind_706_, 3);
lean_inc_ref(v_inst_703_);
v___f_771_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_771_, 0, v_inst_703_);
lean_closure_set(v___f_771_, 1, v_toBind_706_);
lean_closure_set(v___f_771_, 2, v___f_770_);
v___f_772_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_772_, 0, v_inst_703_);
lean_closure_set(v___f_772_, 1, v_toBind_706_);
lean_closure_set(v___f_772_, 2, v___f_771_);
v___x_773_ = lean_box(v___x_768_);
v___f_774_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_774_, 0, v___x_773_);
lean_closure_set(v___f_774_, 1, v_toPure_707_);
v___x_775_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v_getRef_769_, v___f_774_);
v___x_776_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_775_, v___f_772_);
return v___x_776_;
}
else
{
lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v_P_779_; lean_object* v___x_780_; lean_object* v___f_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_777_ = lean_box(v___x_720_);
lean_inc_n(v_toPure_707_, 2);
v___f_778_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_778_, 0, v___x_777_);
lean_closure_set(v___f_778_, 1, v_toPure_707_);
v_P_779_ = l_Lean_Syntax_getArg(v_x_704_, v___x_743_);
lean_dec(v_x_704_);
v___x_780_ = l_Lean_Syntax_getArg(v___x_767_, v___x_731_);
lean_dec(v___x_767_);
lean_inc(v_toBind_706_);
lean_inc_ref(v_inst_703_);
lean_inc_ref(v_inst_702_);
v___f_781_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__6), 15, 14);
lean_closure_set(v___f_781_, 0, v_inst_702_);
lean_closure_set(v___f_781_, 1, v_inst_703_);
lean_closure_set(v___f_781_, 2, v___x_756_);
lean_closure_set(v___f_781_, 3, v___x_708_);
lean_closure_set(v___f_781_, 4, v___x_709_);
lean_closure_set(v___f_781_, 5, v___x_712_);
lean_closure_set(v___f_781_, 6, v___x_713_);
lean_closure_set(v___f_781_, 7, v___x_745_);
lean_closure_set(v___f_781_, 8, v___x_733_);
lean_closure_set(v___f_781_, 9, v___x_780_);
lean_closure_set(v___f_781_, 10, v___x_721_);
lean_closure_set(v___f_781_, 11, v_toPure_707_);
lean_closure_set(v___f_781_, 12, v_toBind_706_);
lean_closure_set(v___f_781_, 13, v___f_778_);
v___x_782_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_701_, v_inst_702_, v_inst_703_, v_P_779_);
v___x_783_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_782_, v___f_781_);
return v___x_783_;
}
}
}
}
}
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = l_Lean_Syntax_getArg(v_x_704_, v___x_784_);
v___x_786_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42));
lean_inc(v___x_785_);
v___x_787_ = l_Lean_Syntax_isOfKind(v___x_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v_getRef_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___f_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_inc_n(v_toPure_707_, 2);
lean_dec(v___x_785_);
lean_dec_ref(v_inst_701_);
v_getRef_788_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_getRef_788_);
lean_dec_ref(v_inst_702_);
v___f_789_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_789_, 0, v_toPure_707_);
lean_closure_set(v___f_789_, 1, v_x_704_);
lean_inc_n(v_toBind_706_, 3);
lean_inc_ref(v_inst_703_);
v___f_790_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_790_, 0, v_inst_703_);
lean_closure_set(v___f_790_, 1, v_toBind_706_);
lean_closure_set(v___f_790_, 2, v___f_789_);
v___f_791_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_791_, 0, v_inst_703_);
lean_closure_set(v___f_791_, 1, v_toBind_706_);
lean_closure_set(v___f_791_, 2, v___f_790_);
v___x_792_ = lean_box(v___x_787_);
v___f_793_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_793_, 0, v___x_792_);
lean_closure_set(v___f_793_, 1, v_toPure_707_);
v___x_794_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v_getRef_788_, v___f_793_);
v___x_795_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_794_, v___f_791_);
return v___x_795_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = l_Lean_Syntax_getArg(v___x_785_, v___x_784_);
v___x_798_ = l_Lean_Syntax_matchesNull(v___x_797_, v___x_796_);
if (v___x_798_ == 0)
{
lean_object* v_getRef_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_inc_n(v_toPure_707_, 2);
lean_dec(v___x_785_);
lean_dec_ref(v_inst_701_);
v_getRef_799_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_getRef_799_);
lean_dec_ref(v_inst_702_);
v___f_800_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_800_, 0, v_toPure_707_);
lean_closure_set(v___f_800_, 1, v_x_704_);
lean_inc_n(v_toBind_706_, 3);
lean_inc_ref(v_inst_703_);
v___f_801_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_801_, 0, v_inst_703_);
lean_closure_set(v___f_801_, 1, v_toBind_706_);
lean_closure_set(v___f_801_, 2, v___f_800_);
v___f_802_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_802_, 0, v_inst_703_);
lean_closure_set(v___f_802_, 1, v_toBind_706_);
lean_closure_set(v___f_802_, 2, v___f_801_);
v___x_803_ = lean_box(v___x_798_);
v___f_804_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_804_, 0, v___x_803_);
lean_closure_set(v___f_804_, 1, v_toPure_707_);
v___x_805_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v_getRef_799_, v___f_804_);
v___x_806_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_805_, v___f_802_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_b_811_; lean_object* v_xs_812_; lean_object* v___f_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v_x_704_);
v___x_807_ = lean_box(v___x_717_);
lean_inc_n(v_toPure_707_, 2);
v___f_808_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_808_, 0, v___x_807_);
lean_closure_set(v___f_808_, 1, v_toPure_707_);
v___x_809_ = l_Lean_Syntax_getArg(v___x_785_, v___x_796_);
v___x_810_ = lean_unsigned_to_nat(3u);
v_b_811_ = l_Lean_Syntax_getArg(v___x_785_, v___x_810_);
lean_dec(v___x_785_);
v_xs_812_ = l_Lean_Syntax_getArgs(v___x_809_);
lean_dec(v___x_809_);
lean_inc(v_toBind_706_);
lean_inc_ref(v_inst_703_);
lean_inc_ref(v_inst_702_);
v___f_813_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__9), 10, 9);
lean_closure_set(v___f_813_, 0, v_inst_702_);
lean_closure_set(v___f_813_, 1, v_inst_703_);
lean_closure_set(v___f_813_, 2, v___x_718_);
lean_closure_set(v___f_813_, 3, v_xs_812_);
lean_closure_set(v___f_813_, 4, v___x_786_);
lean_closure_set(v___f_813_, 5, v___x_719_);
lean_closure_set(v___f_813_, 6, v_toPure_707_);
lean_closure_set(v___f_813_, 7, v_toBind_706_);
lean_closure_set(v___f_813_, 8, v___f_808_);
v___x_814_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_701_, v_inst_702_, v_inst_703_, v_b_811_);
v___x_815_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_814_, v___f_813_);
return v___x_815_;
}
}
}
}
else
{
lean_object* v___x_816_; lean_object* v___f_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_t_821_; lean_object* v___x_822_; lean_object* v_e_823_; lean_object* v___f_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_816_ = lean_box(v___x_715_);
lean_inc_n(v_toPure_707_, 2);
v___f_817_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_817_, 0, v___x_816_);
lean_closure_set(v___f_817_, 1, v_toPure_707_);
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = l_Lean_Syntax_getArg(v_x_704_, v___x_818_);
v___x_820_ = lean_unsigned_to_nat(3u);
v_t_821_ = l_Lean_Syntax_getArg(v_x_704_, v___x_820_);
v___x_822_ = lean_unsigned_to_nat(5u);
v_e_823_ = l_Lean_Syntax_getArg(v_x_704_, v___x_822_);
lean_dec(v_x_704_);
lean_inc_ref(v_inst_701_);
lean_inc(v_toBind_706_);
lean_inc_ref(v_inst_703_);
lean_inc_ref(v_inst_702_);
v___f_824_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__13), 10, 9);
lean_closure_set(v___f_824_, 0, v_inst_702_);
lean_closure_set(v___f_824_, 1, v_inst_703_);
lean_closure_set(v___f_824_, 2, v___x_716_);
lean_closure_set(v___f_824_, 3, v___x_819_);
lean_closure_set(v___f_824_, 4, v_toPure_707_);
lean_closure_set(v___f_824_, 5, v_toBind_706_);
lean_closure_set(v___f_824_, 6, v___f_817_);
lean_closure_set(v___f_824_, 7, v_inst_701_);
lean_closure_set(v___f_824_, 8, v_e_823_);
v___x_825_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_701_, v_inst_702_, v_inst_703_, v_t_821_);
v___x_826_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_825_, v___f_824_);
return v___x_826_;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l_Lean_Syntax_getArg(v_x_704_, v___x_827_);
v___x_829_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12));
lean_inc(v___x_828_);
v___x_830_ = l_Lean_Syntax_isOfKind(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v_getRef_831_; lean_object* v___f_832_; lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___x_835_; lean_object* v___f_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_inc_n(v_toPure_707_, 2);
lean_dec(v___x_828_);
lean_dec_ref(v_inst_701_);
v_getRef_831_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_getRef_831_);
lean_dec_ref(v_inst_702_);
v___f_832_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_832_, 0, v_toPure_707_);
lean_closure_set(v___f_832_, 1, v_x_704_);
lean_inc_n(v_toBind_706_, 3);
lean_inc_ref(v_inst_703_);
v___f_833_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_833_, 0, v_inst_703_);
lean_closure_set(v___f_833_, 1, v_toBind_706_);
lean_closure_set(v___f_833_, 2, v___f_832_);
v___f_834_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_834_, 0, v_inst_703_);
lean_closure_set(v___f_834_, 1, v_toBind_706_);
lean_closure_set(v___f_834_, 2, v___f_833_);
v___x_835_ = lean_box(v___x_830_);
v___f_836_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_836_, 0, v___x_835_);
lean_closure_set(v___f_836_, 1, v_toPure_707_);
v___x_837_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v_getRef_831_, v___f_836_);
v___x_838_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_837_, v___f_834_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_839_ = lean_unsigned_to_nat(1u);
v___x_840_ = l_Lean_Syntax_getArg(v___x_828_, v___x_839_);
lean_dec(v___x_828_);
v___x_841_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14));
lean_inc(v___x_840_);
v___x_842_ = l_Lean_Syntax_isOfKind(v___x_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v_getRef_843_; lean_object* v___f_844_; lean_object* v___f_845_; lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___f_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
lean_inc_n(v_toPure_707_, 2);
lean_dec(v___x_840_);
lean_dec_ref(v_inst_701_);
v_getRef_843_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_getRef_843_);
lean_dec_ref(v_inst_702_);
v___f_844_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_844_, 0, v_toPure_707_);
lean_closure_set(v___f_844_, 1, v_x_704_);
lean_inc_n(v_toBind_706_, 3);
lean_inc_ref(v_inst_703_);
v___f_845_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_845_, 0, v_inst_703_);
lean_closure_set(v___f_845_, 1, v_toBind_706_);
lean_closure_set(v___f_845_, 2, v___f_844_);
v___f_846_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_846_, 0, v_inst_703_);
lean_closure_set(v___f_846_, 1, v_toBind_706_);
lean_closure_set(v___f_846_, 2, v___f_845_);
v___x_847_ = lean_box(v___x_842_);
v___f_848_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_848_, 0, v___x_847_);
lean_closure_set(v___f_848_, 1, v_toPure_707_);
v___x_849_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v_getRef_843_, v___f_848_);
v___x_850_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_849_, v___f_846_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_851_ = l_Lean_Syntax_getArg(v___x_840_, v___x_827_);
lean_dec(v___x_840_);
v___x_852_ = lean_box(0);
v___x_853_ = l_Lean_Syntax_matchesIdent(v___x_851_, v___x_852_);
lean_dec(v___x_851_);
if (v___x_853_ == 0)
{
lean_object* v_getRef_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___f_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_inc_n(v_toPure_707_, 2);
lean_dec_ref(v_inst_701_);
v_getRef_854_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_getRef_854_);
lean_dec_ref(v_inst_702_);
v___f_855_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_855_, 0, v_toPure_707_);
lean_closure_set(v___f_855_, 1, v_x_704_);
lean_inc_n(v_toBind_706_, 3);
lean_inc_ref(v_inst_703_);
v___f_856_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_856_, 0, v_inst_703_);
lean_closure_set(v___f_856_, 1, v_toBind_706_);
lean_closure_set(v___f_856_, 2, v___f_855_);
v___f_857_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_857_, 0, v_inst_703_);
lean_closure_set(v___f_857_, 1, v_toBind_706_);
lean_closure_set(v___f_857_, 2, v___f_856_);
v___x_858_ = lean_box(v___x_853_);
v___f_859_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_859_, 0, v___x_858_);
lean_closure_set(v___f_859_, 1, v_toPure_707_);
v___x_860_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v_getRef_854_, v___f_859_);
v___x_861_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_860_, v___f_857_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; lean_object* v___f_863_; lean_object* v___f_864_; lean_object* v_P_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_862_ = lean_box(v___x_711_);
lean_inc_n(v_toPure_707_, 2);
v___f_863_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_863_, 0, v___x_862_);
lean_closure_set(v___f_863_, 1, v_toPure_707_);
lean_inc(v_toBind_706_);
lean_inc_ref(v_inst_703_);
lean_inc_ref(v_inst_702_);
v___f_864_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__17), 14, 13);
lean_closure_set(v___f_864_, 0, v_inst_702_);
lean_closure_set(v___f_864_, 1, v_inst_703_);
lean_closure_set(v___f_864_, 2, v___x_852_);
lean_closure_set(v___f_864_, 3, v___x_708_);
lean_closure_set(v___f_864_, 4, v___x_709_);
lean_closure_set(v___f_864_, 5, v___x_712_);
lean_closure_set(v___f_864_, 6, v___x_713_);
lean_closure_set(v___f_864_, 7, v___x_841_);
lean_closure_set(v___f_864_, 8, v___x_829_);
lean_closure_set(v___f_864_, 9, v___x_714_);
lean_closure_set(v___f_864_, 10, v_toPure_707_);
lean_closure_set(v___f_864_, 11, v_toBind_706_);
lean_closure_set(v___f_864_, 12, v___f_863_);
v_P_865_ = l_Lean_Syntax_getArg(v_x_704_, v___x_839_);
lean_dec(v_x_704_);
v___x_866_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_701_, v_inst_702_, v_inst_703_, v_P_865_);
v___x_867_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_866_, v___f_864_);
return v___x_867_;
}
}
}
}
}
else
{
lean_object* v_getRef_868_; lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___f_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_inc_n(v_toPure_707_, 2);
lean_dec_ref(v_inst_701_);
v_getRef_868_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_getRef_868_);
lean_dec_ref(v_inst_702_);
v___f_869_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed), 2, 1);
lean_closure_set(v___f_869_, 0, v_toPure_707_);
v___x_870_ = lean_unsigned_to_nat(1u);
v___x_871_ = l_Lean_Syntax_getArg(v_x_704_, v___x_870_);
lean_dec(v_x_704_);
v___f_872_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__19___boxed), 3, 2);
lean_closure_set(v___f_872_, 0, v_toPure_707_);
lean_closure_set(v___f_872_, 1, v___x_871_);
lean_inc_n(v_toBind_706_, 3);
lean_inc_ref(v_inst_703_);
v___f_873_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_873_, 0, v_inst_703_);
lean_closure_set(v___f_873_, 1, v_toBind_706_);
lean_closure_set(v___f_873_, 2, v___f_872_);
v___f_874_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_874_, 0, v_inst_703_);
lean_closure_set(v___f_874_, 1, v_toBind_706_);
lean_closure_set(v___f_874_, 2, v___f_873_);
v___x_875_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v_getRef_868_, v___f_869_);
v___x_876_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_875_, v___f_874_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__13(lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v___x_879_, lean_object* v___x_880_, lean_object* v_toPure_881_, lean_object* v_toBind_882_, lean_object* v___f_883_, lean_object* v_inst_884_, lean_object* v_e_885_, lean_object* v_t_886_){
_start:
{
lean_object* v___f_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_inc(v_toBind_882_);
lean_inc_ref(v_inst_878_);
lean_inc_ref(v_inst_877_);
v___f_887_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__10), 9, 8);
lean_closure_set(v___f_887_, 0, v_inst_877_);
lean_closure_set(v___f_887_, 1, v_inst_878_);
lean_closure_set(v___f_887_, 2, v___x_879_);
lean_closure_set(v___f_887_, 3, v___x_880_);
lean_closure_set(v___f_887_, 4, v_t_886_);
lean_closure_set(v___f_887_, 5, v_toPure_881_);
lean_closure_set(v___f_887_, 6, v_toBind_882_);
lean_closure_set(v___f_887_, 7, v___f_883_);
v___x_888_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_884_, v_inst_877_, v_inst_878_, v_e_885_);
v___x_889_ = lean_apply_4(v_toBind_882_, lean_box(0), lean_box(0), v___x_888_, v___f_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack(lean_object* v_m_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_x_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_891_, v_inst_892_, v_inst_893_, v_x_894_);
return v___x_895_;
}
}
lean_object* runtime_initialize_Std_Do_SPred_SPred(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_SPred_Notation_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Do_SPred_SPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_SPred_Notation_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do_SPred_SPred(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_SPred_Notation_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_SPred_SPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_SPred_Notation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_SPred_Notation_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
