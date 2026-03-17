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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__3(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Notation"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__22___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
v___x_169_ = l_Array_mkArray0(lean_box(0));
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
lean_dec_ref(v_a_172_);
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
lean_dec_ref(v_a_172_);
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
lean_dec_ref(v_a_172_);
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
lean_dec_ref(v_a_172_);
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
lean_dec_ref(v_a_172_);
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
lean_dec_ref(v_a_172_);
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
lean_inc(v_quotContext_212_);
v_currMacroScope_213_ = lean_ctor_get(v_a_172_, 2);
lean_inc(v_currMacroScope_213_);
v_ref_214_ = lean_ctor_get(v_a_172_, 5);
lean_inc(v_ref_214_);
lean_dec_ref(v_a_172_);
v___x_215_ = l_Lean_Syntax_getArg(v___x_180_, v___x_179_);
lean_dec(v___x_180_);
v___x_216_ = l_Lean_Syntax_getArg(v___x_208_, v___x_178_);
lean_dec(v___x_208_);
v___x_217_ = l_Lean_SourceInfo_fromRef(v_ref_214_, v___x_187_);
lean_dec(v_ref_214_);
v___x_218_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15));
lean_inc(v___x_217_);
v___x_219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
v___x_221_ = l_Lean_addMacroScope(v_quotContext_212_, v___x_203_, v_currMacroScope_213_);
v___x_222_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34));
lean_inc(v___x_217_);
v___x_223_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_223_, 0, v___x_217_);
lean_ctor_set(v___x_223_, 1, v___x_220_);
lean_ctor_set(v___x_223_, 2, v___x_221_);
lean_ctor_set(v___x_223_, 3, v___x_222_);
lean_inc(v___x_217_);
v___x_224_ = l_Lean_Syntax_node1(v___x_217_, v___x_198_, v___x_223_);
lean_inc(v___x_217_);
v___x_225_ = l_Lean_Syntax_node2(v___x_217_, v___x_193_, v___x_219_, v___x_224_);
v___x_226_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__6));
lean_inc(v___x_217_);
v___x_227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_217_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
lean_inc(v___x_217_);
v___x_229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_217_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
lean_inc_ref(v___x_229_);
lean_inc(v___x_217_);
v___x_230_ = l_Lean_Syntax_node3(v___x_217_, v___x_174_, v___x_227_, v___x_215_, v___x_229_);
v___x_231_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35));
lean_inc(v___x_217_);
v___x_232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_217_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37));
lean_inc(v___x_217_);
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
lean_inc(v_ref_237_);
lean_dec_ref(v_a_172_);
v___x_238_ = l_Lean_Syntax_getArg(v___x_180_, v___x_179_);
v___x_239_ = lean_unsigned_to_nat(3u);
v___x_240_ = l_Lean_Syntax_getArg(v___x_180_, v___x_239_);
v___x_241_ = lean_unsigned_to_nat(5u);
v___x_242_ = l_Lean_Syntax_getArg(v___x_180_, v___x_241_);
lean_dec(v___x_180_);
v___x_243_ = l_Lean_SourceInfo_fromRef(v_ref_237_, v___x_185_);
lean_dec(v_ref_237_);
v___x_244_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38));
lean_inc(v___x_243_);
v___x_245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39));
lean_inc(v___x_243_);
v___x_247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_243_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__6));
lean_inc(v___x_243_);
v___x_249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_243_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
lean_inc(v___x_243_);
v___x_251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_243_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
lean_inc_ref(v___x_251_);
lean_inc_ref(v___x_249_);
lean_inc(v___x_243_);
v___x_252_ = l_Lean_Syntax_node3(v___x_243_, v___x_174_, v___x_249_, v___x_240_, v___x_251_);
v___x_253_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40));
lean_inc(v___x_243_);
v___x_254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_243_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
lean_inc(v___x_243_);
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
lean_dec_ref(v_a_172_);
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
lean_dec_ref(v_a_172_);
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
lean_inc(v_ref_267_);
lean_dec_ref(v_a_172_);
v___x_268_ = l_Lean_Syntax_getArg(v___x_258_, v___x_178_);
v___x_269_ = lean_unsigned_to_nat(3u);
v___x_270_ = l_Lean_Syntax_getArg(v___x_258_, v___x_269_);
lean_dec(v___x_258_);
v_xs_271_ = l_Lean_Syntax_getArgs(v___x_268_);
lean_dec(v___x_268_);
v___x_272_ = l_Lean_SourceInfo_fromRef(v_ref_267_, v___x_182_);
lean_dec(v_ref_267_);
lean_inc(v___x_272_);
v___x_273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_183_);
v___x_274_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37));
v___x_275_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43);
v___x_276_ = l_Array_append___redArg(v___x_275_, v_xs_271_);
lean_dec_ref(v_xs_271_);
lean_inc(v___x_272_);
v___x_277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_277_, 0, v___x_272_);
lean_ctor_set(v___x_277_, 1, v___x_274_);
lean_ctor_set(v___x_277_, 2, v___x_276_);
lean_inc(v___x_272_);
v___x_278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_278_, 0, v___x_272_);
lean_ctor_set(v___x_278_, 1, v___x_274_);
lean_ctor_set(v___x_278_, 2, v___x_275_);
v___x_279_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44));
lean_inc(v___x_272_);
v___x_280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_272_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__6));
lean_inc(v___x_272_);
v___x_282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_272_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
lean_inc(v___x_272_);
v___x_284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_272_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
lean_inc(v___x_272_);
v___x_285_ = l_Lean_Syntax_node3(v___x_272_, v___x_174_, v___x_282_, v___x_270_, v___x_284_);
lean_inc(v___x_272_);
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
lean_dec_ref(v_a_172_);
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
lean_dec_ref(v_a_172_);
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
lean_dec_ref(v_a_172_);
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
lean_inc(v_quotContext_304_);
v_currMacroScope_305_ = lean_ctor_get(v_a_172_, 2);
lean_inc(v_currMacroScope_305_);
v_ref_306_ = lean_ctor_get(v_a_172_, 5);
lean_inc(v_ref_306_);
lean_dec_ref(v_a_172_);
v___x_307_ = l_Lean_Syntax_getArg(v___x_180_, v___x_179_);
lean_dec(v___x_180_);
v___x_308_ = 0;
v___x_309_ = l_Lean_SourceInfo_fromRef(v_ref_306_, v___x_308_);
lean_dec(v_ref_306_);
v___x_310_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15));
lean_inc(v___x_309_);
v___x_311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
v___x_313_ = l_Lean_addMacroScope(v_quotContext_304_, v___x_300_, v_currMacroScope_305_);
v___x_314_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34));
lean_inc(v___x_309_);
v___x_315_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_315_, 0, v___x_309_);
lean_ctor_set(v___x_315_, 1, v___x_312_);
lean_ctor_set(v___x_315_, 2, v___x_313_);
lean_ctor_set(v___x_315_, 3, v___x_314_);
lean_inc(v___x_309_);
v___x_316_ = l_Lean_Syntax_node1(v___x_309_, v___x_295_, v___x_315_);
lean_inc(v___x_309_);
v___x_317_ = l_Lean_Syntax_node2(v___x_309_, v___x_290_, v___x_311_, v___x_316_);
v___x_318_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__6));
lean_inc(v___x_309_);
v___x_319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_309_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
lean_inc(v___x_309_);
v___x_321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_309_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
lean_inc_ref(v___x_321_);
lean_inc(v___x_309_);
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__0(lean_object* v_toPure_325_, lean_object* v_x_326_, lean_object* v_quotCtx_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_apply_2(v_toPure_325_, lean_box(0), v_x_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed(lean_object* v_toPure_329_, lean_object* v_x_330_, lean_object* v_quotCtx_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__0(v_toPure_329_, v_x_330_, v_quotCtx_331_);
lean_dec(v_quotCtx_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__1(lean_object* v_inst_333_, lean_object* v_toBind_334_, lean_object* v___f_335_, lean_object* v_scp_336_){
_start:
{
lean_object* v_getContext_337_; lean_object* v___x_338_; 
v_getContext_337_ = lean_ctor_get(v_inst_333_, 2);
lean_inc(v_getContext_337_);
lean_dec_ref(v_inst_333_);
v___x_338_ = lean_apply_4(v_toBind_334_, lean_box(0), lean_box(0), v_getContext_337_, v___f_335_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed(lean_object* v_inst_339_, lean_object* v_toBind_340_, lean_object* v___f_341_, lean_object* v_scp_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__1(v_inst_339_, v_toBind_340_, v___f_341_, v_scp_342_);
lean_dec(v_scp_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__2(lean_object* v_inst_344_, lean_object* v_toBind_345_, lean_object* v___f_346_, lean_object* v_info_347_){
_start:
{
lean_object* v_getCurrMacroScope_348_; lean_object* v___x_349_; 
v_getCurrMacroScope_348_ = lean_ctor_get(v_inst_344_, 1);
lean_inc(v_getCurrMacroScope_348_);
lean_dec_ref(v_inst_344_);
v___x_349_ = lean_apply_4(v_toBind_345_, lean_box(0), lean_box(0), v_getCurrMacroScope_348_, v___f_346_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed(lean_object* v_inst_350_, lean_object* v_toBind_351_, lean_object* v___f_352_, lean_object* v_info_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__2(v_inst_350_, v_toBind_351_, v___f_352_, v_info_353_);
lean_dec(v_info_353_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__3(uint8_t v___x_355_, lean_object* v_toPure_356_, lean_object* v_____do__lift_357_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Lean_SourceInfo_fromRef(v_____do__lift_357_, v___x_355_);
v___x_359_ = lean_apply_2(v_toPure_356_, lean_box(0), v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed(lean_object* v___x_360_, lean_object* v_toPure_361_, lean_object* v_____do__lift_362_){
_start:
{
uint8_t v___x_9843__boxed_363_; lean_object* v_res_364_; 
v___x_9843__boxed_363_ = lean_unbox(v___x_360_);
v_res_364_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__3(v___x_9843__boxed_363_, v_toPure_361_, v_____do__lift_362_);
lean_dec(v_____do__lift_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__20(lean_object* v_info_367_, lean_object* v___x_368_, lean_object* v_scp_369_, lean_object* v___x_370_, lean_object* v___x_371_, lean_object* v___x_372_, lean_object* v___x_373_, lean_object* v___x_374_, lean_object* v___x_375_, lean_object* v___x_376_, lean_object* v___x_377_, lean_object* v_____do__lift_378_, lean_object* v_toPure_379_, lean_object* v_quotCtx_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_381_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15));
lean_inc(v_info_367_);
v___x_382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_382_, 0, v_info_367_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
v___x_384_ = l_Lean_addMacroScope(v_quotCtx_380_, v___x_368_, v_scp_369_);
v___x_385_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0));
v___x_386_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1));
v___x_387_ = l_Lean_Name_mkStr4(v___x_370_, v___x_371_, v___x_385_, v___x_386_);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
v___x_389_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20));
lean_inc_ref(v___x_372_);
v___x_390_ = l_Lean_Name_mkStr2(v___x_372_, v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_inc_ref(v___x_372_);
v___x_392_ = l_Lean_Name_mkStr2(v___x_372_, v___x_373_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
v___x_394_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25));
lean_inc_ref(v___x_372_);
v___x_395_ = l_Lean_Name_mkStr2(v___x_372_, v___x_394_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
v___x_397_ = l_Lean_Name_mkStr1(v___x_372_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
v___x_399_ = lean_box(0);
v___x_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_396_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_393_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_391_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_388_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
lean_inc(v_info_367_);
v___x_405_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_405_, 0, v_info_367_);
lean_ctor_set(v___x_405_, 1, v___x_383_);
lean_ctor_set(v___x_405_, 2, v___x_384_);
lean_ctor_set(v___x_405_, 3, v___x_404_);
lean_inc(v_info_367_);
v___x_406_ = l_Lean_Syntax_node1(v_info_367_, v___x_374_, v___x_405_);
lean_inc(v_info_367_);
v___x_407_ = l_Lean_Syntax_node2(v_info_367_, v___x_375_, v___x_382_, v___x_406_);
v___x_408_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35));
lean_inc(v_info_367_);
v___x_409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_409_, 0, v_info_367_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37));
lean_inc(v_info_367_);
v___x_411_ = l_Lean_Syntax_node1(v_info_367_, v___x_410_, v___x_376_);
v___x_412_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
lean_inc(v_info_367_);
v___x_413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_413_, 0, v_info_367_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = l_Lean_Syntax_node5(v_info_367_, v___x_377_, v___x_407_, v_____do__lift_378_, v___x_409_, v___x_411_, v___x_413_);
v___x_415_ = lean_apply_2(v_toPure_379_, lean_box(0), v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__4(lean_object* v_info_416_, lean_object* v___x_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v___x_420_, lean_object* v___x_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v_____do__lift_426_, lean_object* v_toPure_427_, lean_object* v_toBind_428_, lean_object* v_getContext_429_, lean_object* v_scp_430_){
_start:
{
lean_object* v___f_431_; lean_object* v___x_432_; 
v___f_431_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__20), 14, 13);
lean_closure_set(v___f_431_, 0, v_info_416_);
lean_closure_set(v___f_431_, 1, v___x_417_);
lean_closure_set(v___f_431_, 2, v_scp_430_);
lean_closure_set(v___f_431_, 3, v___x_418_);
lean_closure_set(v___f_431_, 4, v___x_419_);
lean_closure_set(v___f_431_, 5, v___x_420_);
lean_closure_set(v___f_431_, 6, v___x_421_);
lean_closure_set(v___f_431_, 7, v___x_422_);
lean_closure_set(v___f_431_, 8, v___x_423_);
lean_closure_set(v___f_431_, 9, v___x_424_);
lean_closure_set(v___f_431_, 10, v___x_425_);
lean_closure_set(v___f_431_, 11, v_____do__lift_426_);
lean_closure_set(v___f_431_, 12, v_toPure_427_);
v___x_432_ = lean_apply_4(v_toBind_428_, lean_box(0), lean_box(0), v_getContext_429_, v___f_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__5(lean_object* v_inst_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v_____do__lift_443_, lean_object* v_toPure_444_, lean_object* v_toBind_445_, lean_object* v_info_446_){
_start:
{
lean_object* v_getCurrMacroScope_447_; lean_object* v_getContext_448_; lean_object* v___f_449_; lean_object* v___x_450_; 
v_getCurrMacroScope_447_ = lean_ctor_get(v_inst_433_, 1);
lean_inc(v_getCurrMacroScope_447_);
v_getContext_448_ = lean_ctor_get(v_inst_433_, 2);
lean_inc(v_getContext_448_);
lean_dec_ref(v_inst_433_);
lean_inc(v_toBind_445_);
v___f_449_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__4), 15, 14);
lean_closure_set(v___f_449_, 0, v_info_446_);
lean_closure_set(v___f_449_, 1, v___x_434_);
lean_closure_set(v___f_449_, 2, v___x_435_);
lean_closure_set(v___f_449_, 3, v___x_436_);
lean_closure_set(v___f_449_, 4, v___x_437_);
lean_closure_set(v___f_449_, 5, v___x_438_);
lean_closure_set(v___f_449_, 6, v___x_439_);
lean_closure_set(v___f_449_, 7, v___x_440_);
lean_closure_set(v___f_449_, 8, v___x_441_);
lean_closure_set(v___f_449_, 9, v___x_442_);
lean_closure_set(v___f_449_, 10, v_____do__lift_443_);
lean_closure_set(v___f_449_, 11, v_toPure_444_);
lean_closure_set(v___f_449_, 12, v_toBind_445_);
lean_closure_set(v___f_449_, 13, v_getContext_448_);
v___x_450_ = lean_apply_4(v_toBind_445_, lean_box(0), lean_box(0), v_getCurrMacroScope_447_, v___f_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7(lean_object* v_inst_451_, lean_object* v_toApplicative_452_, lean_object* v_inst_453_, lean_object* v___x_454_, lean_object* v___x_455_, lean_object* v___x_456_, lean_object* v___x_457_, lean_object* v___x_458_, lean_object* v___x_459_, lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v_toBind_463_, uint8_t v___x_464_, lean_object* v_____do__lift_465_){
_start:
{
lean_object* v_getRef_466_; lean_object* v_toPure_467_; lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___f_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_getRef_466_ = lean_ctor_get(v_inst_451_, 0);
lean_inc(v_getRef_466_);
lean_dec_ref(v_inst_451_);
v_toPure_467_ = lean_ctor_get(v_toApplicative_452_, 1);
lean_inc(v_toPure_467_);
lean_dec_ref(v_toApplicative_452_);
lean_inc(v_toBind_463_);
lean_inc(v_toPure_467_);
v___f_468_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__5), 14, 13);
lean_closure_set(v___f_468_, 0, v_inst_453_);
lean_closure_set(v___f_468_, 1, v___x_454_);
lean_closure_set(v___f_468_, 2, v___x_455_);
lean_closure_set(v___f_468_, 3, v___x_456_);
lean_closure_set(v___f_468_, 4, v___x_457_);
lean_closure_set(v___f_468_, 5, v___x_458_);
lean_closure_set(v___f_468_, 6, v___x_459_);
lean_closure_set(v___f_468_, 7, v___x_460_);
lean_closure_set(v___f_468_, 8, v___x_461_);
lean_closure_set(v___f_468_, 9, v___x_462_);
lean_closure_set(v___f_468_, 10, v_____do__lift_465_);
lean_closure_set(v___f_468_, 11, v_toPure_467_);
lean_closure_set(v___f_468_, 12, v_toBind_463_);
v___x_469_ = lean_box(v___x_464_);
v___f_470_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_470_, 0, v___x_469_);
lean_closure_set(v___f_470_, 1, v_toPure_467_);
lean_inc(v_toBind_463_);
v___x_471_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_getRef_466_, v___f_470_);
v___x_472_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v___x_471_, v___f_468_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed(lean_object* v_inst_473_, lean_object* v_toApplicative_474_, lean_object* v_inst_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v___x_479_, lean_object* v___x_480_, lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v_toBind_485_, lean_object* v___x_486_, lean_object* v_____do__lift_487_){
_start:
{
uint8_t v___x_10033__boxed_488_; lean_object* v_res_489_; 
v___x_10033__boxed_488_ = lean_unbox(v___x_486_);
v_res_489_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__7(v_inst_473_, v_toApplicative_474_, v_inst_475_, v___x_476_, v___x_477_, v___x_478_, v___x_479_, v___x_480_, v___x_481_, v___x_482_, v___x_483_, v___x_484_, v_toBind_485_, v___x_10033__boxed_488_, v_____do__lift_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__15(lean_object* v_info_490_, lean_object* v___x_491_, lean_object* v_xs_492_, lean_object* v___x_493_, lean_object* v_b_494_, lean_object* v___x_495_, lean_object* v_toPure_496_, lean_object* v_quotCtx_497_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_inc(v_info_490_);
v___x_498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_498_, 0, v_info_490_);
lean_ctor_set(v___x_498_, 1, v___x_491_);
v___x_499_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37));
v___x_500_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43);
v___x_501_ = l_Array_append___redArg(v___x_500_, v_xs_492_);
lean_inc(v_info_490_);
v___x_502_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_502_, 0, v_info_490_);
lean_ctor_set(v___x_502_, 1, v___x_499_);
lean_ctor_set(v___x_502_, 2, v___x_501_);
lean_inc(v_info_490_);
v___x_503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_503_, 0, v_info_490_);
lean_ctor_set(v___x_503_, 1, v___x_499_);
lean_ctor_set(v___x_503_, 2, v___x_500_);
v___x_504_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44));
lean_inc(v_info_490_);
v___x_505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_505_, 0, v_info_490_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
lean_inc(v_info_490_);
v___x_506_ = l_Lean_Syntax_node4(v_info_490_, v___x_493_, v___x_502_, v___x_503_, v___x_505_, v_b_494_);
v___x_507_ = l_Lean_Syntax_node2(v_info_490_, v___x_495_, v___x_498_, v___x_506_);
v___x_508_ = lean_apply_2(v_toPure_496_, lean_box(0), v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__15___boxed(lean_object* v_info_509_, lean_object* v___x_510_, lean_object* v_xs_511_, lean_object* v___x_512_, lean_object* v_b_513_, lean_object* v___x_514_, lean_object* v_toPure_515_, lean_object* v_quotCtx_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__15(v_info_509_, v___x_510_, v_xs_511_, v___x_512_, v_b_513_, v___x_514_, v_toPure_515_, v_quotCtx_516_);
lean_dec(v_quotCtx_516_);
lean_dec_ref(v_xs_511_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__6(lean_object* v_toBind_518_, lean_object* v_getContext_519_, lean_object* v___f_520_, lean_object* v_scp_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_apply_4(v_toBind_518_, lean_box(0), lean_box(0), v_getContext_519_, v___f_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed(lean_object* v_toBind_523_, lean_object* v_getContext_524_, lean_object* v___f_525_, lean_object* v_scp_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__6(v_toBind_523_, v_getContext_524_, v___f_525_, v_scp_526_);
lean_dec(v_scp_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__8(lean_object* v_inst_528_, lean_object* v___x_529_, lean_object* v_xs_530_, lean_object* v___x_531_, lean_object* v_b_532_, lean_object* v___x_533_, lean_object* v_toPure_534_, lean_object* v_toBind_535_, lean_object* v_info_536_){
_start:
{
lean_object* v_getCurrMacroScope_537_; lean_object* v_getContext_538_; lean_object* v___f_539_; lean_object* v___f_540_; lean_object* v___x_541_; 
v_getCurrMacroScope_537_ = lean_ctor_get(v_inst_528_, 1);
lean_inc(v_getCurrMacroScope_537_);
v_getContext_538_ = lean_ctor_get(v_inst_528_, 2);
lean_inc(v_getContext_538_);
lean_dec_ref(v_inst_528_);
v___f_539_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__15___boxed), 8, 7);
lean_closure_set(v___f_539_, 0, v_info_536_);
lean_closure_set(v___f_539_, 1, v___x_529_);
lean_closure_set(v___f_539_, 2, v_xs_530_);
lean_closure_set(v___f_539_, 3, v___x_531_);
lean_closure_set(v___f_539_, 4, v_b_532_);
lean_closure_set(v___f_539_, 5, v___x_533_);
lean_closure_set(v___f_539_, 6, v_toPure_534_);
lean_inc(v_toBind_535_);
v___f_540_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed), 4, 3);
lean_closure_set(v___f_540_, 0, v_toBind_535_);
lean_closure_set(v___f_540_, 1, v_getContext_538_);
lean_closure_set(v___f_540_, 2, v___f_539_);
v___x_541_ = lean_apply_4(v_toBind_535_, lean_box(0), lean_box(0), v_getCurrMacroScope_537_, v___f_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__10(lean_object* v_inst_542_, lean_object* v_toApplicative_543_, lean_object* v_inst_544_, lean_object* v___x_545_, lean_object* v_xs_546_, lean_object* v___x_547_, lean_object* v___x_548_, lean_object* v_toBind_549_, uint8_t v___x_550_, lean_object* v_b_551_){
_start:
{
lean_object* v_getRef_552_; lean_object* v_toPure_553_; lean_object* v___f_554_; lean_object* v___x_555_; lean_object* v___f_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_getRef_552_ = lean_ctor_get(v_inst_542_, 0);
lean_inc(v_getRef_552_);
lean_dec_ref(v_inst_542_);
v_toPure_553_ = lean_ctor_get(v_toApplicative_543_, 1);
lean_inc(v_toPure_553_);
lean_dec_ref(v_toApplicative_543_);
lean_inc(v_toBind_549_);
lean_inc(v_toPure_553_);
v___f_554_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__8), 9, 8);
lean_closure_set(v___f_554_, 0, v_inst_544_);
lean_closure_set(v___f_554_, 1, v___x_545_);
lean_closure_set(v___f_554_, 2, v_xs_546_);
lean_closure_set(v___f_554_, 3, v___x_547_);
lean_closure_set(v___f_554_, 4, v_b_551_);
lean_closure_set(v___f_554_, 5, v___x_548_);
lean_closure_set(v___f_554_, 6, v_toPure_553_);
lean_closure_set(v___f_554_, 7, v_toBind_549_);
v___x_555_ = lean_box(v___x_550_);
v___f_556_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_556_, 0, v___x_555_);
lean_closure_set(v___f_556_, 1, v_toPure_553_);
lean_inc(v_toBind_549_);
v___x_557_ = lean_apply_4(v_toBind_549_, lean_box(0), lean_box(0), v_getRef_552_, v___f_556_);
v___x_558_ = lean_apply_4(v_toBind_549_, lean_box(0), lean_box(0), v___x_557_, v___f_554_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__10___boxed(lean_object* v_inst_559_, lean_object* v_toApplicative_560_, lean_object* v_inst_561_, lean_object* v___x_562_, lean_object* v_xs_563_, lean_object* v___x_564_, lean_object* v___x_565_, lean_object* v_toBind_566_, lean_object* v___x_567_, lean_object* v_b_568_){
_start:
{
uint8_t v___x_10143__boxed_569_; lean_object* v_res_570_; 
v___x_10143__boxed_569_ = lean_unbox(v___x_567_);
v_res_570_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__10(v_inst_559_, v_toApplicative_560_, v_inst_561_, v___x_562_, v_xs_563_, v___x_564_, v___x_565_, v_toBind_566_, v___x_10143__boxed_569_, v_b_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__9(lean_object* v_info_571_, lean_object* v___x_572_, lean_object* v___x_573_, lean_object* v_t_574_, lean_object* v_e_575_, lean_object* v_toPure_576_, lean_object* v_quotCtx_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_578_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38));
lean_inc(v_info_571_);
v___x_579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_579_, 0, v_info_571_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39));
lean_inc(v_info_571_);
v___x_581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_581_, 0, v_info_571_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40));
lean_inc(v_info_571_);
v___x_583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_583_, 0, v_info_571_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = l_Lean_Syntax_node6(v_info_571_, v___x_572_, v___x_579_, v___x_573_, v___x_581_, v_t_574_, v___x_583_, v_e_575_);
v___x_585_ = lean_apply_2(v_toPure_576_, lean_box(0), v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__9___boxed(lean_object* v_info_586_, lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v_t_589_, lean_object* v_e_590_, lean_object* v_toPure_591_, lean_object* v_quotCtx_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__9(v_info_586_, v___x_587_, v___x_588_, v_t_589_, v_e_590_, v_toPure_591_, v_quotCtx_592_);
lean_dec(v_quotCtx_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__12(lean_object* v_inst_594_, lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v_t_597_, lean_object* v_e_598_, lean_object* v_toPure_599_, lean_object* v_toBind_600_, lean_object* v_info_601_){
_start:
{
lean_object* v_getCurrMacroScope_602_; lean_object* v_getContext_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___x_606_; 
v_getCurrMacroScope_602_ = lean_ctor_get(v_inst_594_, 1);
lean_inc(v_getCurrMacroScope_602_);
v_getContext_603_ = lean_ctor_get(v_inst_594_, 2);
lean_inc(v_getContext_603_);
lean_dec_ref(v_inst_594_);
v___f_604_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_604_, 0, v_info_601_);
lean_closure_set(v___f_604_, 1, v___x_595_);
lean_closure_set(v___f_604_, 2, v___x_596_);
lean_closure_set(v___f_604_, 3, v_t_597_);
lean_closure_set(v___f_604_, 4, v_e_598_);
lean_closure_set(v___f_604_, 5, v_toPure_599_);
lean_inc(v_toBind_600_);
v___f_605_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed), 4, 3);
lean_closure_set(v___f_605_, 0, v_toBind_600_);
lean_closure_set(v___f_605_, 1, v_getContext_603_);
lean_closure_set(v___f_605_, 2, v___f_604_);
v___x_606_ = lean_apply_4(v_toBind_600_, lean_box(0), lean_box(0), v_getCurrMacroScope_602_, v___f_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__13(lean_object* v_inst_607_, lean_object* v_toApplicative_608_, lean_object* v_inst_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v_t_612_, lean_object* v_toBind_613_, uint8_t v___x_614_, lean_object* v_e_615_){
_start:
{
lean_object* v_getRef_616_; lean_object* v_toPure_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_getRef_616_ = lean_ctor_get(v_inst_607_, 0);
lean_inc(v_getRef_616_);
lean_dec_ref(v_inst_607_);
v_toPure_617_ = lean_ctor_get(v_toApplicative_608_, 1);
lean_inc(v_toPure_617_);
lean_dec_ref(v_toApplicative_608_);
lean_inc(v_toBind_613_);
lean_inc(v_toPure_617_);
v___f_618_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__12), 8, 7);
lean_closure_set(v___f_618_, 0, v_inst_609_);
lean_closure_set(v___f_618_, 1, v___x_610_);
lean_closure_set(v___f_618_, 2, v___x_611_);
lean_closure_set(v___f_618_, 3, v_t_612_);
lean_closure_set(v___f_618_, 4, v_e_615_);
lean_closure_set(v___f_618_, 5, v_toPure_617_);
lean_closure_set(v___f_618_, 6, v_toBind_613_);
v___x_619_ = lean_box(v___x_614_);
v___f_620_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_620_, 0, v___x_619_);
lean_closure_set(v___f_620_, 1, v_toPure_617_);
lean_inc(v_toBind_613_);
v___x_621_ = lean_apply_4(v_toBind_613_, lean_box(0), lean_box(0), v_getRef_616_, v___f_620_);
v___x_622_ = lean_apply_4(v_toBind_613_, lean_box(0), lean_box(0), v___x_621_, v___f_618_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__13___boxed(lean_object* v_inst_623_, lean_object* v_toApplicative_624_, lean_object* v_inst_625_, lean_object* v___x_626_, lean_object* v___x_627_, lean_object* v_t_628_, lean_object* v_toBind_629_, lean_object* v___x_630_, lean_object* v_e_631_){
_start:
{
uint8_t v___x_10215__boxed_632_; lean_object* v_res_633_; 
v___x_10215__boxed_632_ = lean_unbox(v___x_630_);
v_res_633_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__13(v_inst_623_, v_toApplicative_624_, v_inst_625_, v___x_626_, v___x_627_, v_t_628_, v_toBind_629_, v___x_10215__boxed_632_, v_e_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__28(lean_object* v_info_634_, lean_object* v___x_635_, lean_object* v_scp_636_, lean_object* v___x_637_, lean_object* v___x_638_, lean_object* v___x_639_, lean_object* v___x_640_, lean_object* v___x_641_, lean_object* v___x_642_, lean_object* v___x_643_, lean_object* v_____do__lift_644_, lean_object* v_toPure_645_, lean_object* v_quotCtx_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_647_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15));
lean_inc(v_info_634_);
v___x_648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_648_, 0, v_info_634_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
v___x_650_ = l_Lean_addMacroScope(v_quotCtx_646_, v___x_635_, v_scp_636_);
v___x_651_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0));
v___x_652_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1));
v___x_653_ = l_Lean_Name_mkStr4(v___x_637_, v___x_638_, v___x_651_, v___x_652_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
v___x_655_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20));
lean_inc_ref(v___x_639_);
v___x_656_ = l_Lean_Name_mkStr2(v___x_639_, v___x_655_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_inc_ref(v___x_639_);
v___x_658_ = l_Lean_Name_mkStr2(v___x_639_, v___x_640_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
v___x_660_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25));
lean_inc_ref(v___x_639_);
v___x_661_ = l_Lean_Name_mkStr2(v___x_639_, v___x_660_);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
v___x_663_ = l_Lean_Name_mkStr1(v___x_639_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
v___x_665_ = lean_box(0);
v___x_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_662_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_659_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_657_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_654_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
lean_inc(v_info_634_);
v___x_671_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_671_, 0, v_info_634_);
lean_ctor_set(v___x_671_, 1, v___x_649_);
lean_ctor_set(v___x_671_, 2, v___x_650_);
lean_ctor_set(v___x_671_, 3, v___x_670_);
lean_inc(v_info_634_);
v___x_672_ = l_Lean_Syntax_node1(v_info_634_, v___x_641_, v___x_671_);
lean_inc(v_info_634_);
v___x_673_ = l_Lean_Syntax_node2(v_info_634_, v___x_642_, v___x_648_, v___x_672_);
v___x_674_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
lean_inc(v_info_634_);
v___x_675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_675_, 0, v_info_634_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = l_Lean_Syntax_node3(v_info_634_, v___x_643_, v___x_673_, v_____do__lift_644_, v___x_675_);
v___x_677_ = lean_apply_2(v_toPure_645_, lean_box(0), v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__14(lean_object* v_info_678_, lean_object* v___x_679_, lean_object* v___x_680_, lean_object* v___x_681_, lean_object* v___x_682_, lean_object* v___x_683_, lean_object* v___x_684_, lean_object* v___x_685_, lean_object* v___x_686_, lean_object* v_____do__lift_687_, lean_object* v_toPure_688_, lean_object* v_toBind_689_, lean_object* v_getContext_690_, lean_object* v_scp_691_){
_start:
{
lean_object* v___f_692_; lean_object* v___x_693_; 
v___f_692_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__28), 13, 12);
lean_closure_set(v___f_692_, 0, v_info_678_);
lean_closure_set(v___f_692_, 1, v___x_679_);
lean_closure_set(v___f_692_, 2, v_scp_691_);
lean_closure_set(v___f_692_, 3, v___x_680_);
lean_closure_set(v___f_692_, 4, v___x_681_);
lean_closure_set(v___f_692_, 5, v___x_682_);
lean_closure_set(v___f_692_, 6, v___x_683_);
lean_closure_set(v___f_692_, 7, v___x_684_);
lean_closure_set(v___f_692_, 8, v___x_685_);
lean_closure_set(v___f_692_, 9, v___x_686_);
lean_closure_set(v___f_692_, 10, v_____do__lift_687_);
lean_closure_set(v___f_692_, 11, v_toPure_688_);
v___x_693_ = lean_apply_4(v_toBind_689_, lean_box(0), lean_box(0), v_getContext_690_, v___f_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__16(lean_object* v_inst_694_, lean_object* v___x_695_, lean_object* v___x_696_, lean_object* v___x_697_, lean_object* v___x_698_, lean_object* v___x_699_, lean_object* v___x_700_, lean_object* v___x_701_, lean_object* v___x_702_, lean_object* v_____do__lift_703_, lean_object* v_toPure_704_, lean_object* v_toBind_705_, lean_object* v_info_706_){
_start:
{
lean_object* v_getCurrMacroScope_707_; lean_object* v_getContext_708_; lean_object* v___f_709_; lean_object* v___x_710_; 
v_getCurrMacroScope_707_ = lean_ctor_get(v_inst_694_, 1);
lean_inc(v_getCurrMacroScope_707_);
v_getContext_708_ = lean_ctor_get(v_inst_694_, 2);
lean_inc(v_getContext_708_);
lean_dec_ref(v_inst_694_);
lean_inc(v_toBind_705_);
v___f_709_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__14), 14, 13);
lean_closure_set(v___f_709_, 0, v_info_706_);
lean_closure_set(v___f_709_, 1, v___x_695_);
lean_closure_set(v___f_709_, 2, v___x_696_);
lean_closure_set(v___f_709_, 3, v___x_697_);
lean_closure_set(v___f_709_, 4, v___x_698_);
lean_closure_set(v___f_709_, 5, v___x_699_);
lean_closure_set(v___f_709_, 6, v___x_700_);
lean_closure_set(v___f_709_, 7, v___x_701_);
lean_closure_set(v___f_709_, 8, v___x_702_);
lean_closure_set(v___f_709_, 9, v_____do__lift_703_);
lean_closure_set(v___f_709_, 10, v_toPure_704_);
lean_closure_set(v___f_709_, 11, v_toBind_705_);
lean_closure_set(v___f_709_, 12, v_getContext_708_);
v___x_710_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getCurrMacroScope_707_, v___f_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18(lean_object* v_inst_711_, lean_object* v_toApplicative_712_, lean_object* v_inst_713_, lean_object* v___x_714_, lean_object* v___x_715_, lean_object* v___x_716_, lean_object* v___x_717_, lean_object* v___x_718_, lean_object* v___x_719_, lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v_toBind_722_, uint8_t v___x_723_, lean_object* v_____do__lift_724_){
_start:
{
lean_object* v_getRef_725_; lean_object* v_toPure_726_; lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___f_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_getRef_725_ = lean_ctor_get(v_inst_711_, 0);
lean_inc(v_getRef_725_);
lean_dec_ref(v_inst_711_);
v_toPure_726_ = lean_ctor_get(v_toApplicative_712_, 1);
lean_inc(v_toPure_726_);
lean_dec_ref(v_toApplicative_712_);
lean_inc(v_toBind_722_);
lean_inc(v_toPure_726_);
v___f_727_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__16), 13, 12);
lean_closure_set(v___f_727_, 0, v_inst_713_);
lean_closure_set(v___f_727_, 1, v___x_714_);
lean_closure_set(v___f_727_, 2, v___x_715_);
lean_closure_set(v___f_727_, 3, v___x_716_);
lean_closure_set(v___f_727_, 4, v___x_717_);
lean_closure_set(v___f_727_, 5, v___x_718_);
lean_closure_set(v___f_727_, 6, v___x_719_);
lean_closure_set(v___f_727_, 7, v___x_720_);
lean_closure_set(v___f_727_, 8, v___x_721_);
lean_closure_set(v___f_727_, 9, v_____do__lift_724_);
lean_closure_set(v___f_727_, 10, v_toPure_726_);
lean_closure_set(v___f_727_, 11, v_toBind_722_);
v___x_728_ = lean_box(v___x_723_);
v___f_729_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_729_, 0, v___x_728_);
lean_closure_set(v___f_729_, 1, v_toPure_726_);
lean_inc(v_toBind_722_);
v___x_730_ = lean_apply_4(v_toBind_722_, lean_box(0), lean_box(0), v_getRef_725_, v___f_729_);
v___x_731_ = lean_apply_4(v_toBind_722_, lean_box(0), lean_box(0), v___x_730_, v___f_727_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed(lean_object* v_inst_732_, lean_object* v_toApplicative_733_, lean_object* v_inst_734_, lean_object* v___x_735_, lean_object* v___x_736_, lean_object* v___x_737_, lean_object* v___x_738_, lean_object* v___x_739_, lean_object* v___x_740_, lean_object* v___x_741_, lean_object* v___x_742_, lean_object* v_toBind_743_, lean_object* v___x_744_, lean_object* v_____do__lift_745_){
_start:
{
uint8_t v___x_10394__boxed_746_; lean_object* v_res_747_; 
v___x_10394__boxed_746_ = lean_unbox(v___x_744_);
v_res_747_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__18(v_inst_732_, v_toApplicative_733_, v_inst_734_, v___x_735_, v___x_736_, v___x_737_, v___x_738_, v___x_739_, v___x_740_, v___x_741_, v___x_742_, v_toBind_743_, v___x_10394__boxed_746_, v_____do__lift_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__22(lean_object* v_toPure_748_, lean_object* v_____do__lift_749_){
_start:
{
uint8_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = 0;
v___x_751_ = l_Lean_SourceInfo_fromRef(v_____do__lift_749_, v___x_750_);
v___x_752_ = lean_apply_2(v_toPure_748_, lean_box(0), v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__22___boxed(lean_object* v_toPure_753_, lean_object* v_____do__lift_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__22(v_toPure_753_, v_____do__lift_754_);
lean_dec(v_____do__lift_754_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__17(lean_object* v_toPure_756_, lean_object* v___x_757_, lean_object* v_quotCtx_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = lean_apply_2(v_toPure_756_, lean_box(0), v___x_757_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__17___boxed(lean_object* v_toPure_760_, lean_object* v___x_761_, lean_object* v_quotCtx_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__17(v_toPure_760_, v___x_761_, v_quotCtx_762_);
lean_dec(v_quotCtx_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed(lean_object* v_inst_764_, lean_object* v_toApplicative_765_, lean_object* v_inst_766_, lean_object* v___x_767_, lean_object* v___x_768_, lean_object* v_toBind_769_, lean_object* v___x_770_, lean_object* v_inst_771_, lean_object* v_e_772_, lean_object* v_t_773_){
_start:
{
uint8_t v___x_10506__boxed_774_; lean_object* v_res_775_; 
v___x_10506__boxed_774_ = lean_unbox(v___x_770_);
v_res_775_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__11(v_inst_764_, v_toApplicative_765_, v_inst_766_, v___x_767_, v___x_768_, v_toBind_769_, v___x_10506__boxed_774_, v_inst_771_, v_e_772_, v_t_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg(lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_x_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_780_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__0));
v___x_781_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__1));
v___x_782_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__3));
lean_inc(v_x_779_);
v___x_783_ = l_Lean_Syntax_isOfKind(v_x_779_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_784_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0));
v___x_785_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1));
v___x_786_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4));
lean_inc(v_x_779_);
v___x_787_ = l_Lean_Syntax_isOfKind(v_x_779_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8));
lean_inc(v_x_779_);
v___x_789_ = l_Lean_Syntax_isOfKind(v_x_779_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_790_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5));
v___x_791_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6));
lean_inc(v_x_779_);
v___x_792_ = l_Lean_Syntax_isOfKind(v_x_779_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10));
lean_inc(v_x_779_);
v___x_794_ = l_Lean_Syntax_isOfKind(v_x_779_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v_toApplicative_795_; lean_object* v_toBind_796_; lean_object* v_getRef_797_; lean_object* v_toPure_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_toApplicative_795_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_795_);
v_toBind_796_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_796_);
lean_dec_ref(v_inst_776_);
v_getRef_797_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getRef_797_);
lean_dec_ref(v_inst_777_);
v_toPure_798_ = lean_ctor_get(v_toApplicative_795_, 1);
lean_inc(v_toPure_798_);
lean_dec_ref(v_toApplicative_795_);
lean_inc(v_toPure_798_);
v___f_799_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_799_, 0, v_toPure_798_);
lean_closure_set(v___f_799_, 1, v_x_779_);
lean_inc(v_toBind_796_);
lean_inc_ref(v_inst_778_);
v___f_800_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_800_, 0, v_inst_778_);
lean_closure_set(v___f_800_, 1, v_toBind_796_);
lean_closure_set(v___f_800_, 2, v___f_799_);
lean_inc(v_toBind_796_);
v___f_801_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_801_, 0, v_inst_778_);
lean_closure_set(v___f_801_, 1, v_toBind_796_);
lean_closure_set(v___f_801_, 2, v___f_800_);
v___x_802_ = lean_box(v___x_794_);
v___f_803_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_803_, 0, v___x_802_);
lean_closure_set(v___f_803_, 1, v_toPure_798_);
lean_inc(v_toBind_796_);
v___x_804_ = lean_apply_4(v_toBind_796_, lean_box(0), lean_box(0), v_getRef_797_, v___f_803_);
v___x_805_ = lean_apply_4(v_toBind_796_, lean_box(0), lean_box(0), v___x_804_, v___f_801_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = l_Lean_Syntax_getArg(v_x_779_, v___x_806_);
v___x_808_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12));
lean_inc(v___x_807_);
v___x_809_ = l_Lean_Syntax_isOfKind(v___x_807_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v_toApplicative_810_; lean_object* v_toBind_811_; lean_object* v_getRef_812_; lean_object* v_toPure_813_; lean_object* v___f_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v___f_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec(v___x_807_);
v_toApplicative_810_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_810_);
v_toBind_811_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_811_);
lean_dec_ref(v_inst_776_);
v_getRef_812_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getRef_812_);
lean_dec_ref(v_inst_777_);
v_toPure_813_ = lean_ctor_get(v_toApplicative_810_, 1);
lean_inc(v_toPure_813_);
lean_dec_ref(v_toApplicative_810_);
lean_inc(v_toPure_813_);
v___f_814_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_814_, 0, v_toPure_813_);
lean_closure_set(v___f_814_, 1, v_x_779_);
lean_inc(v_toBind_811_);
lean_inc_ref(v_inst_778_);
v___f_815_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_815_, 0, v_inst_778_);
lean_closure_set(v___f_815_, 1, v_toBind_811_);
lean_closure_set(v___f_815_, 2, v___f_814_);
lean_inc(v_toBind_811_);
v___f_816_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_816_, 0, v_inst_778_);
lean_closure_set(v___f_816_, 1, v_toBind_811_);
lean_closure_set(v___f_816_, 2, v___f_815_);
v___x_817_ = lean_box(v___x_809_);
v___f_818_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_818_, 0, v___x_817_);
lean_closure_set(v___f_818_, 1, v_toPure_813_);
lean_inc(v_toBind_811_);
v___x_819_ = lean_apply_4(v_toBind_811_, lean_box(0), lean_box(0), v_getRef_812_, v___f_818_);
v___x_820_ = lean_apply_4(v_toBind_811_, lean_box(0), lean_box(0), v___x_819_, v___f_816_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = l_Lean_Syntax_getArg(v___x_807_, v___x_821_);
lean_dec(v___x_807_);
v___x_823_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14));
lean_inc(v___x_822_);
v___x_824_ = l_Lean_Syntax_isOfKind(v___x_822_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v_toApplicative_825_; lean_object* v_toBind_826_; lean_object* v_getRef_827_; lean_object* v_toPure_828_; lean_object* v___f_829_; lean_object* v___f_830_; lean_object* v___f_831_; lean_object* v___x_832_; lean_object* v___f_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec(v___x_822_);
v_toApplicative_825_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_825_);
v_toBind_826_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_826_);
lean_dec_ref(v_inst_776_);
v_getRef_827_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getRef_827_);
lean_dec_ref(v_inst_777_);
v_toPure_828_ = lean_ctor_get(v_toApplicative_825_, 1);
lean_inc(v_toPure_828_);
lean_dec_ref(v_toApplicative_825_);
lean_inc(v_toPure_828_);
v___f_829_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_829_, 0, v_toPure_828_);
lean_closure_set(v___f_829_, 1, v_x_779_);
lean_inc(v_toBind_826_);
lean_inc_ref(v_inst_778_);
v___f_830_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_830_, 0, v_inst_778_);
lean_closure_set(v___f_830_, 1, v_toBind_826_);
lean_closure_set(v___f_830_, 2, v___f_829_);
lean_inc(v_toBind_826_);
v___f_831_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_831_, 0, v_inst_778_);
lean_closure_set(v___f_831_, 1, v_toBind_826_);
lean_closure_set(v___f_831_, 2, v___f_830_);
v___x_832_ = lean_box(v___x_824_);
v___f_833_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_833_, 0, v___x_832_);
lean_closure_set(v___f_833_, 1, v_toPure_828_);
lean_inc(v_toBind_826_);
v___x_834_ = lean_apply_4(v_toBind_826_, lean_box(0), lean_box(0), v_getRef_827_, v___f_833_);
v___x_835_ = lean_apply_4(v_toBind_826_, lean_box(0), lean_box(0), v___x_834_, v___f_831_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_836_ = l_Lean_Syntax_getArg(v___x_822_, v___x_806_);
lean_dec(v___x_822_);
v___x_837_ = lean_box(0);
v___x_838_ = l_Lean_Syntax_matchesIdent(v___x_836_, v___x_837_);
lean_dec(v___x_836_);
if (v___x_838_ == 0)
{
lean_object* v_toApplicative_839_; lean_object* v_toBind_840_; lean_object* v_getRef_841_; lean_object* v_toPure_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___f_845_; lean_object* v___x_846_; lean_object* v___f_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_toApplicative_839_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_839_);
v_toBind_840_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_840_);
lean_dec_ref(v_inst_776_);
v_getRef_841_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getRef_841_);
lean_dec_ref(v_inst_777_);
v_toPure_842_ = lean_ctor_get(v_toApplicative_839_, 1);
lean_inc(v_toPure_842_);
lean_dec_ref(v_toApplicative_839_);
lean_inc(v_toPure_842_);
v___f_843_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_843_, 0, v_toPure_842_);
lean_closure_set(v___f_843_, 1, v_x_779_);
lean_inc(v_toBind_840_);
lean_inc_ref(v_inst_778_);
v___f_844_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_844_, 0, v_inst_778_);
lean_closure_set(v___f_844_, 1, v_toBind_840_);
lean_closure_set(v___f_844_, 2, v___f_843_);
lean_inc(v_toBind_840_);
v___f_845_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_845_, 0, v_inst_778_);
lean_closure_set(v___f_845_, 1, v_toBind_840_);
lean_closure_set(v___f_845_, 2, v___f_844_);
v___x_846_ = lean_box(v___x_838_);
v___f_847_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_847_, 0, v___x_846_);
lean_closure_set(v___f_847_, 1, v_toPure_842_);
lean_inc(v_toBind_840_);
v___x_848_ = lean_apply_4(v_toBind_840_, lean_box(0), lean_box(0), v_getRef_841_, v___f_847_);
v___x_849_ = lean_apply_4(v_toBind_840_, lean_box(0), lean_box(0), v___x_848_, v___f_845_);
return v___x_849_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_850_ = lean_unsigned_to_nat(3u);
v___x_851_ = l_Lean_Syntax_getArg(v_x_779_, v___x_850_);
lean_inc(v___x_851_);
v___x_852_ = l_Lean_Syntax_matchesNull(v___x_851_, v___x_821_);
if (v___x_852_ == 0)
{
lean_object* v_toApplicative_853_; lean_object* v_toBind_854_; lean_object* v_getRef_855_; lean_object* v_toPure_856_; lean_object* v___f_857_; lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___x_860_; lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v___x_851_);
v_toApplicative_853_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_853_);
v_toBind_854_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_854_);
lean_dec_ref(v_inst_776_);
v_getRef_855_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getRef_855_);
lean_dec_ref(v_inst_777_);
v_toPure_856_ = lean_ctor_get(v_toApplicative_853_, 1);
lean_inc(v_toPure_856_);
lean_dec_ref(v_toApplicative_853_);
lean_inc(v_toPure_856_);
v___f_857_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_857_, 0, v_toPure_856_);
lean_closure_set(v___f_857_, 1, v_x_779_);
lean_inc(v_toBind_854_);
lean_inc_ref(v_inst_778_);
v___f_858_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_858_, 0, v_inst_778_);
lean_closure_set(v___f_858_, 1, v_toBind_854_);
lean_closure_set(v___f_858_, 2, v___f_857_);
lean_inc(v_toBind_854_);
v___f_859_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_859_, 0, v_inst_778_);
lean_closure_set(v___f_859_, 1, v_toBind_854_);
lean_closure_set(v___f_859_, 2, v___f_858_);
v___x_860_ = lean_box(v___x_852_);
v___f_861_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_861_, 0, v___x_860_);
lean_closure_set(v___f_861_, 1, v_toPure_856_);
lean_inc(v_toBind_854_);
v___x_862_ = lean_apply_4(v_toBind_854_, lean_box(0), lean_box(0), v_getRef_855_, v___f_861_);
v___x_863_ = lean_apply_4(v_toBind_854_, lean_box(0), lean_box(0), v___x_862_, v___f_859_);
return v___x_863_;
}
else
{
lean_object* v_toApplicative_864_; lean_object* v_toBind_865_; lean_object* v_P_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_toApplicative_864_ = lean_ctor_get(v_inst_776_, 0);
v_toBind_865_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_865_);
v_P_866_ = l_Lean_Syntax_getArg(v_x_779_, v___x_821_);
lean_dec(v_x_779_);
v___x_867_ = l_Lean_Syntax_getArg(v___x_851_, v___x_806_);
lean_dec(v___x_851_);
v___x_868_ = lean_box(v___x_792_);
lean_inc(v_toBind_865_);
lean_inc_ref(v_inst_778_);
lean_inc_ref(v_toApplicative_864_);
lean_inc_ref(v_inst_777_);
v___f_869_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed), 15, 14);
lean_closure_set(v___f_869_, 0, v_inst_777_);
lean_closure_set(v___f_869_, 1, v_toApplicative_864_);
lean_closure_set(v___f_869_, 2, v_inst_778_);
lean_closure_set(v___f_869_, 3, v___x_837_);
lean_closure_set(v___f_869_, 4, v___x_780_);
lean_closure_set(v___f_869_, 5, v___x_781_);
lean_closure_set(v___f_869_, 6, v___x_784_);
lean_closure_set(v___f_869_, 7, v___x_785_);
lean_closure_set(v___f_869_, 8, v___x_823_);
lean_closure_set(v___f_869_, 9, v___x_808_);
lean_closure_set(v___f_869_, 10, v___x_867_);
lean_closure_set(v___f_869_, 11, v___x_793_);
lean_closure_set(v___f_869_, 12, v_toBind_865_);
lean_closure_set(v___f_869_, 13, v___x_868_);
v___x_870_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_P_866_);
v___x_871_ = lean_apply_4(v_toBind_865_, lean_box(0), lean_box(0), v___x_870_, v___f_869_);
return v___x_871_;
}
}
}
}
}
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = l_Lean_Syntax_getArg(v_x_779_, v___x_872_);
v___x_874_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42));
lean_inc(v___x_873_);
v___x_875_ = l_Lean_Syntax_isOfKind(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v_toApplicative_876_; lean_object* v_toBind_877_; lean_object* v_getRef_878_; lean_object* v_toPure_879_; lean_object* v___f_880_; lean_object* v___f_881_; lean_object* v___f_882_; lean_object* v___x_883_; lean_object* v___f_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec(v___x_873_);
v_toApplicative_876_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_876_);
v_toBind_877_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_877_);
lean_dec_ref(v_inst_776_);
v_getRef_878_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getRef_878_);
lean_dec_ref(v_inst_777_);
v_toPure_879_ = lean_ctor_get(v_toApplicative_876_, 1);
lean_inc(v_toPure_879_);
lean_dec_ref(v_toApplicative_876_);
lean_inc(v_toPure_879_);
v___f_880_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_880_, 0, v_toPure_879_);
lean_closure_set(v___f_880_, 1, v_x_779_);
lean_inc(v_toBind_877_);
lean_inc_ref(v_inst_778_);
v___f_881_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_881_, 0, v_inst_778_);
lean_closure_set(v___f_881_, 1, v_toBind_877_);
lean_closure_set(v___f_881_, 2, v___f_880_);
lean_inc(v_toBind_877_);
v___f_882_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_882_, 0, v_inst_778_);
lean_closure_set(v___f_882_, 1, v_toBind_877_);
lean_closure_set(v___f_882_, 2, v___f_881_);
v___x_883_ = lean_box(v___x_875_);
v___f_884_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_884_, 0, v___x_883_);
lean_closure_set(v___f_884_, 1, v_toPure_879_);
lean_inc(v_toBind_877_);
v___x_885_ = lean_apply_4(v_toBind_877_, lean_box(0), lean_box(0), v_getRef_878_, v___f_884_);
v___x_886_ = lean_apply_4(v_toBind_877_, lean_box(0), lean_box(0), v___x_885_, v___f_882_);
return v___x_886_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = l_Lean_Syntax_getArg(v___x_873_, v___x_872_);
v___x_889_ = l_Lean_Syntax_matchesNull(v___x_888_, v___x_887_);
if (v___x_889_ == 0)
{
lean_object* v_toApplicative_890_; lean_object* v_toBind_891_; lean_object* v_getRef_892_; lean_object* v_toPure_893_; lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec(v___x_873_);
v_toApplicative_890_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_890_);
v_toBind_891_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_891_);
lean_dec_ref(v_inst_776_);
v_getRef_892_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getRef_892_);
lean_dec_ref(v_inst_777_);
v_toPure_893_ = lean_ctor_get(v_toApplicative_890_, 1);
lean_inc(v_toPure_893_);
lean_dec_ref(v_toApplicative_890_);
lean_inc(v_toPure_893_);
v___f_894_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_894_, 0, v_toPure_893_);
lean_closure_set(v___f_894_, 1, v_x_779_);
lean_inc(v_toBind_891_);
lean_inc_ref(v_inst_778_);
v___f_895_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_895_, 0, v_inst_778_);
lean_closure_set(v___f_895_, 1, v_toBind_891_);
lean_closure_set(v___f_895_, 2, v___f_894_);
lean_inc(v_toBind_891_);
v___f_896_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_896_, 0, v_inst_778_);
lean_closure_set(v___f_896_, 1, v_toBind_891_);
lean_closure_set(v___f_896_, 2, v___f_895_);
v___x_897_ = lean_box(v___x_889_);
v___f_898_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_898_, 0, v___x_897_);
lean_closure_set(v___f_898_, 1, v_toPure_893_);
lean_inc(v_toBind_891_);
v___x_899_ = lean_apply_4(v_toBind_891_, lean_box(0), lean_box(0), v_getRef_892_, v___f_898_);
v___x_900_ = lean_apply_4(v_toBind_891_, lean_box(0), lean_box(0), v___x_899_, v___f_896_);
return v___x_900_;
}
else
{
lean_object* v_toApplicative_901_; lean_object* v_toBind_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v_b_905_; lean_object* v_xs_906_; lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_x_779_);
v_toApplicative_901_ = lean_ctor_get(v_inst_776_, 0);
v_toBind_902_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_902_);
v___x_903_ = l_Lean_Syntax_getArg(v___x_873_, v___x_887_);
v___x_904_ = lean_unsigned_to_nat(3u);
v_b_905_ = l_Lean_Syntax_getArg(v___x_873_, v___x_904_);
lean_dec(v___x_873_);
v_xs_906_ = l_Lean_Syntax_getArgs(v___x_903_);
lean_dec(v___x_903_);
v___x_907_ = lean_box(v___x_789_);
lean_inc(v_toBind_902_);
lean_inc_ref(v_inst_778_);
lean_inc_ref(v_toApplicative_901_);
lean_inc_ref(v_inst_777_);
v___f_908_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__10___boxed), 10, 9);
lean_closure_set(v___f_908_, 0, v_inst_777_);
lean_closure_set(v___f_908_, 1, v_toApplicative_901_);
lean_closure_set(v___f_908_, 2, v_inst_778_);
lean_closure_set(v___f_908_, 3, v___x_790_);
lean_closure_set(v___f_908_, 4, v_xs_906_);
lean_closure_set(v___f_908_, 5, v___x_874_);
lean_closure_set(v___f_908_, 6, v___x_791_);
lean_closure_set(v___f_908_, 7, v_toBind_902_);
lean_closure_set(v___f_908_, 8, v___x_907_);
v___x_909_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_b_905_);
v___x_910_ = lean_apply_4(v_toBind_902_, lean_box(0), lean_box(0), v___x_909_, v___f_908_);
return v___x_910_;
}
}
}
}
else
{
lean_object* v_toApplicative_911_; lean_object* v_toBind_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v_t_916_; lean_object* v___x_917_; lean_object* v_e_918_; lean_object* v___x_919_; lean_object* v___f_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_toApplicative_911_ = lean_ctor_get(v_inst_776_, 0);
v_toBind_912_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_912_);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = l_Lean_Syntax_getArg(v_x_779_, v___x_913_);
v___x_915_ = lean_unsigned_to_nat(3u);
v_t_916_ = l_Lean_Syntax_getArg(v_x_779_, v___x_915_);
v___x_917_ = lean_unsigned_to_nat(5u);
v_e_918_ = l_Lean_Syntax_getArg(v_x_779_, v___x_917_);
lean_dec(v_x_779_);
v___x_919_ = lean_box(v___x_787_);
lean_inc_ref(v_inst_776_);
lean_inc(v_toBind_912_);
lean_inc_ref(v_inst_778_);
lean_inc_ref(v_toApplicative_911_);
lean_inc_ref(v_inst_777_);
v___f_920_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed), 10, 9);
lean_closure_set(v___f_920_, 0, v_inst_777_);
lean_closure_set(v___f_920_, 1, v_toApplicative_911_);
lean_closure_set(v___f_920_, 2, v_inst_778_);
lean_closure_set(v___f_920_, 3, v___x_788_);
lean_closure_set(v___f_920_, 4, v___x_914_);
lean_closure_set(v___f_920_, 5, v_toBind_912_);
lean_closure_set(v___f_920_, 6, v___x_919_);
lean_closure_set(v___f_920_, 7, v_inst_776_);
lean_closure_set(v___f_920_, 8, v_e_918_);
v___x_921_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_t_916_);
v___x_922_ = lean_apply_4(v_toBind_912_, lean_box(0), lean_box(0), v___x_921_, v___f_920_);
return v___x_922_;
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = l_Lean_Syntax_getArg(v_x_779_, v___x_923_);
v___x_925_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12));
lean_inc(v___x_924_);
v___x_926_ = l_Lean_Syntax_isOfKind(v___x_924_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v_toApplicative_927_; lean_object* v_toBind_928_; lean_object* v_getRef_929_; lean_object* v_toPure_930_; lean_object* v___f_931_; lean_object* v___f_932_; lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___f_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v___x_924_);
v_toApplicative_927_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_927_);
v_toBind_928_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_928_);
lean_dec_ref(v_inst_776_);
v_getRef_929_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getRef_929_);
lean_dec_ref(v_inst_777_);
v_toPure_930_ = lean_ctor_get(v_toApplicative_927_, 1);
lean_inc(v_toPure_930_);
lean_dec_ref(v_toApplicative_927_);
lean_inc(v_toPure_930_);
v___f_931_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_931_, 0, v_toPure_930_);
lean_closure_set(v___f_931_, 1, v_x_779_);
lean_inc(v_toBind_928_);
lean_inc_ref(v_inst_778_);
v___f_932_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_932_, 0, v_inst_778_);
lean_closure_set(v___f_932_, 1, v_toBind_928_);
lean_closure_set(v___f_932_, 2, v___f_931_);
lean_inc(v_toBind_928_);
v___f_933_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_933_, 0, v_inst_778_);
lean_closure_set(v___f_933_, 1, v_toBind_928_);
lean_closure_set(v___f_933_, 2, v___f_932_);
v___x_934_ = lean_box(v___x_926_);
v___f_935_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_935_, 0, v___x_934_);
lean_closure_set(v___f_935_, 1, v_toPure_930_);
lean_inc(v_toBind_928_);
v___x_936_ = lean_apply_4(v_toBind_928_, lean_box(0), lean_box(0), v_getRef_929_, v___f_935_);
v___x_937_ = lean_apply_4(v_toBind_928_, lean_box(0), lean_box(0), v___x_936_, v___f_933_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = l_Lean_Syntax_getArg(v___x_924_, v___x_938_);
lean_dec(v___x_924_);
v___x_940_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14));
lean_inc(v___x_939_);
v___x_941_ = l_Lean_Syntax_isOfKind(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v_toApplicative_942_; lean_object* v_toBind_943_; lean_object* v_getRef_944_; lean_object* v_toPure_945_; lean_object* v___f_946_; lean_object* v___f_947_; lean_object* v___f_948_; lean_object* v___x_949_; lean_object* v___f_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v___x_939_);
v_toApplicative_942_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_942_);
v_toBind_943_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_943_);
lean_dec_ref(v_inst_776_);
v_getRef_944_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getRef_944_);
lean_dec_ref(v_inst_777_);
v_toPure_945_ = lean_ctor_get(v_toApplicative_942_, 1);
lean_inc(v_toPure_945_);
lean_dec_ref(v_toApplicative_942_);
lean_inc(v_toPure_945_);
v___f_946_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_946_, 0, v_toPure_945_);
lean_closure_set(v___f_946_, 1, v_x_779_);
lean_inc(v_toBind_943_);
lean_inc_ref(v_inst_778_);
v___f_947_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_947_, 0, v_inst_778_);
lean_closure_set(v___f_947_, 1, v_toBind_943_);
lean_closure_set(v___f_947_, 2, v___f_946_);
lean_inc(v_toBind_943_);
v___f_948_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_948_, 0, v_inst_778_);
lean_closure_set(v___f_948_, 1, v_toBind_943_);
lean_closure_set(v___f_948_, 2, v___f_947_);
v___x_949_ = lean_box(v___x_941_);
v___f_950_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_950_, 0, v___x_949_);
lean_closure_set(v___f_950_, 1, v_toPure_945_);
lean_inc(v_toBind_943_);
v___x_951_ = lean_apply_4(v_toBind_943_, lean_box(0), lean_box(0), v_getRef_944_, v___f_950_);
v___x_952_ = lean_apply_4(v_toBind_943_, lean_box(0), lean_box(0), v___x_951_, v___f_948_);
return v___x_952_;
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_953_ = l_Lean_Syntax_getArg(v___x_939_, v___x_923_);
lean_dec(v___x_939_);
v___x_954_ = lean_box(0);
v___x_955_ = l_Lean_Syntax_matchesIdent(v___x_953_, v___x_954_);
lean_dec(v___x_953_);
if (v___x_955_ == 0)
{
lean_object* v_toApplicative_956_; lean_object* v_toBind_957_; lean_object* v_getRef_958_; lean_object* v_toPure_959_; lean_object* v___f_960_; lean_object* v___f_961_; lean_object* v___f_962_; lean_object* v___x_963_; lean_object* v___f_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_toApplicative_956_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_956_);
v_toBind_957_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_957_);
lean_dec_ref(v_inst_776_);
v_getRef_958_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getRef_958_);
lean_dec_ref(v_inst_777_);
v_toPure_959_ = lean_ctor_get(v_toApplicative_956_, 1);
lean_inc(v_toPure_959_);
lean_dec_ref(v_toApplicative_956_);
lean_inc(v_toPure_959_);
v___f_960_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_960_, 0, v_toPure_959_);
lean_closure_set(v___f_960_, 1, v_x_779_);
lean_inc(v_toBind_957_);
lean_inc_ref(v_inst_778_);
v___f_961_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_961_, 0, v_inst_778_);
lean_closure_set(v___f_961_, 1, v_toBind_957_);
lean_closure_set(v___f_961_, 2, v___f_960_);
lean_inc(v_toBind_957_);
v___f_962_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_962_, 0, v_inst_778_);
lean_closure_set(v___f_962_, 1, v_toBind_957_);
lean_closure_set(v___f_962_, 2, v___f_961_);
v___x_963_ = lean_box(v___x_955_);
v___f_964_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_964_, 0, v___x_963_);
lean_closure_set(v___f_964_, 1, v_toPure_959_);
lean_inc(v_toBind_957_);
v___x_965_ = lean_apply_4(v_toBind_957_, lean_box(0), lean_box(0), v_getRef_958_, v___f_964_);
v___x_966_ = lean_apply_4(v_toBind_957_, lean_box(0), lean_box(0), v___x_965_, v___f_962_);
return v___x_966_;
}
else
{
lean_object* v_toApplicative_967_; lean_object* v_toBind_968_; lean_object* v_P_969_; lean_object* v___x_970_; lean_object* v___f_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_toApplicative_967_ = lean_ctor_get(v_inst_776_, 0);
v_toBind_968_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_968_);
v_P_969_ = l_Lean_Syntax_getArg(v_x_779_, v___x_938_);
lean_dec(v_x_779_);
v___x_970_ = lean_box(v___x_783_);
lean_inc(v_toBind_968_);
lean_inc_ref(v_inst_778_);
lean_inc_ref(v_toApplicative_967_);
lean_inc_ref(v_inst_777_);
v___f_971_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed), 14, 13);
lean_closure_set(v___f_971_, 0, v_inst_777_);
lean_closure_set(v___f_971_, 1, v_toApplicative_967_);
lean_closure_set(v___f_971_, 2, v_inst_778_);
lean_closure_set(v___f_971_, 3, v___x_954_);
lean_closure_set(v___f_971_, 4, v___x_780_);
lean_closure_set(v___f_971_, 5, v___x_781_);
lean_closure_set(v___f_971_, 6, v___x_784_);
lean_closure_set(v___f_971_, 7, v___x_785_);
lean_closure_set(v___f_971_, 8, v___x_940_);
lean_closure_set(v___f_971_, 9, v___x_925_);
lean_closure_set(v___f_971_, 10, v___x_786_);
lean_closure_set(v___f_971_, 11, v_toBind_968_);
lean_closure_set(v___f_971_, 12, v___x_970_);
v___x_972_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_P_969_);
v___x_973_ = lean_apply_4(v_toBind_968_, lean_box(0), lean_box(0), v___x_972_, v___f_971_);
return v___x_973_;
}
}
}
}
}
else
{
lean_object* v_toApplicative_974_; lean_object* v_toBind_975_; lean_object* v_getRef_976_; lean_object* v_toPure_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___f_980_; lean_object* v___f_981_; lean_object* v___f_982_; lean_object* v___f_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_toApplicative_974_ = lean_ctor_get(v_inst_776_, 0);
lean_inc_ref(v_toApplicative_974_);
v_toBind_975_ = lean_ctor_get(v_inst_776_, 1);
lean_inc(v_toBind_975_);
lean_dec_ref(v_inst_776_);
v_getRef_976_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getRef_976_);
lean_dec_ref(v_inst_777_);
v_toPure_977_ = lean_ctor_get(v_toApplicative_974_, 1);
lean_inc(v_toPure_977_);
lean_dec_ref(v_toApplicative_974_);
v___x_978_ = lean_unsigned_to_nat(1u);
v___x_979_ = l_Lean_Syntax_getArg(v_x_779_, v___x_978_);
lean_dec(v_x_779_);
lean_inc(v_toPure_977_);
v___f_980_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__17___boxed), 3, 2);
lean_closure_set(v___f_980_, 0, v_toPure_977_);
lean_closure_set(v___f_980_, 1, v___x_979_);
lean_inc(v_toBind_975_);
lean_inc_ref(v_inst_778_);
v___f_981_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_981_, 0, v_inst_778_);
lean_closure_set(v___f_981_, 1, v_toBind_975_);
lean_closure_set(v___f_981_, 2, v___f_980_);
lean_inc(v_toBind_975_);
v___f_982_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_982_, 0, v_inst_778_);
lean_closure_set(v___f_982_, 1, v_toBind_975_);
lean_closure_set(v___f_982_, 2, v___f_981_);
v___f_983_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__22___boxed), 2, 1);
lean_closure_set(v___f_983_, 0, v_toPure_977_);
lean_inc(v_toBind_975_);
v___x_984_ = lean_apply_4(v_toBind_975_, lean_box(0), lean_box(0), v_getRef_976_, v___f_983_);
v___x_985_ = lean_apply_4(v_toBind_975_, lean_box(0), lean_box(0), v___x_984_, v___f_982_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11(lean_object* v_inst_986_, lean_object* v_toApplicative_987_, lean_object* v_inst_988_, lean_object* v___x_989_, lean_object* v___x_990_, lean_object* v_toBind_991_, uint8_t v___x_992_, lean_object* v_inst_993_, lean_object* v_e_994_, lean_object* v_t_995_){
_start:
{
lean_object* v___x_996_; lean_object* v___f_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_996_ = lean_box(v___x_992_);
lean_inc(v_toBind_991_);
lean_inc_ref(v_inst_988_);
lean_inc_ref(v_inst_986_);
v___f_997_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_997_, 0, v_inst_986_);
lean_closure_set(v___f_997_, 1, v_toApplicative_987_);
lean_closure_set(v___f_997_, 2, v_inst_988_);
lean_closure_set(v___f_997_, 3, v___x_989_);
lean_closure_set(v___f_997_, 4, v___x_990_);
lean_closure_set(v___f_997_, 5, v_t_995_);
lean_closure_set(v___f_997_, 6, v_toBind_991_);
lean_closure_set(v___f_997_, 7, v___x_996_);
v___x_998_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_993_, v_inst_986_, v_inst_988_, v_e_994_);
v___x_999_ = lean_apply_4(v_toBind_991_, lean_box(0), lean_box(0), v___x_998_, v___f_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack(lean_object* v_m_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_1001_, v_inst_1002_, v_inst_1003_, v_x_1004_);
return v___x_1005_;
}
}
lean_object* runtime_initialize_Std_Do_SPred_SPred(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_SPred_Notation_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
