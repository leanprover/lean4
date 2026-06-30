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
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__3(uint8_t v___x_359_, lean_object* v_toPure_360_, lean_object* v_____do__lift_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l_Lean_SourceInfo_fromRef(v_____do__lift_361_, v___x_359_);
v___x_363_ = lean_apply_2(v_toPure_360_, lean_box(0), v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed(lean_object* v___x_364_, lean_object* v_toPure_365_, lean_object* v_____do__lift_366_){
_start:
{
uint8_t v___x_9844__boxed_367_; lean_object* v_res_368_; 
v___x_9844__boxed_367_ = lean_unbox(v___x_364_);
v_res_368_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__3(v___x_9844__boxed_367_, v_toPure_365_, v_____do__lift_366_);
lean_dec(v_____do__lift_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__20(lean_object* v_info_371_, lean_object* v___x_372_, lean_object* v_scp_373_, lean_object* v___x_374_, lean_object* v___x_375_, lean_object* v___x_376_, lean_object* v___x_377_, lean_object* v___x_378_, lean_object* v___x_379_, lean_object* v___x_380_, lean_object* v___x_381_, lean_object* v_____do__lift_382_, lean_object* v_toPure_383_, lean_object* v_quotCtx_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_385_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15));
lean_inc_n(v_info_371_, 7);
v___x_386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_386_, 0, v_info_371_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
v___x_388_ = l_Lean_addMacroScope(v_quotCtx_384_, v___x_372_, v_scp_373_);
v___x_389_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0));
v___x_390_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1));
v___x_391_ = l_Lean_Name_mkStr4(v___x_374_, v___x_375_, v___x_389_, v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
v___x_393_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20));
lean_inc_ref_n(v___x_376_, 3);
v___x_394_ = l_Lean_Name_mkStr2(v___x_376_, v___x_393_);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
v___x_396_ = l_Lean_Name_mkStr2(v___x_376_, v___x_377_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
v___x_398_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25));
v___x_399_ = l_Lean_Name_mkStr2(v___x_376_, v___x_398_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
v___x_401_ = l_Lean_Name_mkStr1(v___x_376_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_400_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_397_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_395_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_392_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_409_, 0, v_info_371_);
lean_ctor_set(v___x_409_, 1, v___x_387_);
lean_ctor_set(v___x_409_, 2, v___x_388_);
lean_ctor_set(v___x_409_, 3, v___x_408_);
v___x_410_ = l_Lean_Syntax_node1(v_info_371_, v___x_378_, v___x_409_);
v___x_411_ = l_Lean_Syntax_node2(v_info_371_, v___x_379_, v___x_386_, v___x_410_);
v___x_412_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35));
v___x_413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_413_, 0, v_info_371_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37));
v___x_415_ = l_Lean_Syntax_node1(v_info_371_, v___x_414_, v___x_380_);
v___x_416_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
v___x_417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_417_, 0, v_info_371_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_Syntax_node5(v_info_371_, v___x_381_, v___x_411_, v_____do__lift_382_, v___x_413_, v___x_415_, v___x_417_);
v___x_419_ = lean_apply_2(v_toPure_383_, lean_box(0), v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__4(lean_object* v_info_420_, lean_object* v___x_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v___x_426_, lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v_____do__lift_430_, lean_object* v_toPure_431_, lean_object* v_toBind_432_, lean_object* v_getContext_433_, lean_object* v_scp_434_){
_start:
{
lean_object* v___f_435_; lean_object* v___x_436_; 
v___f_435_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__20), 14, 13);
lean_closure_set(v___f_435_, 0, v_info_420_);
lean_closure_set(v___f_435_, 1, v___x_421_);
lean_closure_set(v___f_435_, 2, v_scp_434_);
lean_closure_set(v___f_435_, 3, v___x_422_);
lean_closure_set(v___f_435_, 4, v___x_423_);
lean_closure_set(v___f_435_, 5, v___x_424_);
lean_closure_set(v___f_435_, 6, v___x_425_);
lean_closure_set(v___f_435_, 7, v___x_426_);
lean_closure_set(v___f_435_, 8, v___x_427_);
lean_closure_set(v___f_435_, 9, v___x_428_);
lean_closure_set(v___f_435_, 10, v___x_429_);
lean_closure_set(v___f_435_, 11, v_____do__lift_430_);
lean_closure_set(v___f_435_, 12, v_toPure_431_);
v___x_436_ = lean_apply_4(v_toBind_432_, lean_box(0), lean_box(0), v_getContext_433_, v___f_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__5(lean_object* v_inst_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v___x_445_, lean_object* v___x_446_, lean_object* v_____do__lift_447_, lean_object* v_toPure_448_, lean_object* v_toBind_449_, lean_object* v_info_450_){
_start:
{
lean_object* v_getCurrMacroScope_451_; lean_object* v_getContext_452_; lean_object* v___f_453_; lean_object* v___x_454_; 
v_getCurrMacroScope_451_ = lean_ctor_get(v_inst_437_, 1);
lean_inc(v_getCurrMacroScope_451_);
v_getContext_452_ = lean_ctor_get(v_inst_437_, 2);
lean_inc(v_getContext_452_);
lean_dec_ref(v_inst_437_);
lean_inc(v_toBind_449_);
v___f_453_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__4), 15, 14);
lean_closure_set(v___f_453_, 0, v_info_450_);
lean_closure_set(v___f_453_, 1, v___x_438_);
lean_closure_set(v___f_453_, 2, v___x_439_);
lean_closure_set(v___f_453_, 3, v___x_440_);
lean_closure_set(v___f_453_, 4, v___x_441_);
lean_closure_set(v___f_453_, 5, v___x_442_);
lean_closure_set(v___f_453_, 6, v___x_443_);
lean_closure_set(v___f_453_, 7, v___x_444_);
lean_closure_set(v___f_453_, 8, v___x_445_);
lean_closure_set(v___f_453_, 9, v___x_446_);
lean_closure_set(v___f_453_, 10, v_____do__lift_447_);
lean_closure_set(v___f_453_, 11, v_toPure_448_);
lean_closure_set(v___f_453_, 12, v_toBind_449_);
lean_closure_set(v___f_453_, 13, v_getContext_452_);
v___x_454_ = lean_apply_4(v_toBind_449_, lean_box(0), lean_box(0), v_getCurrMacroScope_451_, v___f_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7(lean_object* v_inst_455_, lean_object* v_toApplicative_456_, lean_object* v_inst_457_, lean_object* v___x_458_, lean_object* v___x_459_, lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v___x_463_, lean_object* v___x_464_, lean_object* v___x_465_, lean_object* v___x_466_, lean_object* v_toBind_467_, uint8_t v___x_468_, lean_object* v_____do__lift_469_){
_start:
{
lean_object* v_getRef_470_; lean_object* v_toPure_471_; lean_object* v___f_472_; lean_object* v___x_473_; lean_object* v___f_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_getRef_470_ = lean_ctor_get(v_inst_455_, 0);
lean_inc(v_getRef_470_);
lean_dec_ref(v_inst_455_);
v_toPure_471_ = lean_ctor_get(v_toApplicative_456_, 1);
lean_inc_n(v_toPure_471_, 2);
lean_dec_ref(v_toApplicative_456_);
lean_inc_n(v_toBind_467_, 2);
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
lean_closure_set(v___f_472_, 10, v_____do__lift_469_);
lean_closure_set(v___f_472_, 11, v_toPure_471_);
lean_closure_set(v___f_472_, 12, v_toBind_467_);
v___x_473_ = lean_box(v___x_468_);
v___f_474_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_474_, 0, v___x_473_);
lean_closure_set(v___f_474_, 1, v_toPure_471_);
v___x_475_ = lean_apply_4(v_toBind_467_, lean_box(0), lean_box(0), v_getRef_470_, v___f_474_);
v___x_476_ = lean_apply_4(v_toBind_467_, lean_box(0), lean_box(0), v___x_475_, v___f_472_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed(lean_object* v_inst_477_, lean_object* v_toApplicative_478_, lean_object* v_inst_479_, lean_object* v___x_480_, lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v___x_488_, lean_object* v_toBind_489_, lean_object* v___x_490_, lean_object* v_____do__lift_491_){
_start:
{
uint8_t v___x_10034__boxed_492_; lean_object* v_res_493_; 
v___x_10034__boxed_492_ = lean_unbox(v___x_490_);
v_res_493_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__7(v_inst_477_, v_toApplicative_478_, v_inst_479_, v___x_480_, v___x_481_, v___x_482_, v___x_483_, v___x_484_, v___x_485_, v___x_486_, v___x_487_, v___x_488_, v_toBind_489_, v___x_10034__boxed_492_, v_____do__lift_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__15(lean_object* v_info_494_, lean_object* v___x_495_, lean_object* v_xs_496_, lean_object* v___x_497_, lean_object* v_b_498_, lean_object* v___x_499_, lean_object* v_toPure_500_, lean_object* v_quotCtx_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_inc_n(v_info_494_, 5);
v___x_502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_502_, 0, v_info_494_);
lean_ctor_set(v___x_502_, 1, v___x_495_);
v___x_503_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37));
v___x_504_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43);
v___x_505_ = l_Array_append___redArg(v___x_504_, v_xs_496_);
v___x_506_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_506_, 0, v_info_494_);
lean_ctor_set(v___x_506_, 1, v___x_503_);
lean_ctor_set(v___x_506_, 2, v___x_505_);
v___x_507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_507_, 0, v_info_494_);
lean_ctor_set(v___x_507_, 1, v___x_503_);
lean_ctor_set(v___x_507_, 2, v___x_504_);
v___x_508_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44));
v___x_509_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_509_, 0, v_info_494_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = l_Lean_Syntax_node4(v_info_494_, v___x_497_, v___x_506_, v___x_507_, v___x_509_, v_b_498_);
v___x_511_ = l_Lean_Syntax_node2(v_info_494_, v___x_499_, v___x_502_, v___x_510_);
v___x_512_ = lean_apply_2(v_toPure_500_, lean_box(0), v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__15___boxed(lean_object* v_info_513_, lean_object* v___x_514_, lean_object* v_xs_515_, lean_object* v___x_516_, lean_object* v_b_517_, lean_object* v___x_518_, lean_object* v_toPure_519_, lean_object* v_quotCtx_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__15(v_info_513_, v___x_514_, v_xs_515_, v___x_516_, v_b_517_, v___x_518_, v_toPure_519_, v_quotCtx_520_);
lean_dec(v_quotCtx_520_);
lean_dec_ref(v_xs_515_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__6(lean_object* v_toBind_522_, lean_object* v_getContext_523_, lean_object* v___f_524_, lean_object* v_scp_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_apply_4(v_toBind_522_, lean_box(0), lean_box(0), v_getContext_523_, v___f_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed(lean_object* v_toBind_527_, lean_object* v_getContext_528_, lean_object* v___f_529_, lean_object* v_scp_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__6(v_toBind_527_, v_getContext_528_, v___f_529_, v_scp_530_);
lean_dec(v_scp_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__8(lean_object* v_inst_532_, lean_object* v___x_533_, lean_object* v_xs_534_, lean_object* v___x_535_, lean_object* v_b_536_, lean_object* v___x_537_, lean_object* v_toPure_538_, lean_object* v_toBind_539_, lean_object* v_info_540_){
_start:
{
lean_object* v_getCurrMacroScope_541_; lean_object* v_getContext_542_; lean_object* v___f_543_; lean_object* v___f_544_; lean_object* v___x_545_; 
v_getCurrMacroScope_541_ = lean_ctor_get(v_inst_532_, 1);
lean_inc(v_getCurrMacroScope_541_);
v_getContext_542_ = lean_ctor_get(v_inst_532_, 2);
lean_inc(v_getContext_542_);
lean_dec_ref(v_inst_532_);
v___f_543_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__15___boxed), 8, 7);
lean_closure_set(v___f_543_, 0, v_info_540_);
lean_closure_set(v___f_543_, 1, v___x_533_);
lean_closure_set(v___f_543_, 2, v_xs_534_);
lean_closure_set(v___f_543_, 3, v___x_535_);
lean_closure_set(v___f_543_, 4, v_b_536_);
lean_closure_set(v___f_543_, 5, v___x_537_);
lean_closure_set(v___f_543_, 6, v_toPure_538_);
lean_inc(v_toBind_539_);
v___f_544_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed), 4, 3);
lean_closure_set(v___f_544_, 0, v_toBind_539_);
lean_closure_set(v___f_544_, 1, v_getContext_542_);
lean_closure_set(v___f_544_, 2, v___f_543_);
v___x_545_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v_getCurrMacroScope_541_, v___f_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__10(lean_object* v_inst_546_, lean_object* v_toApplicative_547_, lean_object* v_inst_548_, lean_object* v___x_549_, lean_object* v_xs_550_, lean_object* v___x_551_, lean_object* v___x_552_, lean_object* v_toBind_553_, uint8_t v___x_554_, lean_object* v_b_555_){
_start:
{
lean_object* v_getRef_556_; lean_object* v_toPure_557_; lean_object* v___f_558_; lean_object* v___x_559_; lean_object* v___f_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_getRef_556_ = lean_ctor_get(v_inst_546_, 0);
lean_inc(v_getRef_556_);
lean_dec_ref(v_inst_546_);
v_toPure_557_ = lean_ctor_get(v_toApplicative_547_, 1);
lean_inc_n(v_toPure_557_, 2);
lean_dec_ref(v_toApplicative_547_);
lean_inc_n(v_toBind_553_, 2);
v___f_558_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__8), 9, 8);
lean_closure_set(v___f_558_, 0, v_inst_548_);
lean_closure_set(v___f_558_, 1, v___x_549_);
lean_closure_set(v___f_558_, 2, v_xs_550_);
lean_closure_set(v___f_558_, 3, v___x_551_);
lean_closure_set(v___f_558_, 4, v_b_555_);
lean_closure_set(v___f_558_, 5, v___x_552_);
lean_closure_set(v___f_558_, 6, v_toPure_557_);
lean_closure_set(v___f_558_, 7, v_toBind_553_);
v___x_559_ = lean_box(v___x_554_);
v___f_560_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_560_, 0, v___x_559_);
lean_closure_set(v___f_560_, 1, v_toPure_557_);
v___x_561_ = lean_apply_4(v_toBind_553_, lean_box(0), lean_box(0), v_getRef_556_, v___f_560_);
v___x_562_ = lean_apply_4(v_toBind_553_, lean_box(0), lean_box(0), v___x_561_, v___f_558_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__10___boxed(lean_object* v_inst_563_, lean_object* v_toApplicative_564_, lean_object* v_inst_565_, lean_object* v___x_566_, lean_object* v_xs_567_, lean_object* v___x_568_, lean_object* v___x_569_, lean_object* v_toBind_570_, lean_object* v___x_571_, lean_object* v_b_572_){
_start:
{
uint8_t v___x_10144__boxed_573_; lean_object* v_res_574_; 
v___x_10144__boxed_573_ = lean_unbox(v___x_571_);
v_res_574_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__10(v_inst_563_, v_toApplicative_564_, v_inst_565_, v___x_566_, v_xs_567_, v___x_568_, v___x_569_, v_toBind_570_, v___x_10144__boxed_573_, v_b_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__9(lean_object* v_info_575_, lean_object* v___x_576_, lean_object* v___x_577_, lean_object* v_t_578_, lean_object* v_e_579_, lean_object* v_toPure_580_, lean_object* v_quotCtx_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_582_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38));
lean_inc_n(v_info_575_, 3);
v___x_583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_583_, 0, v_info_575_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39));
v___x_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_585_, 0, v_info_575_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40));
v___x_587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_587_, 0, v_info_575_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l_Lean_Syntax_node6(v_info_575_, v___x_576_, v___x_583_, v___x_577_, v___x_585_, v_t_578_, v___x_587_, v_e_579_);
v___x_589_ = lean_apply_2(v_toPure_580_, lean_box(0), v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__9___boxed(lean_object* v_info_590_, lean_object* v___x_591_, lean_object* v___x_592_, lean_object* v_t_593_, lean_object* v_e_594_, lean_object* v_toPure_595_, lean_object* v_quotCtx_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__9(v_info_590_, v___x_591_, v___x_592_, v_t_593_, v_e_594_, v_toPure_595_, v_quotCtx_596_);
lean_dec(v_quotCtx_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__12(lean_object* v_inst_598_, lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v_t_601_, lean_object* v_e_602_, lean_object* v_toPure_603_, lean_object* v_toBind_604_, lean_object* v_info_605_){
_start:
{
lean_object* v_getCurrMacroScope_606_; lean_object* v_getContext_607_; lean_object* v___f_608_; lean_object* v___f_609_; lean_object* v___x_610_; 
v_getCurrMacroScope_606_ = lean_ctor_get(v_inst_598_, 1);
lean_inc(v_getCurrMacroScope_606_);
v_getContext_607_ = lean_ctor_get(v_inst_598_, 2);
lean_inc(v_getContext_607_);
lean_dec_ref(v_inst_598_);
v___f_608_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_608_, 0, v_info_605_);
lean_closure_set(v___f_608_, 1, v___x_599_);
lean_closure_set(v___f_608_, 2, v___x_600_);
lean_closure_set(v___f_608_, 3, v_t_601_);
lean_closure_set(v___f_608_, 4, v_e_602_);
lean_closure_set(v___f_608_, 5, v_toPure_603_);
lean_inc(v_toBind_604_);
v___f_609_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed), 4, 3);
lean_closure_set(v___f_609_, 0, v_toBind_604_);
lean_closure_set(v___f_609_, 1, v_getContext_607_);
lean_closure_set(v___f_609_, 2, v___f_608_);
v___x_610_ = lean_apply_4(v_toBind_604_, lean_box(0), lean_box(0), v_getCurrMacroScope_606_, v___f_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__13(lean_object* v_inst_611_, lean_object* v_toApplicative_612_, lean_object* v_inst_613_, lean_object* v___x_614_, lean_object* v___x_615_, lean_object* v_t_616_, lean_object* v_toBind_617_, uint8_t v___x_618_, lean_object* v_e_619_){
_start:
{
lean_object* v_getRef_620_; lean_object* v_toPure_621_; lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___f_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_getRef_620_ = lean_ctor_get(v_inst_611_, 0);
lean_inc(v_getRef_620_);
lean_dec_ref(v_inst_611_);
v_toPure_621_ = lean_ctor_get(v_toApplicative_612_, 1);
lean_inc_n(v_toPure_621_, 2);
lean_dec_ref(v_toApplicative_612_);
lean_inc_n(v_toBind_617_, 2);
v___f_622_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__12), 8, 7);
lean_closure_set(v___f_622_, 0, v_inst_613_);
lean_closure_set(v___f_622_, 1, v___x_614_);
lean_closure_set(v___f_622_, 2, v___x_615_);
lean_closure_set(v___f_622_, 3, v_t_616_);
lean_closure_set(v___f_622_, 4, v_e_619_);
lean_closure_set(v___f_622_, 5, v_toPure_621_);
lean_closure_set(v___f_622_, 6, v_toBind_617_);
v___x_623_ = lean_box(v___x_618_);
v___f_624_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_624_, 0, v___x_623_);
lean_closure_set(v___f_624_, 1, v_toPure_621_);
v___x_625_ = lean_apply_4(v_toBind_617_, lean_box(0), lean_box(0), v_getRef_620_, v___f_624_);
v___x_626_ = lean_apply_4(v_toBind_617_, lean_box(0), lean_box(0), v___x_625_, v___f_622_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__13___boxed(lean_object* v_inst_627_, lean_object* v_toApplicative_628_, lean_object* v_inst_629_, lean_object* v___x_630_, lean_object* v___x_631_, lean_object* v_t_632_, lean_object* v_toBind_633_, lean_object* v___x_634_, lean_object* v_e_635_){
_start:
{
uint8_t v___x_10216__boxed_636_; lean_object* v_res_637_; 
v___x_10216__boxed_636_ = lean_unbox(v___x_634_);
v_res_637_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__13(v_inst_627_, v_toApplicative_628_, v_inst_629_, v___x_630_, v___x_631_, v_t_632_, v_toBind_633_, v___x_10216__boxed_636_, v_e_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__28(lean_object* v_info_638_, lean_object* v___x_639_, lean_object* v_scp_640_, lean_object* v___x_641_, lean_object* v___x_642_, lean_object* v___x_643_, lean_object* v___x_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v___x_647_, lean_object* v_____do__lift_648_, lean_object* v_toPure_649_, lean_object* v_quotCtx_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_651_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15));
lean_inc_n(v_info_638_, 5);
v___x_652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_652_, 0, v_info_638_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
v___x_654_ = l_Lean_addMacroScope(v_quotCtx_650_, v___x_639_, v_scp_640_);
v___x_655_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0));
v___x_656_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1));
v___x_657_ = l_Lean_Name_mkStr4(v___x_641_, v___x_642_, v___x_655_, v___x_656_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
v___x_659_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20));
lean_inc_ref_n(v___x_643_, 3);
v___x_660_ = l_Lean_Name_mkStr2(v___x_643_, v___x_659_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
v___x_662_ = l_Lean_Name_mkStr2(v___x_643_, v___x_644_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
v___x_664_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25));
v___x_665_ = l_Lean_Name_mkStr2(v___x_643_, v___x_664_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
v___x_667_ = l_Lean_Name_mkStr1(v___x_643_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
v___x_669_ = lean_box(0);
v___x_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_666_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_663_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_661_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_658_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_675_, 0, v_info_638_);
lean_ctor_set(v___x_675_, 1, v___x_653_);
lean_ctor_set(v___x_675_, 2, v___x_654_);
lean_ctor_set(v___x_675_, 3, v___x_674_);
v___x_676_ = l_Lean_Syntax_node1(v_info_638_, v___x_645_, v___x_675_);
v___x_677_ = l_Lean_Syntax_node2(v_info_638_, v___x_646_, v___x_652_, v___x_676_);
v___x_678_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
v___x_679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_679_, 0, v_info_638_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = l_Lean_Syntax_node3(v_info_638_, v___x_647_, v___x_677_, v_____do__lift_648_, v___x_679_);
v___x_681_ = lean_apply_2(v_toPure_649_, lean_box(0), v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__14(lean_object* v_info_682_, lean_object* v___x_683_, lean_object* v___x_684_, lean_object* v___x_685_, lean_object* v___x_686_, lean_object* v___x_687_, lean_object* v___x_688_, lean_object* v___x_689_, lean_object* v___x_690_, lean_object* v_____do__lift_691_, lean_object* v_toPure_692_, lean_object* v_toBind_693_, lean_object* v_getContext_694_, lean_object* v_scp_695_){
_start:
{
lean_object* v___f_696_; lean_object* v___x_697_; 
v___f_696_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__28), 13, 12);
lean_closure_set(v___f_696_, 0, v_info_682_);
lean_closure_set(v___f_696_, 1, v___x_683_);
lean_closure_set(v___f_696_, 2, v_scp_695_);
lean_closure_set(v___f_696_, 3, v___x_684_);
lean_closure_set(v___f_696_, 4, v___x_685_);
lean_closure_set(v___f_696_, 5, v___x_686_);
lean_closure_set(v___f_696_, 6, v___x_687_);
lean_closure_set(v___f_696_, 7, v___x_688_);
lean_closure_set(v___f_696_, 8, v___x_689_);
lean_closure_set(v___f_696_, 9, v___x_690_);
lean_closure_set(v___f_696_, 10, v_____do__lift_691_);
lean_closure_set(v___f_696_, 11, v_toPure_692_);
v___x_697_ = lean_apply_4(v_toBind_693_, lean_box(0), lean_box(0), v_getContext_694_, v___f_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__16(lean_object* v_inst_698_, lean_object* v___x_699_, lean_object* v___x_700_, lean_object* v___x_701_, lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v_____do__lift_707_, lean_object* v_toPure_708_, lean_object* v_toBind_709_, lean_object* v_info_710_){
_start:
{
lean_object* v_getCurrMacroScope_711_; lean_object* v_getContext_712_; lean_object* v___f_713_; lean_object* v___x_714_; 
v_getCurrMacroScope_711_ = lean_ctor_get(v_inst_698_, 1);
lean_inc(v_getCurrMacroScope_711_);
v_getContext_712_ = lean_ctor_get(v_inst_698_, 2);
lean_inc(v_getContext_712_);
lean_dec_ref(v_inst_698_);
lean_inc(v_toBind_709_);
v___f_713_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__14), 14, 13);
lean_closure_set(v___f_713_, 0, v_info_710_);
lean_closure_set(v___f_713_, 1, v___x_699_);
lean_closure_set(v___f_713_, 2, v___x_700_);
lean_closure_set(v___f_713_, 3, v___x_701_);
lean_closure_set(v___f_713_, 4, v___x_702_);
lean_closure_set(v___f_713_, 5, v___x_703_);
lean_closure_set(v___f_713_, 6, v___x_704_);
lean_closure_set(v___f_713_, 7, v___x_705_);
lean_closure_set(v___f_713_, 8, v___x_706_);
lean_closure_set(v___f_713_, 9, v_____do__lift_707_);
lean_closure_set(v___f_713_, 10, v_toPure_708_);
lean_closure_set(v___f_713_, 11, v_toBind_709_);
lean_closure_set(v___f_713_, 12, v_getContext_712_);
v___x_714_ = lean_apply_4(v_toBind_709_, lean_box(0), lean_box(0), v_getCurrMacroScope_711_, v___f_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18(lean_object* v_inst_715_, lean_object* v_toApplicative_716_, lean_object* v_inst_717_, lean_object* v___x_718_, lean_object* v___x_719_, lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v___x_723_, lean_object* v___x_724_, lean_object* v___x_725_, lean_object* v_toBind_726_, uint8_t v___x_727_, lean_object* v_____do__lift_728_){
_start:
{
lean_object* v_getRef_729_; lean_object* v_toPure_730_; lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_getRef_729_ = lean_ctor_get(v_inst_715_, 0);
lean_inc(v_getRef_729_);
lean_dec_ref(v_inst_715_);
v_toPure_730_ = lean_ctor_get(v_toApplicative_716_, 1);
lean_inc_n(v_toPure_730_, 2);
lean_dec_ref(v_toApplicative_716_);
lean_inc_n(v_toBind_726_, 2);
v___f_731_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__16), 13, 12);
lean_closure_set(v___f_731_, 0, v_inst_717_);
lean_closure_set(v___f_731_, 1, v___x_718_);
lean_closure_set(v___f_731_, 2, v___x_719_);
lean_closure_set(v___f_731_, 3, v___x_720_);
lean_closure_set(v___f_731_, 4, v___x_721_);
lean_closure_set(v___f_731_, 5, v___x_722_);
lean_closure_set(v___f_731_, 6, v___x_723_);
lean_closure_set(v___f_731_, 7, v___x_724_);
lean_closure_set(v___f_731_, 8, v___x_725_);
lean_closure_set(v___f_731_, 9, v_____do__lift_728_);
lean_closure_set(v___f_731_, 10, v_toPure_730_);
lean_closure_set(v___f_731_, 11, v_toBind_726_);
v___x_732_ = lean_box(v___x_727_);
v___f_733_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_733_, 0, v___x_732_);
lean_closure_set(v___f_733_, 1, v_toPure_730_);
v___x_734_ = lean_apply_4(v_toBind_726_, lean_box(0), lean_box(0), v_getRef_729_, v___f_733_);
v___x_735_ = lean_apply_4(v_toBind_726_, lean_box(0), lean_box(0), v___x_734_, v___f_731_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed(lean_object* v_inst_736_, lean_object* v_toApplicative_737_, lean_object* v_inst_738_, lean_object* v___x_739_, lean_object* v___x_740_, lean_object* v___x_741_, lean_object* v___x_742_, lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v___x_745_, lean_object* v___x_746_, lean_object* v_toBind_747_, lean_object* v___x_748_, lean_object* v_____do__lift_749_){
_start:
{
uint8_t v___x_10395__boxed_750_; lean_object* v_res_751_; 
v___x_10395__boxed_750_ = lean_unbox(v___x_748_);
v_res_751_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__18(v_inst_736_, v_toApplicative_737_, v_inst_738_, v___x_739_, v___x_740_, v___x_741_, v___x_742_, v___x_743_, v___x_744_, v___x_745_, v___x_746_, v_toBind_747_, v___x_10395__boxed_750_, v_____do__lift_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__22(lean_object* v_toPure_752_, lean_object* v_____do__lift_753_){
_start:
{
uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = 0;
v___x_755_ = l_Lean_SourceInfo_fromRef(v_____do__lift_753_, v___x_754_);
v___x_756_ = lean_apply_2(v_toPure_752_, lean_box(0), v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__22___boxed(lean_object* v_toPure_757_, lean_object* v_____do__lift_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__22(v_toPure_757_, v_____do__lift_758_);
lean_dec(v_____do__lift_758_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__17(lean_object* v_toPure_760_, lean_object* v___x_761_, lean_object* v_quotCtx_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = lean_apply_2(v_toPure_760_, lean_box(0), v___x_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__17___boxed(lean_object* v_toPure_764_, lean_object* v___x_765_, lean_object* v_quotCtx_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__17(v_toPure_764_, v___x_765_, v_quotCtx_766_);
lean_dec(v_quotCtx_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed(lean_object* v_inst_768_, lean_object* v_toApplicative_769_, lean_object* v_inst_770_, lean_object* v___x_771_, lean_object* v___x_772_, lean_object* v_toBind_773_, lean_object* v___x_774_, lean_object* v_inst_775_, lean_object* v_e_776_, lean_object* v_t_777_){
_start:
{
uint8_t v___x_10507__boxed_778_; lean_object* v_res_779_; 
v___x_10507__boxed_778_ = lean_unbox(v___x_774_);
v_res_779_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__11(v_inst_768_, v_toApplicative_769_, v_inst_770_, v___x_771_, v___x_772_, v_toBind_773_, v___x_10507__boxed_778_, v_inst_775_, v_e_776_, v_t_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg(lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_x_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_784_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__0));
v___x_785_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__1));
v___x_786_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__3));
lean_inc(v_x_783_);
v___x_787_ = l_Lean_Syntax_isOfKind(v_x_783_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_788_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0));
v___x_789_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1));
v___x_790_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4));
lean_inc(v_x_783_);
v___x_791_ = l_Lean_Syntax_isOfKind(v_x_783_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8));
lean_inc(v_x_783_);
v___x_793_ = l_Lean_Syntax_isOfKind(v_x_783_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_794_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5));
v___x_795_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6));
lean_inc(v_x_783_);
v___x_796_ = l_Lean_Syntax_isOfKind(v_x_783_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10));
lean_inc(v_x_783_);
v___x_798_ = l_Lean_Syntax_isOfKind(v_x_783_, v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v_toApplicative_799_; lean_object* v_toBind_800_; lean_object* v_getRef_801_; lean_object* v_toPure_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___f_805_; lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_toApplicative_799_ = lean_ctor_get(v_inst_780_, 0);
lean_inc_ref(v_toApplicative_799_);
v_toBind_800_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_800_, 4);
lean_dec_ref(v_inst_780_);
v_getRef_801_ = lean_ctor_get(v_inst_781_, 0);
lean_inc(v_getRef_801_);
lean_dec_ref(v_inst_781_);
v_toPure_802_ = lean_ctor_get(v_toApplicative_799_, 1);
lean_inc_n(v_toPure_802_, 2);
lean_dec_ref(v_toApplicative_799_);
v___f_803_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_803_, 0, v_toPure_802_);
lean_closure_set(v___f_803_, 1, v_x_783_);
lean_inc_ref(v_inst_782_);
v___f_804_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_804_, 0, v_inst_782_);
lean_closure_set(v___f_804_, 1, v_toBind_800_);
lean_closure_set(v___f_804_, 2, v___f_803_);
v___f_805_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_805_, 0, v_inst_782_);
lean_closure_set(v___f_805_, 1, v_toBind_800_);
lean_closure_set(v___f_805_, 2, v___f_804_);
v___x_806_ = lean_box(v___x_798_);
v___f_807_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_807_, 0, v___x_806_);
lean_closure_set(v___f_807_, 1, v_toPure_802_);
v___x_808_ = lean_apply_4(v_toBind_800_, lean_box(0), lean_box(0), v_getRef_801_, v___f_807_);
v___x_809_ = lean_apply_4(v_toBind_800_, lean_box(0), lean_box(0), v___x_808_, v___f_805_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = l_Lean_Syntax_getArg(v_x_783_, v___x_810_);
v___x_812_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12));
lean_inc(v___x_811_);
v___x_813_ = l_Lean_Syntax_isOfKind(v___x_811_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v_toApplicative_814_; lean_object* v_toBind_815_; lean_object* v_getRef_816_; lean_object* v_toPure_817_; lean_object* v___f_818_; lean_object* v___f_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec(v___x_811_);
v_toApplicative_814_ = lean_ctor_get(v_inst_780_, 0);
lean_inc_ref(v_toApplicative_814_);
v_toBind_815_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_815_, 4);
lean_dec_ref(v_inst_780_);
v_getRef_816_ = lean_ctor_get(v_inst_781_, 0);
lean_inc(v_getRef_816_);
lean_dec_ref(v_inst_781_);
v_toPure_817_ = lean_ctor_get(v_toApplicative_814_, 1);
lean_inc_n(v_toPure_817_, 2);
lean_dec_ref(v_toApplicative_814_);
v___f_818_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_818_, 0, v_toPure_817_);
lean_closure_set(v___f_818_, 1, v_x_783_);
lean_inc_ref(v_inst_782_);
v___f_819_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_819_, 0, v_inst_782_);
lean_closure_set(v___f_819_, 1, v_toBind_815_);
lean_closure_set(v___f_819_, 2, v___f_818_);
v___f_820_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_820_, 0, v_inst_782_);
lean_closure_set(v___f_820_, 1, v_toBind_815_);
lean_closure_set(v___f_820_, 2, v___f_819_);
v___x_821_ = lean_box(v___x_813_);
v___f_822_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_822_, 0, v___x_821_);
lean_closure_set(v___f_822_, 1, v_toPure_817_);
v___x_823_ = lean_apply_4(v_toBind_815_, lean_box(0), lean_box(0), v_getRef_816_, v___f_822_);
v___x_824_ = lean_apply_4(v_toBind_815_, lean_box(0), lean_box(0), v___x_823_, v___f_820_);
return v___x_824_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = l_Lean_Syntax_getArg(v___x_811_, v___x_825_);
lean_dec(v___x_811_);
v___x_827_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14));
lean_inc(v___x_826_);
v___x_828_ = l_Lean_Syntax_isOfKind(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v_toApplicative_829_; lean_object* v_toBind_830_; lean_object* v_getRef_831_; lean_object* v_toPure_832_; lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___f_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v___x_826_);
v_toApplicative_829_ = lean_ctor_get(v_inst_780_, 0);
lean_inc_ref(v_toApplicative_829_);
v_toBind_830_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_830_, 4);
lean_dec_ref(v_inst_780_);
v_getRef_831_ = lean_ctor_get(v_inst_781_, 0);
lean_inc(v_getRef_831_);
lean_dec_ref(v_inst_781_);
v_toPure_832_ = lean_ctor_get(v_toApplicative_829_, 1);
lean_inc_n(v_toPure_832_, 2);
lean_dec_ref(v_toApplicative_829_);
v___f_833_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_833_, 0, v_toPure_832_);
lean_closure_set(v___f_833_, 1, v_x_783_);
lean_inc_ref(v_inst_782_);
v___f_834_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_834_, 0, v_inst_782_);
lean_closure_set(v___f_834_, 1, v_toBind_830_);
lean_closure_set(v___f_834_, 2, v___f_833_);
v___f_835_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_835_, 0, v_inst_782_);
lean_closure_set(v___f_835_, 1, v_toBind_830_);
lean_closure_set(v___f_835_, 2, v___f_834_);
v___x_836_ = lean_box(v___x_828_);
v___f_837_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_837_, 0, v___x_836_);
lean_closure_set(v___f_837_, 1, v_toPure_832_);
v___x_838_ = lean_apply_4(v_toBind_830_, lean_box(0), lean_box(0), v_getRef_831_, v___f_837_);
v___x_839_ = lean_apply_4(v_toBind_830_, lean_box(0), lean_box(0), v___x_838_, v___f_835_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_840_ = l_Lean_Syntax_getArg(v___x_826_, v___x_810_);
lean_dec(v___x_826_);
v___x_841_ = lean_box(0);
v___x_842_ = l_Lean_Syntax_matchesIdent(v___x_840_, v___x_841_);
lean_dec(v___x_840_);
if (v___x_842_ == 0)
{
lean_object* v_toApplicative_843_; lean_object* v_toBind_844_; lean_object* v_getRef_845_; lean_object* v_toPure_846_; lean_object* v___f_847_; lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___x_850_; lean_object* v___f_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_toApplicative_843_ = lean_ctor_get(v_inst_780_, 0);
lean_inc_ref(v_toApplicative_843_);
v_toBind_844_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_844_, 4);
lean_dec_ref(v_inst_780_);
v_getRef_845_ = lean_ctor_get(v_inst_781_, 0);
lean_inc(v_getRef_845_);
lean_dec_ref(v_inst_781_);
v_toPure_846_ = lean_ctor_get(v_toApplicative_843_, 1);
lean_inc_n(v_toPure_846_, 2);
lean_dec_ref(v_toApplicative_843_);
v___f_847_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_847_, 0, v_toPure_846_);
lean_closure_set(v___f_847_, 1, v_x_783_);
lean_inc_ref(v_inst_782_);
v___f_848_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_848_, 0, v_inst_782_);
lean_closure_set(v___f_848_, 1, v_toBind_844_);
lean_closure_set(v___f_848_, 2, v___f_847_);
v___f_849_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_849_, 0, v_inst_782_);
lean_closure_set(v___f_849_, 1, v_toBind_844_);
lean_closure_set(v___f_849_, 2, v___f_848_);
v___x_850_ = lean_box(v___x_842_);
v___f_851_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_851_, 0, v___x_850_);
lean_closure_set(v___f_851_, 1, v_toPure_846_);
v___x_852_ = lean_apply_4(v_toBind_844_, lean_box(0), lean_box(0), v_getRef_845_, v___f_851_);
v___x_853_ = lean_apply_4(v_toBind_844_, lean_box(0), lean_box(0), v___x_852_, v___f_849_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_854_ = lean_unsigned_to_nat(3u);
v___x_855_ = l_Lean_Syntax_getArg(v_x_783_, v___x_854_);
lean_inc(v___x_855_);
v___x_856_ = l_Lean_Syntax_matchesNull(v___x_855_, v___x_825_);
if (v___x_856_ == 0)
{
lean_object* v_toApplicative_857_; lean_object* v_toBind_858_; lean_object* v_getRef_859_; lean_object* v_toPure_860_; lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___f_863_; lean_object* v___x_864_; lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v___x_855_);
v_toApplicative_857_ = lean_ctor_get(v_inst_780_, 0);
lean_inc_ref(v_toApplicative_857_);
v_toBind_858_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_858_, 4);
lean_dec_ref(v_inst_780_);
v_getRef_859_ = lean_ctor_get(v_inst_781_, 0);
lean_inc(v_getRef_859_);
lean_dec_ref(v_inst_781_);
v_toPure_860_ = lean_ctor_get(v_toApplicative_857_, 1);
lean_inc_n(v_toPure_860_, 2);
lean_dec_ref(v_toApplicative_857_);
v___f_861_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_861_, 0, v_toPure_860_);
lean_closure_set(v___f_861_, 1, v_x_783_);
lean_inc_ref(v_inst_782_);
v___f_862_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_862_, 0, v_inst_782_);
lean_closure_set(v___f_862_, 1, v_toBind_858_);
lean_closure_set(v___f_862_, 2, v___f_861_);
v___f_863_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_863_, 0, v_inst_782_);
lean_closure_set(v___f_863_, 1, v_toBind_858_);
lean_closure_set(v___f_863_, 2, v___f_862_);
v___x_864_ = lean_box(v___x_856_);
v___f_865_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_865_, 0, v___x_864_);
lean_closure_set(v___f_865_, 1, v_toPure_860_);
v___x_866_ = lean_apply_4(v_toBind_858_, lean_box(0), lean_box(0), v_getRef_859_, v___f_865_);
v___x_867_ = lean_apply_4(v_toBind_858_, lean_box(0), lean_box(0), v___x_866_, v___f_863_);
return v___x_867_;
}
else
{
lean_object* v_toApplicative_868_; lean_object* v_toBind_869_; lean_object* v_P_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_toApplicative_868_ = lean_ctor_get(v_inst_780_, 0);
v_toBind_869_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_869_, 2);
v_P_870_ = l_Lean_Syntax_getArg(v_x_783_, v___x_825_);
lean_dec(v_x_783_);
v___x_871_ = l_Lean_Syntax_getArg(v___x_855_, v___x_810_);
lean_dec(v___x_855_);
v___x_872_ = lean_box(v___x_796_);
lean_inc_ref(v_inst_782_);
lean_inc_ref(v_toApplicative_868_);
lean_inc_ref(v_inst_781_);
v___f_873_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed), 15, 14);
lean_closure_set(v___f_873_, 0, v_inst_781_);
lean_closure_set(v___f_873_, 1, v_toApplicative_868_);
lean_closure_set(v___f_873_, 2, v_inst_782_);
lean_closure_set(v___f_873_, 3, v___x_841_);
lean_closure_set(v___f_873_, 4, v___x_784_);
lean_closure_set(v___f_873_, 5, v___x_785_);
lean_closure_set(v___f_873_, 6, v___x_788_);
lean_closure_set(v___f_873_, 7, v___x_789_);
lean_closure_set(v___f_873_, 8, v___x_827_);
lean_closure_set(v___f_873_, 9, v___x_812_);
lean_closure_set(v___f_873_, 10, v___x_871_);
lean_closure_set(v___f_873_, 11, v___x_797_);
lean_closure_set(v___f_873_, 12, v_toBind_869_);
lean_closure_set(v___f_873_, 13, v___x_872_);
v___x_874_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_780_, v_inst_781_, v_inst_782_, v_P_870_);
v___x_875_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_874_, v___f_873_);
return v___x_875_;
}
}
}
}
}
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_876_ = lean_unsigned_to_nat(1u);
v___x_877_ = l_Lean_Syntax_getArg(v_x_783_, v___x_876_);
v___x_878_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42));
lean_inc(v___x_877_);
v___x_879_ = l_Lean_Syntax_isOfKind(v___x_877_, v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v_toApplicative_880_; lean_object* v_toBind_881_; lean_object* v_getRef_882_; lean_object* v_toPure_883_; lean_object* v___f_884_; lean_object* v___f_885_; lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v___x_877_);
v_toApplicative_880_ = lean_ctor_get(v_inst_780_, 0);
lean_inc_ref(v_toApplicative_880_);
v_toBind_881_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_881_, 4);
lean_dec_ref(v_inst_780_);
v_getRef_882_ = lean_ctor_get(v_inst_781_, 0);
lean_inc(v_getRef_882_);
lean_dec_ref(v_inst_781_);
v_toPure_883_ = lean_ctor_get(v_toApplicative_880_, 1);
lean_inc_n(v_toPure_883_, 2);
lean_dec_ref(v_toApplicative_880_);
v___f_884_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_884_, 0, v_toPure_883_);
lean_closure_set(v___f_884_, 1, v_x_783_);
lean_inc_ref(v_inst_782_);
v___f_885_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_885_, 0, v_inst_782_);
lean_closure_set(v___f_885_, 1, v_toBind_881_);
lean_closure_set(v___f_885_, 2, v___f_884_);
v___f_886_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_886_, 0, v_inst_782_);
lean_closure_set(v___f_886_, 1, v_toBind_881_);
lean_closure_set(v___f_886_, 2, v___f_885_);
v___x_887_ = lean_box(v___x_879_);
v___f_888_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_888_, 0, v___x_887_);
lean_closure_set(v___f_888_, 1, v_toPure_883_);
v___x_889_ = lean_apply_4(v_toBind_881_, lean_box(0), lean_box(0), v_getRef_882_, v___f_888_);
v___x_890_ = lean_apply_4(v_toBind_881_, lean_box(0), lean_box(0), v___x_889_, v___f_886_);
return v___x_890_;
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = l_Lean_Syntax_getArg(v___x_877_, v___x_876_);
v___x_893_ = l_Lean_Syntax_matchesNull(v___x_892_, v___x_891_);
if (v___x_893_ == 0)
{
lean_object* v_toApplicative_894_; lean_object* v_toBind_895_; lean_object* v_getRef_896_; lean_object* v_toPure_897_; lean_object* v___f_898_; lean_object* v___f_899_; lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v___f_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec(v___x_877_);
v_toApplicative_894_ = lean_ctor_get(v_inst_780_, 0);
lean_inc_ref(v_toApplicative_894_);
v_toBind_895_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_895_, 4);
lean_dec_ref(v_inst_780_);
v_getRef_896_ = lean_ctor_get(v_inst_781_, 0);
lean_inc(v_getRef_896_);
lean_dec_ref(v_inst_781_);
v_toPure_897_ = lean_ctor_get(v_toApplicative_894_, 1);
lean_inc_n(v_toPure_897_, 2);
lean_dec_ref(v_toApplicative_894_);
v___f_898_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_898_, 0, v_toPure_897_);
lean_closure_set(v___f_898_, 1, v_x_783_);
lean_inc_ref(v_inst_782_);
v___f_899_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_899_, 0, v_inst_782_);
lean_closure_set(v___f_899_, 1, v_toBind_895_);
lean_closure_set(v___f_899_, 2, v___f_898_);
v___f_900_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_900_, 0, v_inst_782_);
lean_closure_set(v___f_900_, 1, v_toBind_895_);
lean_closure_set(v___f_900_, 2, v___f_899_);
v___x_901_ = lean_box(v___x_893_);
v___f_902_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_902_, 0, v___x_901_);
lean_closure_set(v___f_902_, 1, v_toPure_897_);
v___x_903_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v_getRef_896_, v___f_902_);
v___x_904_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_903_, v___f_900_);
return v___x_904_;
}
else
{
lean_object* v_toApplicative_905_; lean_object* v_toBind_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_b_909_; lean_object* v_xs_910_; lean_object* v___x_911_; lean_object* v___f_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_x_783_);
v_toApplicative_905_ = lean_ctor_get(v_inst_780_, 0);
v_toBind_906_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_906_, 2);
v___x_907_ = l_Lean_Syntax_getArg(v___x_877_, v___x_891_);
v___x_908_ = lean_unsigned_to_nat(3u);
v_b_909_ = l_Lean_Syntax_getArg(v___x_877_, v___x_908_);
lean_dec(v___x_877_);
v_xs_910_ = l_Lean_Syntax_getArgs(v___x_907_);
lean_dec(v___x_907_);
v___x_911_ = lean_box(v___x_793_);
lean_inc_ref(v_inst_782_);
lean_inc_ref(v_toApplicative_905_);
lean_inc_ref(v_inst_781_);
v___f_912_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__10___boxed), 10, 9);
lean_closure_set(v___f_912_, 0, v_inst_781_);
lean_closure_set(v___f_912_, 1, v_toApplicative_905_);
lean_closure_set(v___f_912_, 2, v_inst_782_);
lean_closure_set(v___f_912_, 3, v___x_794_);
lean_closure_set(v___f_912_, 4, v_xs_910_);
lean_closure_set(v___f_912_, 5, v___x_878_);
lean_closure_set(v___f_912_, 6, v___x_795_);
lean_closure_set(v___f_912_, 7, v_toBind_906_);
lean_closure_set(v___f_912_, 8, v___x_911_);
v___x_913_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_780_, v_inst_781_, v_inst_782_, v_b_909_);
v___x_914_ = lean_apply_4(v_toBind_906_, lean_box(0), lean_box(0), v___x_913_, v___f_912_);
return v___x_914_;
}
}
}
}
else
{
lean_object* v_toApplicative_915_; lean_object* v_toBind_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_t_920_; lean_object* v___x_921_; lean_object* v_e_922_; lean_object* v___x_923_; lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_toApplicative_915_ = lean_ctor_get(v_inst_780_, 0);
v_toBind_916_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_916_, 2);
v___x_917_ = lean_unsigned_to_nat(1u);
v___x_918_ = l_Lean_Syntax_getArg(v_x_783_, v___x_917_);
v___x_919_ = lean_unsigned_to_nat(3u);
v_t_920_ = l_Lean_Syntax_getArg(v_x_783_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(5u);
v_e_922_ = l_Lean_Syntax_getArg(v_x_783_, v___x_921_);
lean_dec(v_x_783_);
v___x_923_ = lean_box(v___x_791_);
lean_inc_ref(v_inst_780_);
lean_inc_ref(v_inst_782_);
lean_inc_ref(v_toApplicative_915_);
lean_inc_ref(v_inst_781_);
v___f_924_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed), 10, 9);
lean_closure_set(v___f_924_, 0, v_inst_781_);
lean_closure_set(v___f_924_, 1, v_toApplicative_915_);
lean_closure_set(v___f_924_, 2, v_inst_782_);
lean_closure_set(v___f_924_, 3, v___x_792_);
lean_closure_set(v___f_924_, 4, v___x_918_);
lean_closure_set(v___f_924_, 5, v_toBind_916_);
lean_closure_set(v___f_924_, 6, v___x_923_);
lean_closure_set(v___f_924_, 7, v_inst_780_);
lean_closure_set(v___f_924_, 8, v_e_922_);
v___x_925_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_780_, v_inst_781_, v_inst_782_, v_t_920_);
v___x_926_ = lean_apply_4(v_toBind_916_, lean_box(0), lean_box(0), v___x_925_, v___f_924_);
return v___x_926_;
}
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = l_Lean_Syntax_getArg(v_x_783_, v___x_927_);
v___x_929_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12));
lean_inc(v___x_928_);
v___x_930_ = l_Lean_Syntax_isOfKind(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v_toApplicative_931_; lean_object* v_toBind_932_; lean_object* v_getRef_933_; lean_object* v_toPure_934_; lean_object* v___f_935_; lean_object* v___f_936_; lean_object* v___f_937_; lean_object* v___x_938_; lean_object* v___f_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
lean_dec(v___x_928_);
v_toApplicative_931_ = lean_ctor_get(v_inst_780_, 0);
lean_inc_ref(v_toApplicative_931_);
v_toBind_932_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_932_, 4);
lean_dec_ref(v_inst_780_);
v_getRef_933_ = lean_ctor_get(v_inst_781_, 0);
lean_inc(v_getRef_933_);
lean_dec_ref(v_inst_781_);
v_toPure_934_ = lean_ctor_get(v_toApplicative_931_, 1);
lean_inc_n(v_toPure_934_, 2);
lean_dec_ref(v_toApplicative_931_);
v___f_935_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_935_, 0, v_toPure_934_);
lean_closure_set(v___f_935_, 1, v_x_783_);
lean_inc_ref(v_inst_782_);
v___f_936_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_936_, 0, v_inst_782_);
lean_closure_set(v___f_936_, 1, v_toBind_932_);
lean_closure_set(v___f_936_, 2, v___f_935_);
v___f_937_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_937_, 0, v_inst_782_);
lean_closure_set(v___f_937_, 1, v_toBind_932_);
lean_closure_set(v___f_937_, 2, v___f_936_);
v___x_938_ = lean_box(v___x_930_);
v___f_939_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_939_, 0, v___x_938_);
lean_closure_set(v___f_939_, 1, v_toPure_934_);
v___x_940_ = lean_apply_4(v_toBind_932_, lean_box(0), lean_box(0), v_getRef_933_, v___f_939_);
v___x_941_ = lean_apply_4(v_toBind_932_, lean_box(0), lean_box(0), v___x_940_, v___f_937_);
return v___x_941_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = l_Lean_Syntax_getArg(v___x_928_, v___x_942_);
lean_dec(v___x_928_);
v___x_944_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14));
lean_inc(v___x_943_);
v___x_945_ = l_Lean_Syntax_isOfKind(v___x_943_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v_toApplicative_946_; lean_object* v_toBind_947_; lean_object* v_getRef_948_; lean_object* v_toPure_949_; lean_object* v___f_950_; lean_object* v___f_951_; lean_object* v___f_952_; lean_object* v___x_953_; lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v___x_943_);
v_toApplicative_946_ = lean_ctor_get(v_inst_780_, 0);
lean_inc_ref(v_toApplicative_946_);
v_toBind_947_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_947_, 4);
lean_dec_ref(v_inst_780_);
v_getRef_948_ = lean_ctor_get(v_inst_781_, 0);
lean_inc(v_getRef_948_);
lean_dec_ref(v_inst_781_);
v_toPure_949_ = lean_ctor_get(v_toApplicative_946_, 1);
lean_inc_n(v_toPure_949_, 2);
lean_dec_ref(v_toApplicative_946_);
v___f_950_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_950_, 0, v_toPure_949_);
lean_closure_set(v___f_950_, 1, v_x_783_);
lean_inc_ref(v_inst_782_);
v___f_951_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_951_, 0, v_inst_782_);
lean_closure_set(v___f_951_, 1, v_toBind_947_);
lean_closure_set(v___f_951_, 2, v___f_950_);
v___f_952_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_952_, 0, v_inst_782_);
lean_closure_set(v___f_952_, 1, v_toBind_947_);
lean_closure_set(v___f_952_, 2, v___f_951_);
v___x_953_ = lean_box(v___x_945_);
v___f_954_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_954_, 0, v___x_953_);
lean_closure_set(v___f_954_, 1, v_toPure_949_);
v___x_955_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v_getRef_948_, v___f_954_);
v___x_956_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v___x_955_, v___f_952_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_957_ = l_Lean_Syntax_getArg(v___x_943_, v___x_927_);
lean_dec(v___x_943_);
v___x_958_ = lean_box(0);
v___x_959_ = l_Lean_Syntax_matchesIdent(v___x_957_, v___x_958_);
lean_dec(v___x_957_);
if (v___x_959_ == 0)
{
lean_object* v_toApplicative_960_; lean_object* v_toBind_961_; lean_object* v_getRef_962_; lean_object* v_toPure_963_; lean_object* v___f_964_; lean_object* v___f_965_; lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v___f_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_toApplicative_960_ = lean_ctor_get(v_inst_780_, 0);
lean_inc_ref(v_toApplicative_960_);
v_toBind_961_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_961_, 4);
lean_dec_ref(v_inst_780_);
v_getRef_962_ = lean_ctor_get(v_inst_781_, 0);
lean_inc(v_getRef_962_);
lean_dec_ref(v_inst_781_);
v_toPure_963_ = lean_ctor_get(v_toApplicative_960_, 1);
lean_inc_n(v_toPure_963_, 2);
lean_dec_ref(v_toApplicative_960_);
v___f_964_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_964_, 0, v_toPure_963_);
lean_closure_set(v___f_964_, 1, v_x_783_);
lean_inc_ref(v_inst_782_);
v___f_965_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_965_, 0, v_inst_782_);
lean_closure_set(v___f_965_, 1, v_toBind_961_);
lean_closure_set(v___f_965_, 2, v___f_964_);
v___f_966_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_966_, 0, v_inst_782_);
lean_closure_set(v___f_966_, 1, v_toBind_961_);
lean_closure_set(v___f_966_, 2, v___f_965_);
v___x_967_ = lean_box(v___x_959_);
v___f_968_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_968_, 0, v___x_967_);
lean_closure_set(v___f_968_, 1, v_toPure_963_);
v___x_969_ = lean_apply_4(v_toBind_961_, lean_box(0), lean_box(0), v_getRef_962_, v___f_968_);
v___x_970_ = lean_apply_4(v_toBind_961_, lean_box(0), lean_box(0), v___x_969_, v___f_966_);
return v___x_970_;
}
else
{
lean_object* v_toApplicative_971_; lean_object* v_toBind_972_; lean_object* v_P_973_; lean_object* v___x_974_; lean_object* v___f_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_toApplicative_971_ = lean_ctor_get(v_inst_780_, 0);
v_toBind_972_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_972_, 2);
v_P_973_ = l_Lean_Syntax_getArg(v_x_783_, v___x_942_);
lean_dec(v_x_783_);
v___x_974_ = lean_box(v___x_787_);
lean_inc_ref(v_inst_782_);
lean_inc_ref(v_toApplicative_971_);
lean_inc_ref(v_inst_781_);
v___f_975_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed), 14, 13);
lean_closure_set(v___f_975_, 0, v_inst_781_);
lean_closure_set(v___f_975_, 1, v_toApplicative_971_);
lean_closure_set(v___f_975_, 2, v_inst_782_);
lean_closure_set(v___f_975_, 3, v___x_958_);
lean_closure_set(v___f_975_, 4, v___x_784_);
lean_closure_set(v___f_975_, 5, v___x_785_);
lean_closure_set(v___f_975_, 6, v___x_788_);
lean_closure_set(v___f_975_, 7, v___x_789_);
lean_closure_set(v___f_975_, 8, v___x_944_);
lean_closure_set(v___f_975_, 9, v___x_929_);
lean_closure_set(v___f_975_, 10, v___x_790_);
lean_closure_set(v___f_975_, 11, v_toBind_972_);
lean_closure_set(v___f_975_, 12, v___x_974_);
v___x_976_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_780_, v_inst_781_, v_inst_782_, v_P_973_);
v___x_977_ = lean_apply_4(v_toBind_972_, lean_box(0), lean_box(0), v___x_976_, v___f_975_);
return v___x_977_;
}
}
}
}
}
else
{
lean_object* v_toApplicative_978_; lean_object* v_toBind_979_; lean_object* v_getRef_980_; lean_object* v_toPure_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___f_984_; lean_object* v___f_985_; lean_object* v___f_986_; lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_toApplicative_978_ = lean_ctor_get(v_inst_780_, 0);
lean_inc_ref(v_toApplicative_978_);
v_toBind_979_ = lean_ctor_get(v_inst_780_, 1);
lean_inc_n(v_toBind_979_, 4);
lean_dec_ref(v_inst_780_);
v_getRef_980_ = lean_ctor_get(v_inst_781_, 0);
lean_inc(v_getRef_980_);
lean_dec_ref(v_inst_781_);
v_toPure_981_ = lean_ctor_get(v_toApplicative_978_, 1);
lean_inc_n(v_toPure_981_, 2);
lean_dec_ref(v_toApplicative_978_);
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = l_Lean_Syntax_getArg(v_x_783_, v___x_982_);
lean_dec(v_x_783_);
v___f_984_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__17___boxed), 3, 2);
lean_closure_set(v___f_984_, 0, v_toPure_981_);
lean_closure_set(v___f_984_, 1, v___x_983_);
lean_inc_ref(v_inst_782_);
v___f_985_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_985_, 0, v_inst_782_);
lean_closure_set(v___f_985_, 1, v_toBind_979_);
lean_closure_set(v___f_985_, 2, v___f_984_);
v___f_986_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_986_, 0, v_inst_782_);
lean_closure_set(v___f_986_, 1, v_toBind_979_);
lean_closure_set(v___f_986_, 2, v___f_985_);
v___f_987_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__22___boxed), 2, 1);
lean_closure_set(v___f_987_, 0, v_toPure_981_);
v___x_988_ = lean_apply_4(v_toBind_979_, lean_box(0), lean_box(0), v_getRef_980_, v___f_987_);
v___x_989_ = lean_apply_4(v_toBind_979_, lean_box(0), lean_box(0), v___x_988_, v___f_986_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11(lean_object* v_inst_990_, lean_object* v_toApplicative_991_, lean_object* v_inst_992_, lean_object* v___x_993_, lean_object* v___x_994_, lean_object* v_toBind_995_, uint8_t v___x_996_, lean_object* v_inst_997_, lean_object* v_e_998_, lean_object* v_t_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1000_ = lean_box(v___x_996_);
lean_inc(v_toBind_995_);
lean_inc_ref(v_inst_992_);
lean_inc_ref(v_inst_990_);
v___f_1001_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_1001_, 0, v_inst_990_);
lean_closure_set(v___f_1001_, 1, v_toApplicative_991_);
lean_closure_set(v___f_1001_, 2, v_inst_992_);
lean_closure_set(v___f_1001_, 3, v___x_993_);
lean_closure_set(v___f_1001_, 4, v___x_994_);
lean_closure_set(v___f_1001_, 5, v_t_999_);
lean_closure_set(v___f_1001_, 6, v_toBind_995_);
lean_closure_set(v___f_1001_, 7, v___x_1000_);
v___x_1002_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_997_, v_inst_990_, v_inst_992_, v_e_998_);
v___x_1003_ = lean_apply_4(v_toBind_995_, lean_box(0), lean_box(0), v___x_1002_, v___f_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack(lean_object* v_m_1004_, lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_1005_, v_inst_1006_, v_inst_1007_, v_x_1008_);
return v___x_1009_;
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
