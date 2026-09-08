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
uint8_t v___x_1564__boxed_367_; lean_object* v_res_368_; 
v___x_1564__boxed_367_ = lean_unbox(v___x_364_);
v_res_368_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__3(v___x_1564__boxed_367_, v_toPure_365_, v_____do__lift_366_);
lean_dec(v_____do__lift_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__21(lean_object* v_info_371_, lean_object* v___x_372_, lean_object* v_scp_373_, lean_object* v___x_374_, lean_object* v___x_375_, lean_object* v___x_376_, lean_object* v___x_377_, lean_object* v___x_378_, lean_object* v___x_379_, lean_object* v___x_380_, lean_object* v___x_381_, lean_object* v_____do__lift_382_, lean_object* v_toPure_383_, lean_object* v_quotCtx_384_){
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
v___x_389_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__0));
v___x_390_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__1));
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
v___f_435_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__21), 14, 13);
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__6(lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v___x_457_, lean_object* v___x_458_, lean_object* v___x_459_, lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v___x_463_, lean_object* v___x_464_, lean_object* v___x_465_, lean_object* v_toPure_466_, lean_object* v_toBind_467_, lean_object* v___f_468_, lean_object* v_____do__lift_469_){
_start:
{
lean_object* v_getRef_470_; lean_object* v___f_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_getRef_470_ = lean_ctor_get(v_inst_455_, 0);
lean_inc(v_getRef_470_);
lean_dec_ref(v_inst_455_);
lean_inc_n(v_toBind_467_, 2);
v___f_471_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__5), 14, 13);
lean_closure_set(v___f_471_, 0, v_inst_456_);
lean_closure_set(v___f_471_, 1, v___x_457_);
lean_closure_set(v___f_471_, 2, v___x_458_);
lean_closure_set(v___f_471_, 3, v___x_459_);
lean_closure_set(v___f_471_, 4, v___x_460_);
lean_closure_set(v___f_471_, 5, v___x_461_);
lean_closure_set(v___f_471_, 6, v___x_462_);
lean_closure_set(v___f_471_, 7, v___x_463_);
lean_closure_set(v___f_471_, 8, v___x_464_);
lean_closure_set(v___f_471_, 9, v___x_465_);
lean_closure_set(v___f_471_, 10, v_____do__lift_469_);
lean_closure_set(v___f_471_, 11, v_toPure_466_);
lean_closure_set(v___f_471_, 12, v_toBind_467_);
v___x_472_ = lean_apply_4(v_toBind_467_, lean_box(0), lean_box(0), v_getRef_470_, v___f_468_);
v___x_473_ = lean_apply_4(v_toBind_467_, lean_box(0), lean_box(0), v___x_472_, v___f_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__16(lean_object* v_info_474_, lean_object* v___x_475_, lean_object* v_xs_476_, lean_object* v___x_477_, lean_object* v_b_478_, lean_object* v___x_479_, lean_object* v_toPure_480_, lean_object* v_quotCtx_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_inc_n(v_info_474_, 5);
v___x_482_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_482_, 0, v_info_474_);
lean_ctor_set(v___x_482_, 1, v___x_475_);
v___x_483_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37));
v___x_484_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43);
v___x_485_ = l_Array_append___redArg(v___x_484_, v_xs_476_);
v___x_486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_486_, 0, v_info_474_);
lean_ctor_set(v___x_486_, 1, v___x_483_);
lean_ctor_set(v___x_486_, 2, v___x_485_);
v___x_487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_487_, 0, v_info_474_);
lean_ctor_set(v___x_487_, 1, v___x_483_);
lean_ctor_set(v___x_487_, 2, v___x_484_);
v___x_488_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44));
v___x_489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_489_, 0, v_info_474_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_Syntax_node4(v_info_474_, v___x_477_, v___x_486_, v___x_487_, v___x_489_, v_b_478_);
v___x_491_ = l_Lean_Syntax_node2(v_info_474_, v___x_479_, v___x_482_, v___x_490_);
v___x_492_ = lean_apply_2(v_toPure_480_, lean_box(0), v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__16___boxed(lean_object* v_info_493_, lean_object* v___x_494_, lean_object* v_xs_495_, lean_object* v___x_496_, lean_object* v_b_497_, lean_object* v___x_498_, lean_object* v_toPure_499_, lean_object* v_quotCtx_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__16(v_info_493_, v___x_494_, v_xs_495_, v___x_496_, v_b_497_, v___x_498_, v_toPure_499_, v_quotCtx_500_);
lean_dec(v_quotCtx_500_);
lean_dec_ref(v_xs_495_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7(lean_object* v_toBind_502_, lean_object* v_getContext_503_, lean_object* v___f_504_, lean_object* v_scp_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = lean_apply_4(v_toBind_502_, lean_box(0), lean_box(0), v_getContext_503_, v___f_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed(lean_object* v_toBind_507_, lean_object* v_getContext_508_, lean_object* v___f_509_, lean_object* v_scp_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__7(v_toBind_507_, v_getContext_508_, v___f_509_, v_scp_510_);
lean_dec(v_scp_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__8(lean_object* v_inst_512_, lean_object* v___x_513_, lean_object* v_xs_514_, lean_object* v___x_515_, lean_object* v_b_516_, lean_object* v___x_517_, lean_object* v_toPure_518_, lean_object* v_toBind_519_, lean_object* v_info_520_){
_start:
{
lean_object* v_getCurrMacroScope_521_; lean_object* v_getContext_522_; lean_object* v___f_523_; lean_object* v___f_524_; lean_object* v___x_525_; 
v_getCurrMacroScope_521_ = lean_ctor_get(v_inst_512_, 1);
lean_inc(v_getCurrMacroScope_521_);
v_getContext_522_ = lean_ctor_get(v_inst_512_, 2);
lean_inc(v_getContext_522_);
lean_dec_ref(v_inst_512_);
v___f_523_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__16___boxed), 8, 7);
lean_closure_set(v___f_523_, 0, v_info_520_);
lean_closure_set(v___f_523_, 1, v___x_513_);
lean_closure_set(v___f_523_, 2, v_xs_514_);
lean_closure_set(v___f_523_, 3, v___x_515_);
lean_closure_set(v___f_523_, 4, v_b_516_);
lean_closure_set(v___f_523_, 5, v___x_517_);
lean_closure_set(v___f_523_, 6, v_toPure_518_);
lean_inc(v_toBind_519_);
v___f_524_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_524_, 0, v_toBind_519_);
lean_closure_set(v___f_524_, 1, v_getContext_522_);
lean_closure_set(v___f_524_, 2, v___f_523_);
v___x_525_ = lean_apply_4(v_toBind_519_, lean_box(0), lean_box(0), v_getCurrMacroScope_521_, v___f_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__9(lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v___x_528_, lean_object* v_xs_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v_toPure_532_, lean_object* v_toBind_533_, lean_object* v___f_534_, lean_object* v_b_535_){
_start:
{
lean_object* v_getRef_536_; lean_object* v___f_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_getRef_536_ = lean_ctor_get(v_inst_526_, 0);
lean_inc(v_getRef_536_);
lean_dec_ref(v_inst_526_);
lean_inc_n(v_toBind_533_, 2);
v___f_537_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__8), 9, 8);
lean_closure_set(v___f_537_, 0, v_inst_527_);
lean_closure_set(v___f_537_, 1, v___x_528_);
lean_closure_set(v___f_537_, 2, v_xs_529_);
lean_closure_set(v___f_537_, 3, v___x_530_);
lean_closure_set(v___f_537_, 4, v_b_535_);
lean_closure_set(v___f_537_, 5, v___x_531_);
lean_closure_set(v___f_537_, 6, v_toPure_532_);
lean_closure_set(v___f_537_, 7, v_toBind_533_);
v___x_538_ = lean_apply_4(v_toBind_533_, lean_box(0), lean_box(0), v_getRef_536_, v___f_534_);
v___x_539_ = lean_apply_4(v_toBind_533_, lean_box(0), lean_box(0), v___x_538_, v___f_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11(lean_object* v_info_540_, lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v_t_543_, lean_object* v_e_544_, lean_object* v_toPure_545_, lean_object* v_quotCtx_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_547_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38));
lean_inc_n(v_info_540_, 3);
v___x_548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_548_, 0, v_info_540_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39));
v___x_550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_550_, 0, v_info_540_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40));
v___x_552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_552_, 0, v_info_540_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = l_Lean_Syntax_node6(v_info_540_, v___x_541_, v___x_548_, v___x_542_, v___x_550_, v_t_543_, v___x_552_, v_e_544_);
v___x_554_ = lean_apply_2(v_toPure_545_, lean_box(0), v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed(lean_object* v_info_555_, lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v_t_558_, lean_object* v_e_559_, lean_object* v_toPure_560_, lean_object* v_quotCtx_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__11(v_info_555_, v___x_556_, v___x_557_, v_t_558_, v_e_559_, v_toPure_560_, v_quotCtx_561_);
lean_dec(v_quotCtx_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__12(lean_object* v_inst_563_, lean_object* v___x_564_, lean_object* v___x_565_, lean_object* v_t_566_, lean_object* v_e_567_, lean_object* v_toPure_568_, lean_object* v_toBind_569_, lean_object* v_info_570_){
_start:
{
lean_object* v_getCurrMacroScope_571_; lean_object* v_getContext_572_; lean_object* v___f_573_; lean_object* v___f_574_; lean_object* v___x_575_; 
v_getCurrMacroScope_571_ = lean_ctor_get(v_inst_563_, 1);
lean_inc(v_getCurrMacroScope_571_);
v_getContext_572_ = lean_ctor_get(v_inst_563_, 2);
lean_inc(v_getContext_572_);
lean_dec_ref(v_inst_563_);
v___f_573_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed), 7, 6);
lean_closure_set(v___f_573_, 0, v_info_570_);
lean_closure_set(v___f_573_, 1, v___x_564_);
lean_closure_set(v___f_573_, 2, v___x_565_);
lean_closure_set(v___f_573_, 3, v_t_566_);
lean_closure_set(v___f_573_, 4, v_e_567_);
lean_closure_set(v___f_573_, 5, v_toPure_568_);
lean_inc(v_toBind_569_);
v___f_574_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_574_, 0, v_toBind_569_);
lean_closure_set(v___f_574_, 1, v_getContext_572_);
lean_closure_set(v___f_574_, 2, v___f_573_);
v___x_575_ = lean_apply_4(v_toBind_569_, lean_box(0), lean_box(0), v_getCurrMacroScope_571_, v___f_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__10(lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v___x_578_, lean_object* v___x_579_, lean_object* v_t_580_, lean_object* v_toPure_581_, lean_object* v_toBind_582_, lean_object* v___f_583_, lean_object* v_e_584_){
_start:
{
lean_object* v_getRef_585_; lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_getRef_585_ = lean_ctor_get(v_inst_576_, 0);
lean_inc(v_getRef_585_);
lean_dec_ref(v_inst_576_);
lean_inc_n(v_toBind_582_, 2);
v___f_586_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__12), 8, 7);
lean_closure_set(v___f_586_, 0, v_inst_577_);
lean_closure_set(v___f_586_, 1, v___x_578_);
lean_closure_set(v___f_586_, 2, v___x_579_);
lean_closure_set(v___f_586_, 3, v_t_580_);
lean_closure_set(v___f_586_, 4, v_e_584_);
lean_closure_set(v___f_586_, 5, v_toPure_581_);
lean_closure_set(v___f_586_, 6, v_toBind_582_);
v___x_587_ = lean_apply_4(v_toBind_582_, lean_box(0), lean_box(0), v_getRef_585_, v___f_583_);
v___x_588_ = lean_apply_4(v_toBind_582_, lean_box(0), lean_box(0), v___x_587_, v___f_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__19(lean_object* v_toPure_589_, lean_object* v___x_590_, lean_object* v_quotCtx_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = lean_apply_2(v_toPure_589_, lean_box(0), v___x_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__19___boxed(lean_object* v_toPure_593_, lean_object* v___x_594_, lean_object* v_quotCtx_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__19(v_toPure_593_, v___x_594_, v_quotCtx_595_);
lean_dec(v_quotCtx_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18(lean_object* v_toPure_597_, lean_object* v_____do__lift_598_){
_start:
{
uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = 0;
v___x_600_ = l_Lean_SourceInfo_fromRef(v_____do__lift_598_, v___x_599_);
v___x_601_ = lean_apply_2(v_toPure_597_, lean_box(0), v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed(lean_object* v_toPure_602_, lean_object* v_____do__lift_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__18(v_toPure_602_, v_____do__lift_603_);
lean_dec(v_____do__lift_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__29(lean_object* v_info_605_, lean_object* v___x_606_, lean_object* v_scp_607_, lean_object* v___x_608_, lean_object* v___x_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v___x_613_, lean_object* v___x_614_, lean_object* v_____do__lift_615_, lean_object* v_toPure_616_, lean_object* v_quotCtx_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_618_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15));
lean_inc_n(v_info_605_, 5);
v___x_619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_619_, 0, v_info_605_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17, &l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
v___x_621_ = l_Lean_addMacroScope(v_quotCtx_617_, v___x_606_, v_scp_607_);
v___x_622_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__0));
v___x_623_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__21___closed__1));
v___x_624_ = l_Lean_Name_mkStr4(v___x_608_, v___x_609_, v___x_622_, v___x_623_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v___x_626_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20));
lean_inc_ref_n(v___x_610_, 3);
v___x_627_ = l_Lean_Name_mkStr2(v___x_610_, v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
v___x_629_ = l_Lean_Name_mkStr2(v___x_610_, v___x_611_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
v___x_631_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25));
v___x_632_ = l_Lean_Name_mkStr2(v___x_610_, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = l_Lean_Name_mkStr1(v___x_610_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_633_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_630_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_628_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_625_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_642_, 0, v_info_605_);
lean_ctor_set(v___x_642_, 1, v___x_620_);
lean_ctor_set(v___x_642_, 2, v___x_621_);
lean_ctor_set(v___x_642_, 3, v___x_641_);
v___x_643_ = l_Lean_Syntax_node1(v_info_605_, v___x_612_, v___x_642_);
v___x_644_ = l_Lean_Syntax_node2(v_info_605_, v___x_613_, v___x_619_, v___x_643_);
v___x_645_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__12));
v___x_646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_646_, 0, v_info_605_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = l_Lean_Syntax_node3(v_info_605_, v___x_614_, v___x_644_, v_____do__lift_615_, v___x_646_);
v___x_648_ = lean_apply_2(v_toPure_616_, lean_box(0), v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__14(lean_object* v_info_649_, lean_object* v___x_650_, lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v___x_654_, lean_object* v___x_655_, lean_object* v___x_656_, lean_object* v___x_657_, lean_object* v_____do__lift_658_, lean_object* v_toPure_659_, lean_object* v_toBind_660_, lean_object* v_getContext_661_, lean_object* v_scp_662_){
_start:
{
lean_object* v___f_663_; lean_object* v___x_664_; 
v___f_663_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__29), 13, 12);
lean_closure_set(v___f_663_, 0, v_info_649_);
lean_closure_set(v___f_663_, 1, v___x_650_);
lean_closure_set(v___f_663_, 2, v_scp_662_);
lean_closure_set(v___f_663_, 3, v___x_651_);
lean_closure_set(v___f_663_, 4, v___x_652_);
lean_closure_set(v___f_663_, 5, v___x_653_);
lean_closure_set(v___f_663_, 6, v___x_654_);
lean_closure_set(v___f_663_, 7, v___x_655_);
lean_closure_set(v___f_663_, 8, v___x_656_);
lean_closure_set(v___f_663_, 9, v___x_657_);
lean_closure_set(v___f_663_, 10, v_____do__lift_658_);
lean_closure_set(v___f_663_, 11, v_toPure_659_);
v___x_664_ = lean_apply_4(v_toBind_660_, lean_box(0), lean_box(0), v_getContext_661_, v___f_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__15(lean_object* v_inst_665_, lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v___x_672_, lean_object* v___x_673_, lean_object* v_____do__lift_674_, lean_object* v_toPure_675_, lean_object* v_toBind_676_, lean_object* v_info_677_){
_start:
{
lean_object* v_getCurrMacroScope_678_; lean_object* v_getContext_679_; lean_object* v___f_680_; lean_object* v___x_681_; 
v_getCurrMacroScope_678_ = lean_ctor_get(v_inst_665_, 1);
lean_inc(v_getCurrMacroScope_678_);
v_getContext_679_ = lean_ctor_get(v_inst_665_, 2);
lean_inc(v_getContext_679_);
lean_dec_ref(v_inst_665_);
lean_inc(v_toBind_676_);
v___f_680_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__14), 14, 13);
lean_closure_set(v___f_680_, 0, v_info_677_);
lean_closure_set(v___f_680_, 1, v___x_666_);
lean_closure_set(v___f_680_, 2, v___x_667_);
lean_closure_set(v___f_680_, 3, v___x_668_);
lean_closure_set(v___f_680_, 4, v___x_669_);
lean_closure_set(v___f_680_, 5, v___x_670_);
lean_closure_set(v___f_680_, 6, v___x_671_);
lean_closure_set(v___f_680_, 7, v___x_672_);
lean_closure_set(v___f_680_, 8, v___x_673_);
lean_closure_set(v___f_680_, 9, v_____do__lift_674_);
lean_closure_set(v___f_680_, 10, v_toPure_675_);
lean_closure_set(v___f_680_, 11, v_toBind_676_);
lean_closure_set(v___f_680_, 12, v_getContext_679_);
v___x_681_ = lean_apply_4(v_toBind_676_, lean_box(0), lean_box(0), v_getCurrMacroScope_678_, v___f_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__17(lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v___x_684_, lean_object* v___x_685_, lean_object* v___x_686_, lean_object* v___x_687_, lean_object* v___x_688_, lean_object* v___x_689_, lean_object* v___x_690_, lean_object* v___x_691_, lean_object* v_toPure_692_, lean_object* v_toBind_693_, lean_object* v___f_694_, lean_object* v_____do__lift_695_){
_start:
{
lean_object* v_getRef_696_; lean_object* v___f_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_getRef_696_ = lean_ctor_get(v_inst_682_, 0);
lean_inc(v_getRef_696_);
lean_dec_ref(v_inst_682_);
lean_inc_n(v_toBind_693_, 2);
v___f_697_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__15), 13, 12);
lean_closure_set(v___f_697_, 0, v_inst_683_);
lean_closure_set(v___f_697_, 1, v___x_684_);
lean_closure_set(v___f_697_, 2, v___x_685_);
lean_closure_set(v___f_697_, 3, v___x_686_);
lean_closure_set(v___f_697_, 4, v___x_687_);
lean_closure_set(v___f_697_, 5, v___x_688_);
lean_closure_set(v___f_697_, 6, v___x_689_);
lean_closure_set(v___f_697_, 7, v___x_690_);
lean_closure_set(v___f_697_, 8, v___x_691_);
lean_closure_set(v___f_697_, 9, v_____do__lift_695_);
lean_closure_set(v___f_697_, 10, v_toPure_692_);
lean_closure_set(v___f_697_, 11, v_toBind_693_);
v___x_698_ = lean_apply_4(v_toBind_693_, lean_box(0), lean_box(0), v_getRef_696_, v___f_694_);
v___x_699_ = lean_apply_4(v_toBind_693_, lean_box(0), lean_box(0), v___x_698_, v___f_697_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg(lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_x_703_){
_start:
{
lean_object* v_toApplicative_704_; lean_object* v_toBind_705_; lean_object* v_toPure_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_toApplicative_704_ = lean_ctor_get(v_inst_700_, 0);
v_toBind_705_ = lean_ctor_get(v_inst_700_, 1);
lean_inc(v_toBind_705_);
v_toPure_706_ = lean_ctor_get(v_toApplicative_704_, 1);
v___x_707_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__0));
v___x_708_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__1));
v___x_709_ = ((lean_object*)(l_Std_Do_termSpred_x28___x29___closed__3));
lean_inc(v_x_703_);
v___x_710_ = l_Lean_Syntax_isOfKind(v_x_703_, v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_711_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0));
v___x_712_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1));
v___x_713_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4));
lean_inc(v_x_703_);
v___x_714_ = l_Lean_Syntax_isOfKind(v_x_703_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8));
lean_inc(v_x_703_);
v___x_716_ = l_Lean_Syntax_isOfKind(v_x_703_, v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_717_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5));
v___x_718_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6));
lean_inc(v_x_703_);
v___x_719_ = l_Lean_Syntax_isOfKind(v_x_703_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10));
lean_inc(v_x_703_);
v___x_721_ = l_Lean_Syntax_isOfKind(v_x_703_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v_getRef_722_; lean_object* v___f_723_; lean_object* v___f_724_; lean_object* v___f_725_; lean_object* v___x_726_; lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_inc_n(v_toPure_706_, 2);
lean_dec_ref(v_inst_700_);
v_getRef_722_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_getRef_722_);
lean_dec_ref(v_inst_701_);
v___f_723_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_723_, 0, v_toPure_706_);
lean_closure_set(v___f_723_, 1, v_x_703_);
lean_inc_n(v_toBind_705_, 3);
lean_inc_ref(v_inst_702_);
v___f_724_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_724_, 0, v_inst_702_);
lean_closure_set(v___f_724_, 1, v_toBind_705_);
lean_closure_set(v___f_724_, 2, v___f_723_);
v___f_725_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_725_, 0, v_inst_702_);
lean_closure_set(v___f_725_, 1, v_toBind_705_);
lean_closure_set(v___f_725_, 2, v___f_724_);
v___x_726_ = lean_box(v___x_721_);
v___f_727_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_727_, 0, v___x_726_);
lean_closure_set(v___f_727_, 1, v_toPure_706_);
v___x_728_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getRef_722_, v___f_727_);
v___x_729_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_728_, v___f_725_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_730_ = lean_unsigned_to_nat(0u);
v___x_731_ = l_Lean_Syntax_getArg(v_x_703_, v___x_730_);
v___x_732_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12));
lean_inc(v___x_731_);
v___x_733_ = l_Lean_Syntax_isOfKind(v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v_getRef_734_; lean_object* v___f_735_; lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_inc_n(v_toPure_706_, 2);
lean_dec(v___x_731_);
lean_dec_ref(v_inst_700_);
v_getRef_734_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_getRef_734_);
lean_dec_ref(v_inst_701_);
v___f_735_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_735_, 0, v_toPure_706_);
lean_closure_set(v___f_735_, 1, v_x_703_);
lean_inc_n(v_toBind_705_, 3);
lean_inc_ref(v_inst_702_);
v___f_736_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_736_, 0, v_inst_702_);
lean_closure_set(v___f_736_, 1, v_toBind_705_);
lean_closure_set(v___f_736_, 2, v___f_735_);
v___f_737_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_737_, 0, v_inst_702_);
lean_closure_set(v___f_737_, 1, v_toBind_705_);
lean_closure_set(v___f_737_, 2, v___f_736_);
v___x_738_ = lean_box(v___x_733_);
v___f_739_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_739_, 0, v___x_738_);
lean_closure_set(v___f_739_, 1, v_toPure_706_);
v___x_740_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getRef_734_, v___f_739_);
v___x_741_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_740_, v___f_737_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = l_Lean_Syntax_getArg(v___x_731_, v___x_742_);
lean_dec(v___x_731_);
v___x_744_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14));
lean_inc(v___x_743_);
v___x_745_ = l_Lean_Syntax_isOfKind(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v_getRef_746_; lean_object* v___f_747_; lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_inc_n(v_toPure_706_, 2);
lean_dec(v___x_743_);
lean_dec_ref(v_inst_700_);
v_getRef_746_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_getRef_746_);
lean_dec_ref(v_inst_701_);
v___f_747_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_747_, 0, v_toPure_706_);
lean_closure_set(v___f_747_, 1, v_x_703_);
lean_inc_n(v_toBind_705_, 3);
lean_inc_ref(v_inst_702_);
v___f_748_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_748_, 0, v_inst_702_);
lean_closure_set(v___f_748_, 1, v_toBind_705_);
lean_closure_set(v___f_748_, 2, v___f_747_);
v___f_749_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_749_, 0, v_inst_702_);
lean_closure_set(v___f_749_, 1, v_toBind_705_);
lean_closure_set(v___f_749_, 2, v___f_748_);
v___x_750_ = lean_box(v___x_745_);
v___f_751_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_751_, 0, v___x_750_);
lean_closure_set(v___f_751_, 1, v_toPure_706_);
v___x_752_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getRef_746_, v___f_751_);
v___x_753_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_752_, v___f_749_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = l_Lean_Syntax_getArg(v___x_743_, v___x_730_);
lean_dec(v___x_743_);
v___x_755_ = lean_box(0);
v___x_756_ = l_Lean_Syntax_matchesIdent(v___x_754_, v___x_755_);
lean_dec(v___x_754_);
if (v___x_756_ == 0)
{
lean_object* v_getRef_757_; lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_inc_n(v_toPure_706_, 2);
lean_dec_ref(v_inst_700_);
v_getRef_757_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_getRef_757_);
lean_dec_ref(v_inst_701_);
v___f_758_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_758_, 0, v_toPure_706_);
lean_closure_set(v___f_758_, 1, v_x_703_);
lean_inc_n(v_toBind_705_, 3);
lean_inc_ref(v_inst_702_);
v___f_759_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_759_, 0, v_inst_702_);
lean_closure_set(v___f_759_, 1, v_toBind_705_);
lean_closure_set(v___f_759_, 2, v___f_758_);
v___f_760_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_760_, 0, v_inst_702_);
lean_closure_set(v___f_760_, 1, v_toBind_705_);
lean_closure_set(v___f_760_, 2, v___f_759_);
v___x_761_ = lean_box(v___x_756_);
v___f_762_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_762_, 0, v___x_761_);
lean_closure_set(v___f_762_, 1, v_toPure_706_);
v___x_763_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getRef_757_, v___f_762_);
v___x_764_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_763_, v___f_760_);
return v___x_764_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(3u);
v___x_766_ = l_Lean_Syntax_getArg(v_x_703_, v___x_765_);
lean_inc(v___x_766_);
v___x_767_ = l_Lean_Syntax_matchesNull(v___x_766_, v___x_742_);
if (v___x_767_ == 0)
{
lean_object* v_getRef_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_inc_n(v_toPure_706_, 2);
lean_dec(v___x_766_);
lean_dec_ref(v_inst_700_);
v_getRef_768_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_getRef_768_);
lean_dec_ref(v_inst_701_);
v___f_769_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_769_, 0, v_toPure_706_);
lean_closure_set(v___f_769_, 1, v_x_703_);
lean_inc_n(v_toBind_705_, 3);
lean_inc_ref(v_inst_702_);
v___f_770_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_770_, 0, v_inst_702_);
lean_closure_set(v___f_770_, 1, v_toBind_705_);
lean_closure_set(v___f_770_, 2, v___f_769_);
v___f_771_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_771_, 0, v_inst_702_);
lean_closure_set(v___f_771_, 1, v_toBind_705_);
lean_closure_set(v___f_771_, 2, v___f_770_);
v___x_772_ = lean_box(v___x_767_);
v___f_773_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_773_, 0, v___x_772_);
lean_closure_set(v___f_773_, 1, v_toPure_706_);
v___x_774_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getRef_768_, v___f_773_);
v___x_775_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_774_, v___f_771_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; lean_object* v___f_777_; lean_object* v_P_778_; lean_object* v___x_779_; lean_object* v___f_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_776_ = lean_box(v___x_719_);
lean_inc_n(v_toPure_706_, 2);
v___f_777_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_777_, 0, v___x_776_);
lean_closure_set(v___f_777_, 1, v_toPure_706_);
v_P_778_ = l_Lean_Syntax_getArg(v_x_703_, v___x_742_);
lean_dec(v_x_703_);
v___x_779_ = l_Lean_Syntax_getArg(v___x_766_, v___x_730_);
lean_dec(v___x_766_);
lean_inc(v_toBind_705_);
lean_inc_ref(v_inst_702_);
lean_inc_ref(v_inst_701_);
v___f_780_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__6), 15, 14);
lean_closure_set(v___f_780_, 0, v_inst_701_);
lean_closure_set(v___f_780_, 1, v_inst_702_);
lean_closure_set(v___f_780_, 2, v___x_755_);
lean_closure_set(v___f_780_, 3, v___x_707_);
lean_closure_set(v___f_780_, 4, v___x_708_);
lean_closure_set(v___f_780_, 5, v___x_711_);
lean_closure_set(v___f_780_, 6, v___x_712_);
lean_closure_set(v___f_780_, 7, v___x_744_);
lean_closure_set(v___f_780_, 8, v___x_732_);
lean_closure_set(v___f_780_, 9, v___x_779_);
lean_closure_set(v___f_780_, 10, v___x_720_);
lean_closure_set(v___f_780_, 11, v_toPure_706_);
lean_closure_set(v___f_780_, 12, v_toBind_705_);
lean_closure_set(v___f_780_, 13, v___f_777_);
v___x_781_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_700_, v_inst_701_, v_inst_702_, v_P_778_);
v___x_782_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_781_, v___f_780_);
return v___x_782_;
}
}
}
}
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = l_Lean_Syntax_getArg(v_x_703_, v___x_783_);
v___x_785_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42));
lean_inc(v___x_784_);
v___x_786_ = l_Lean_Syntax_isOfKind(v___x_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v_getRef_787_; lean_object* v___f_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___x_791_; lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_inc_n(v_toPure_706_, 2);
lean_dec(v___x_784_);
lean_dec_ref(v_inst_700_);
v_getRef_787_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_getRef_787_);
lean_dec_ref(v_inst_701_);
v___f_788_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_788_, 0, v_toPure_706_);
lean_closure_set(v___f_788_, 1, v_x_703_);
lean_inc_n(v_toBind_705_, 3);
lean_inc_ref(v_inst_702_);
v___f_789_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_789_, 0, v_inst_702_);
lean_closure_set(v___f_789_, 1, v_toBind_705_);
lean_closure_set(v___f_789_, 2, v___f_788_);
v___f_790_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_790_, 0, v_inst_702_);
lean_closure_set(v___f_790_, 1, v_toBind_705_);
lean_closure_set(v___f_790_, 2, v___f_789_);
v___x_791_ = lean_box(v___x_786_);
v___f_792_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_792_, 0, v___x_791_);
lean_closure_set(v___f_792_, 1, v_toPure_706_);
v___x_793_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getRef_787_, v___f_792_);
v___x_794_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_793_, v___f_790_);
return v___x_794_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = l_Lean_Syntax_getArg(v___x_784_, v___x_783_);
v___x_797_ = l_Lean_Syntax_matchesNull(v___x_796_, v___x_795_);
if (v___x_797_ == 0)
{
lean_object* v_getRef_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_inc_n(v_toPure_706_, 2);
lean_dec(v___x_784_);
lean_dec_ref(v_inst_700_);
v_getRef_798_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_getRef_798_);
lean_dec_ref(v_inst_701_);
v___f_799_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_799_, 0, v_toPure_706_);
lean_closure_set(v___f_799_, 1, v_x_703_);
lean_inc_n(v_toBind_705_, 3);
lean_inc_ref(v_inst_702_);
v___f_800_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_800_, 0, v_inst_702_);
lean_closure_set(v___f_800_, 1, v_toBind_705_);
lean_closure_set(v___f_800_, 2, v___f_799_);
v___f_801_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_801_, 0, v_inst_702_);
lean_closure_set(v___f_801_, 1, v_toBind_705_);
lean_closure_set(v___f_801_, 2, v___f_800_);
v___x_802_ = lean_box(v___x_797_);
v___f_803_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_803_, 0, v___x_802_);
lean_closure_set(v___f_803_, 1, v_toPure_706_);
v___x_804_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getRef_798_, v___f_803_);
v___x_805_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_804_, v___f_801_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_b_810_; lean_object* v_xs_811_; lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v_x_703_);
v___x_806_ = lean_box(v___x_716_);
lean_inc_n(v_toPure_706_, 2);
v___f_807_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_807_, 0, v___x_806_);
lean_closure_set(v___f_807_, 1, v_toPure_706_);
v___x_808_ = l_Lean_Syntax_getArg(v___x_784_, v___x_795_);
v___x_809_ = lean_unsigned_to_nat(3u);
v_b_810_ = l_Lean_Syntax_getArg(v___x_784_, v___x_809_);
lean_dec(v___x_784_);
v_xs_811_ = l_Lean_Syntax_getArgs(v___x_808_);
lean_dec(v___x_808_);
lean_inc(v_toBind_705_);
lean_inc_ref(v_inst_702_);
lean_inc_ref(v_inst_701_);
v___f_812_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__9), 10, 9);
lean_closure_set(v___f_812_, 0, v_inst_701_);
lean_closure_set(v___f_812_, 1, v_inst_702_);
lean_closure_set(v___f_812_, 2, v___x_717_);
lean_closure_set(v___f_812_, 3, v_xs_811_);
lean_closure_set(v___f_812_, 4, v___x_785_);
lean_closure_set(v___f_812_, 5, v___x_718_);
lean_closure_set(v___f_812_, 6, v_toPure_706_);
lean_closure_set(v___f_812_, 7, v_toBind_705_);
lean_closure_set(v___f_812_, 8, v___f_807_);
v___x_813_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_700_, v_inst_701_, v_inst_702_, v_b_810_);
v___x_814_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_813_, v___f_812_);
return v___x_814_;
}
}
}
}
else
{
lean_object* v___x_815_; lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_t_820_; lean_object* v___x_821_; lean_object* v_e_822_; lean_object* v___f_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_815_ = lean_box(v___x_714_);
lean_inc_n(v_toPure_706_, 2);
v___f_816_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_816_, 0, v___x_815_);
lean_closure_set(v___f_816_, 1, v_toPure_706_);
v___x_817_ = lean_unsigned_to_nat(1u);
v___x_818_ = l_Lean_Syntax_getArg(v_x_703_, v___x_817_);
v___x_819_ = lean_unsigned_to_nat(3u);
v_t_820_ = l_Lean_Syntax_getArg(v_x_703_, v___x_819_);
v___x_821_ = lean_unsigned_to_nat(5u);
v_e_822_ = l_Lean_Syntax_getArg(v_x_703_, v___x_821_);
lean_dec(v_x_703_);
lean_inc_ref(v_inst_700_);
lean_inc(v_toBind_705_);
lean_inc_ref(v_inst_702_);
lean_inc_ref(v_inst_701_);
v___f_823_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__13), 10, 9);
lean_closure_set(v___f_823_, 0, v_inst_701_);
lean_closure_set(v___f_823_, 1, v_inst_702_);
lean_closure_set(v___f_823_, 2, v___x_715_);
lean_closure_set(v___f_823_, 3, v___x_818_);
lean_closure_set(v___f_823_, 4, v_toPure_706_);
lean_closure_set(v___f_823_, 5, v_toBind_705_);
lean_closure_set(v___f_823_, 6, v___f_816_);
lean_closure_set(v___f_823_, 7, v_inst_700_);
lean_closure_set(v___f_823_, 8, v_e_822_);
v___x_824_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_700_, v_inst_701_, v_inst_702_, v_t_820_);
v___x_825_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_824_, v___f_823_);
return v___x_825_;
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = l_Lean_Syntax_getArg(v_x_703_, v___x_826_);
v___x_828_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12));
lean_inc(v___x_827_);
v___x_829_ = l_Lean_Syntax_isOfKind(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v_getRef_830_; lean_object* v___f_831_; lean_object* v___f_832_; lean_object* v___f_833_; lean_object* v___x_834_; lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_inc_n(v_toPure_706_, 2);
lean_dec(v___x_827_);
lean_dec_ref(v_inst_700_);
v_getRef_830_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_getRef_830_);
lean_dec_ref(v_inst_701_);
v___f_831_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_831_, 0, v_toPure_706_);
lean_closure_set(v___f_831_, 1, v_x_703_);
lean_inc_n(v_toBind_705_, 3);
lean_inc_ref(v_inst_702_);
v___f_832_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_832_, 0, v_inst_702_);
lean_closure_set(v___f_832_, 1, v_toBind_705_);
lean_closure_set(v___f_832_, 2, v___f_831_);
v___f_833_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_833_, 0, v_inst_702_);
lean_closure_set(v___f_833_, 1, v_toBind_705_);
lean_closure_set(v___f_833_, 2, v___f_832_);
v___x_834_ = lean_box(v___x_829_);
v___f_835_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_835_, 0, v___x_834_);
lean_closure_set(v___f_835_, 1, v_toPure_706_);
v___x_836_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getRef_830_, v___f_835_);
v___x_837_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_836_, v___f_833_);
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = l_Lean_Syntax_getArg(v___x_827_, v___x_838_);
lean_dec(v___x_827_);
v___x_840_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14));
lean_inc(v___x_839_);
v___x_841_ = l_Lean_Syntax_isOfKind(v___x_839_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v_getRef_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___f_845_; lean_object* v___x_846_; lean_object* v___f_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_inc_n(v_toPure_706_, 2);
lean_dec(v___x_839_);
lean_dec_ref(v_inst_700_);
v_getRef_842_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_getRef_842_);
lean_dec_ref(v_inst_701_);
v___f_843_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_843_, 0, v_toPure_706_);
lean_closure_set(v___f_843_, 1, v_x_703_);
lean_inc_n(v_toBind_705_, 3);
lean_inc_ref(v_inst_702_);
v___f_844_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_844_, 0, v_inst_702_);
lean_closure_set(v___f_844_, 1, v_toBind_705_);
lean_closure_set(v___f_844_, 2, v___f_843_);
v___f_845_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_845_, 0, v_inst_702_);
lean_closure_set(v___f_845_, 1, v_toBind_705_);
lean_closure_set(v___f_845_, 2, v___f_844_);
v___x_846_ = lean_box(v___x_841_);
v___f_847_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_847_, 0, v___x_846_);
lean_closure_set(v___f_847_, 1, v_toPure_706_);
v___x_848_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getRef_842_, v___f_847_);
v___x_849_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_848_, v___f_845_);
return v___x_849_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_850_ = l_Lean_Syntax_getArg(v___x_839_, v___x_826_);
lean_dec(v___x_839_);
v___x_851_ = lean_box(0);
v___x_852_ = l_Lean_Syntax_matchesIdent(v___x_850_, v___x_851_);
lean_dec(v___x_850_);
if (v___x_852_ == 0)
{
lean_object* v_getRef_853_; lean_object* v___f_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___f_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
lean_inc_n(v_toPure_706_, 2);
lean_dec_ref(v_inst_700_);
v_getRef_853_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_getRef_853_);
lean_dec_ref(v_inst_701_);
v___f_854_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_854_, 0, v_toPure_706_);
lean_closure_set(v___f_854_, 1, v_x_703_);
lean_inc_n(v_toBind_705_, 3);
lean_inc_ref(v_inst_702_);
v___f_855_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_855_, 0, v_inst_702_);
lean_closure_set(v___f_855_, 1, v_toBind_705_);
lean_closure_set(v___f_855_, 2, v___f_854_);
v___f_856_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_856_, 0, v_inst_702_);
lean_closure_set(v___f_856_, 1, v_toBind_705_);
lean_closure_set(v___f_856_, 2, v___f_855_);
v___x_857_ = lean_box(v___x_852_);
v___f_858_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_858_, 0, v___x_857_);
lean_closure_set(v___f_858_, 1, v_toPure_706_);
v___x_859_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getRef_853_, v___f_858_);
v___x_860_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_859_, v___f_856_);
return v___x_860_;
}
else
{
lean_object* v___x_861_; lean_object* v___f_862_; lean_object* v___f_863_; lean_object* v_P_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_861_ = lean_box(v___x_710_);
lean_inc_n(v_toPure_706_, 2);
v___f_862_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_862_, 0, v___x_861_);
lean_closure_set(v___f_862_, 1, v_toPure_706_);
lean_inc(v_toBind_705_);
lean_inc_ref(v_inst_702_);
lean_inc_ref(v_inst_701_);
v___f_863_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__17), 14, 13);
lean_closure_set(v___f_863_, 0, v_inst_701_);
lean_closure_set(v___f_863_, 1, v_inst_702_);
lean_closure_set(v___f_863_, 2, v___x_851_);
lean_closure_set(v___f_863_, 3, v___x_707_);
lean_closure_set(v___f_863_, 4, v___x_708_);
lean_closure_set(v___f_863_, 5, v___x_711_);
lean_closure_set(v___f_863_, 6, v___x_712_);
lean_closure_set(v___f_863_, 7, v___x_840_);
lean_closure_set(v___f_863_, 8, v___x_828_);
lean_closure_set(v___f_863_, 9, v___x_713_);
lean_closure_set(v___f_863_, 10, v_toPure_706_);
lean_closure_set(v___f_863_, 11, v_toBind_705_);
lean_closure_set(v___f_863_, 12, v___f_862_);
v_P_864_ = l_Lean_Syntax_getArg(v_x_703_, v___x_838_);
lean_dec(v_x_703_);
v___x_865_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_700_, v_inst_701_, v_inst_702_, v_P_864_);
v___x_866_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_865_, v___f_863_);
return v___x_866_;
}
}
}
}
}
else
{
lean_object* v_getRef_867_; lean_object* v___f_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___f_871_; lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_inc_n(v_toPure_706_, 2);
lean_dec_ref(v_inst_700_);
v_getRef_867_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_getRef_867_);
lean_dec_ref(v_inst_701_);
v___f_868_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed), 2, 1);
lean_closure_set(v___f_868_, 0, v_toPure_706_);
v___x_869_ = lean_unsigned_to_nat(1u);
v___x_870_ = l_Lean_Syntax_getArg(v_x_703_, v___x_869_);
lean_dec(v_x_703_);
v___f_871_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__19___boxed), 3, 2);
lean_closure_set(v___f_871_, 0, v_toPure_706_);
lean_closure_set(v___f_871_, 1, v___x_870_);
lean_inc_n(v_toBind_705_, 3);
lean_inc_ref(v_inst_702_);
v___f_872_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_872_, 0, v_inst_702_);
lean_closure_set(v___f_872_, 1, v_toBind_705_);
lean_closure_set(v___f_872_, 2, v___f_871_);
v___f_873_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_873_, 0, v_inst_702_);
lean_closure_set(v___f_873_, 1, v_toBind_705_);
lean_closure_set(v___f_873_, 2, v___f_872_);
v___x_874_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v_getRef_867_, v___f_868_);
v___x_875_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_874_, v___f_873_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___redArg___lam__13(lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v___x_878_, lean_object* v___x_879_, lean_object* v_toPure_880_, lean_object* v_toBind_881_, lean_object* v___f_882_, lean_object* v_inst_883_, lean_object* v_e_884_, lean_object* v_t_885_){
_start:
{
lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
lean_inc(v_toBind_881_);
lean_inc_ref(v_inst_877_);
lean_inc_ref(v_inst_876_);
v___f_886_ = lean_alloc_closure((void*)(l_Std_Do_SPred_Notation_unpack___redArg___lam__10), 9, 8);
lean_closure_set(v___f_886_, 0, v_inst_876_);
lean_closure_set(v___f_886_, 1, v_inst_877_);
lean_closure_set(v___f_886_, 2, v___x_878_);
lean_closure_set(v___f_886_, 3, v___x_879_);
lean_closure_set(v___f_886_, 4, v_t_885_);
lean_closure_set(v___f_886_, 5, v_toPure_880_);
lean_closure_set(v___f_886_, 6, v_toBind_881_);
lean_closure_set(v___f_886_, 7, v___f_882_);
v___x_887_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_883_, v_inst_876_, v_inst_877_, v_e_884_);
v___x_888_ = lean_apply_4(v_toBind_881_, lean_box(0), lean_box(0), v___x_887_, v___f_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack(lean_object* v_m_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_x_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Std_Do_SPred_Notation_unpack___redArg(v_inst_890_, v_inst_891_, v_inst_892_, v_x_893_);
return v___x_894_;
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
