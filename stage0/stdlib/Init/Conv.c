// Lean compiler output
// Module: Init.Conv
// Imports: public import Init.Tactics public meta import Init.Meta
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_caseArg;
extern lean_object* l_Lean_Parser_Tactic_simpLemma;
extern lean_object* l_Lean_Parser_Tactic_simpErase;
extern lean_object* l_Lean_Parser_Tactic_simpStar;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_rwRuleSeq;
extern lean_object* l_Lean_Parser_Tactic_optConfig;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_binderIdent;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_discharger;
extern lean_object* l_Lean_Parser_Tactic_dsimpArgs;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simpArgs;
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(232, 67, 39, 189, 45, 247, 54, 81)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 237, 175, 125, 142, 154, 152, 39)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__7_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "`(conv| "};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(232, 67, 39, 189, 45, 247, 54, 81)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__16_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_quot___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__17_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__18_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_conv_quot = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_conv;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "convSeq1Indented"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 35, 202, 76, 198, 168, 114, 30)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "sepBy1IndentSemicolon"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 113, 252, 92, 83, 246, 160, 172)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convSeq1Indented = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "convSeqBracketed"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 46, 60, 206, 104, 220, 125, 67)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sepByIndentSemicolon"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6_value),LEAN_SCALAR_PTR_LITERAL(139, 141, 160, 225, 89, 107, 71, 117)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convSeqBracketed = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "convSeq"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 81, 30, 13, 252, 23, 29, 64)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convSeq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convSeq___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convSeq = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "occsWildcard"};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 134, 186, 55, 123, 29, 184, 158)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_occsWildcard = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "occsIndexed"};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 79, 250, 218, 138, 32, 121, 144)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_occsIndexed = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_occs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "occs"};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 84, 10, 70, 31, 153, 125, 43)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_occs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_occs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_occs___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__11_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__13_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_occs___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ") "};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__13_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_occs___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__16_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_occs___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__17_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_occs = (const lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__17_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "withAnnotateState"};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 133, 126, 96, 213, 194, 239, 44)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "with_annotate_state "};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rawStx"};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 156, 151, 53, 25, 160, 240, 109)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_withAnnotateState = (const lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_skip___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l_Lean_Parser_Tactic_Conv_skip___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_skip___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 180, 41, 36, 18, 201, 24, 192)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_skip___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_skip___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_skip___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_skip___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_skip___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_skip = (const lean_object*)&l_Lean_Parser_Tactic_Conv_skip___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_cbv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l_Lean_Parser_Tactic_Conv_cbv___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_cbv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 158, 11, 110, 229, 69, 84, 167)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_cbv___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_cbv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_cbv___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_cbv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_cbv___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_cbv = (const lean_object*)&l_Lean_Parser_Tactic_Conv_cbv___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_lhs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lhs"};
static const lean_object* l_Lean_Parser_Tactic_Conv_lhs___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_lhs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 125, 121, 151, 86, 248, 18, 33)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_lhs___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_lhs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_lhs___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_lhs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_lhs___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_lhs = (const lean_object*)&l_Lean_Parser_Tactic_Conv_lhs___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_rhs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l_Lean_Parser_Tactic_Conv_rhs___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rhs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 199, 30, 64, 233, 37, 34, 201)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_rhs___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rhs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_rhs___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rhs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_rhs___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_rhs = (const lean_object*)&l_Lean_Parser_Tactic_Conv_rhs___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_fun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Parser_Tactic_Conv_fun___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_fun___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 22, 157, 83, 164, 254, 43, 206)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_fun___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_fun___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_fun___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_fun___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_fun___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_fun = (const lean_object*)&l_Lean_Parser_Tactic_Conv_fun___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_whnf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "whnf"};
static const lean_object* l_Lean_Parser_Tactic_Conv_whnf___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_whnf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 111, 86, 148, 119, 255, 116, 73)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_whnf___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_whnf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_whnf___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_whnf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_whnf___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_whnf = (const lean_object*)&l_Lean_Parser_Tactic_Conv_whnf___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_zeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zeta"};
static const lean_object* l_Lean_Parser_Tactic_Conv_zeta___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_zeta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 143, 59, 185, 170, 152, 3, 30)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_zeta___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_zeta___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_zeta___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_zeta___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_zeta___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_zeta = (const lean_object*)&l_Lean_Parser_Tactic_Conv_zeta___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_reduce___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reduce"};
static const lean_object* l_Lean_Parser_Tactic_Conv_reduce___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_reduce___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 127, 28, 249, 1, 118, 43, 106)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_reduce___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_reduce___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_reduce___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_reduce___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_reduce___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_reduce = (const lean_object*)&l_Lean_Parser_Tactic_Conv_reduce___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_congr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l_Lean_Parser_Tactic_Conv_congr___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_congr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 182, 72, 178, 102, 27, 55, 200)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_congr___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_congr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_congr___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_congr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_congr___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_congr = (const lean_object*)&l_Lean_Parser_Tactic_Conv_congr___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_argArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "argArg"};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 211, 157, 2, 56, 142, 56, 136)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_argArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_argArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_argArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_argArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_argArg___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__12_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_argArg = (const lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_arg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l_Lean_Parser_Tactic_Conv_arg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_arg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 63, 45, 128, 216, 102, 81, 96)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_arg___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_arg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "arg "};
static const lean_object* l_Lean_Parser_Tactic_Conv_arg___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_arg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_arg___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_arg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_arg___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_arg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_arg___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_arg = (const lean_object*)&l_Lean_Parser_Tactic_Conv_arg___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_ext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_ext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 59, 213, 100, 231, 162, 190, 80)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_ext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_ext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_ext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_ext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_ext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__5_value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_ext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_ext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_ext___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_ext___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_ext___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_ext___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_ext___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_ext;
static const lean_string_object l_Lean_Parser_Tactic_Conv_change___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "change"};
static const lean_object* l_Lean_Parser_Tactic_Conv_change___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_change___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 48, 251, 99, 118, 217, 178, 16)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_change___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_change___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "change "};
static const lean_object* l_Lean_Parser_Tactic_Conv_change___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_change___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_change___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_change___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_Tactic_Conv_change___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_change___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__4_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_change___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_change___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Conv_change___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_change___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_change___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_change___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_change___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_change = (const lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_delta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "delta"};
static const lean_object* l_Lean_Parser_Tactic_Conv_delta___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 217, 17, 26, 4, 182, 95, 121)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_delta___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_delta___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_delta___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_Tactic_Conv_delta___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_delta___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_delta___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_delta___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_delta___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_delta___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_delta___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_delta___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_delta = (const lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_unfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unfold"};
static const lean_object* l_Lean_Parser_Tactic_Conv_unfold___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_unfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 13, 86, 191, 228, 222, 83, 199)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_unfold___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_unfold___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_unfold___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_unfold___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_unfold___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_unfold___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_unfold___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_unfold = (const lean_object*)&l_Lean_Parser_Tactic_Conv_unfold___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_pattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pattern"};
static const lean_object* l_Lean_Parser_Tactic_Conv_pattern___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_pattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 139, 144, 223, 221, 17, 152, 53)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_pattern___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_pattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pattern "};
static const lean_object* l_Lean_Parser_Tactic_Conv_pattern___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_pattern___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_pattern___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_pattern___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__17_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_pattern___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_pattern___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_pattern___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_pattern___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_pattern___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_pattern___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_pattern___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_pattern = (const lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l_Lean_Parser_Tactic_Conv_rewrite___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 123, 122, 14, 133, 216, 210, 10)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_rewrite___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_rewrite___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_rewrite___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_rewrite___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_rewrite___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_rewrite___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_rewrite___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_rewrite___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_rewrite___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_rewrite___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_rewrite;
static const lean_string_object l_Lean_Parser_Tactic_Conv_simp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 165, 42, 136, 187, 206, 234, 202)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__5;
static const lean_string_object l_Lean_Parser_Tactic_Conv_simp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " only"};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__9;
static const lean_string_object l_Lean_Parser_Tactic_Conv_simp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__11_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__12;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__13;
static const lean_string_object l_Lean_Parser_Tactic_Conv_simp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__14_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_simp___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simp___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__16_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__17;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__18;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__19;
static const lean_string_object l_Lean_Parser_Tactic_Conv_simp___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simp___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__20_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__21_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__22;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__23;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__24;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simp___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simp___closed__25;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_simp;
static const lean_string_object l_Lean_Parser_Tactic_Conv_simpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpTrace"};
static const lean_object* l_Lean_Parser_Tactic_Conv_simpTrace___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_simpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 24, 207, 89, 155, 142, 251, 55)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simpTrace___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_simpTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "simp\?"};
static const lean_object* l_Lean_Parser_Tactic_Conv_simpTrace___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simpTrace___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simpTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simpTrace___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simpTrace___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simpTrace___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simpTrace___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simpTrace___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simpTrace___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simpTrace___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simpTrace___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simpTrace___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simpTrace___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simpTrace___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simpTrace___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_simpTrace___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_simpTrace___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_simpTrace;
static const lean_string_object l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 35, 2, 104, 74, 78, 120, 9)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_dsimp___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimp___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimp___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimp___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimp___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_dsimp;
static const lean_string_object l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dsimpTrace"};
static const lean_object* l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 139, 45, 80, 126, 130, 141, 19)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "dsimp\?"};
static const lean_object* l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_dsimpTrace;
static const lean_string_object l_Lean_Parser_Tactic_Conv_simpMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpMatch"};
static const lean_object* l_Lean_Parser_Tactic_Conv_simpMatch___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 31, 17, 130, 102, 107, 154, 37)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simpMatch___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_simpMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simp_match"};
static const lean_object* l_Lean_Parser_Tactic_Conv_simpMatch___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpMatch___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simpMatch___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_simpMatch___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_simpMatch___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_simpMatch = (const lean_object*)&l_Lean_Parser_Tactic_Conv_simpMatch___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_clear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clear"};
static const lean_object* l_Lean_Parser_Tactic_Conv_clear___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_clear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 78, 175, 7, 2, 107, 214, 173)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_clear___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_clear___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_clear___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_clear___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__5_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Conv_clear___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_clear___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_clear___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_clear___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_clear___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_clear___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_clear___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_clear___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_clear___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_clear = (const lean_object*)&l_Lean_Parser_Tactic_Conv_clear___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "nestedTacticCore"};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 23, 62, 30, 134, 160, 158, 203)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "tactic'"};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_nestedTacticCore = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedTactic"};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 28, 213, 2, 207, 8, 223, 137)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_nestedTactic = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "convTactic"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTactic___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 239, 251, 250, 179, 30, 250, 48)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTactic___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "conv'"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTactic___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTactic___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTactic___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTactic___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTactic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTactic___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convTactic = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTactic___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_nestedConv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "nestedConv"};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedConv___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedConv___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedConv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 174, 232, 149, 164, 188, 109, 191)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedConv___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_nestedConv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_nestedConv___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedConv___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_nestedConv = (const lean_object*)&l_Lean_Parser_Tactic_Conv_nestedConv___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_paren___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Parser_Tactic_Conv_paren___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_paren___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 172, 52, 155, 88, 222, 189, 57)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_paren___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_paren___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occs___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_paren___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_paren___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_paren___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_paren___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_paren___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_paren___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_paren___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_paren___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_paren___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_paren = (const lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convRfl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "convRfl"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRfl___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 42, 80, 127, 121, 246, 194, 78)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRfl___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convRfl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRfl___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRfl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRfl___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRfl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRfl___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convRfl = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRfl___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_convDone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "convDone"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convDone___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convDone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 92, 241, 196, 189, 115, 58, 157)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convDone___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convDone___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convDone___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convDone___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convDone___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convDone___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convDone___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convDone = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convDone___closed__2_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "convTrace_state"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 26, 191, 85, 36, 254, 172, 75)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "trace_state"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convTrace__state = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "traceState"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 119, 9, 141, 95, 188, 244, 206)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l_Lean_Parser_Tactic_Conv_allGoals___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 55, 182, 70, 128, 26, 115, 15)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_allGoals___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_allGoals___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "all_goals "};
static const lean_object* l_Lean_Parser_Tactic_Conv_allGoals___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_allGoals___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_allGoals___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_allGoals___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_allGoals___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_allGoals___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_allGoals___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_allGoals = (const lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "all_goals"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "anyGoals"};
static const lean_object* l_Lean_Parser_Tactic_Conv_anyGoals___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 41, 143, 75, 238, 57, 26, 246)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_anyGoals___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_anyGoals___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "any_goals "};
static const lean_object* l_Lean_Parser_Tactic_Conv_anyGoals___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_anyGoals___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_anyGoals___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_anyGoals___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_anyGoals___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_anyGoals___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_anyGoals___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_anyGoals = (const lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 19, 163, 3, 232, 106, 175, 32)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "any_goals"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_case___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "case"};
static const lean_object* l_Lean_Parser_Tactic_Conv_case___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 23, 91, 126, 214, 77, 25, 163)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_case___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_case___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case "};
static const lean_object* l_Lean_Parser_Tactic_Conv_case___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_case___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_case___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Parser_Tactic_Conv_case___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_case___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_case___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_case___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_case___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_case___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_case___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_case___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_case___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_case___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_case___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_case___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_case;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_case___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 244, 120, 128, 139, 198, 139, 51)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case'"};
static const lean_object* l_Lean_Parser_Tactic_Conv_case_x27___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 157, 98, 160, 189, 128, 94, 31)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_case_x27___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_case_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "case' "};
static const lean_object* l_Lean_Parser_Tactic_Conv_case_x27___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_case_x27___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_case_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_case_x27___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_case_x27___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_case_x27___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_case_x27___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_case_x27___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_case_x27___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_case_x27___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_case_x27___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_case_x27___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_case_x27___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_case_x27___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_case_x27;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 21, 185, 205, 238, 88, 7, 106)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "convNext__=>_"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 255, 234, 0, 142, 69, 158, 51)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "next"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_focus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "focus"};
static const lean_object* l_Lean_Parser_Tactic_Conv_focus___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_focus___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 104, 36, 236, 86, 45, 58, 207)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_focus___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_focus___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "focus "};
static const lean_object* l_Lean_Parser_Tactic_Conv_focus___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_focus___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_focus___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_focus___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_focus___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_focus___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_focus___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_focus = (const lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_focus___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 223, 207, 6, 131, 57, 182, 221)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "convConvSeq"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 85, 97, 250, 95, 212, 248, 253)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convConvSeq = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 6, .m_data = "conv·_"};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 17, 134, 179, 95, 143, 156, 206)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "· "};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_conv_xb7__ = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv_xb7____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv_xb7____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "failIfSuccess"};
static const lean_object* l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 74, 242, 37, 111, 42, 66, 94)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fail_if_success "};
static const lean_object* l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_failIfSuccess = (const lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 159, 155, 237, 20, 68, 221, 246)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fail_if_success"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "convRw__"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 150, 200, 64, 217, 142, 60, 16)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rw"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_convRw____;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRw______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRw______1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "convErw__"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 240, 248, 235, 235, 171, 22, 12)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "erw"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_convErw____;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "valConfigItem"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(135, 67, 19, 169, 17, 95, 109, 188)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "transparency"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(185, 88, 49, 212, 108, 152, 53, 137)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(29, 214, 131, 210, 10, 90, 37, 134)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Inhabited"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(174, 152, 115, 107, 166, 56, 116, 8)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18_value),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_convArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "convArgs"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convArgs___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 1, 159, 69, 155, 70, 85, 122)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convArgs___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "args"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convArgs___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convArgs___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convArgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convArgs___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convArgs = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convArgs___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convArgs__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convArgs__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_convLeft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "convLeft"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convLeft___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 230, 157, 228, 176, 103, 184, 79)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convLeft___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convLeft___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convLeft___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convLeft___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convLeft___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convLeft___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convLeft___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convLeft = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convLeft___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convLeft__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convLeft__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_convRight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "convRight"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRight___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRight___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 17, 134, 30, 162, 108, 108, 144)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRight___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convRight___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRight___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRight___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRight___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRight___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRight___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convRight = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRight___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRight__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRight__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "convIntro___"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 68, 154, 126, 169, 192, 138, 68)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_convIntro______;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convIntro________1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convIntro________1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "enterPattern"};
static const lean_object* l_Lean_Parser_Tactic_Conv_enterPattern___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 190, 181, 104, 228, 19, 208, 104)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_enterPattern___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_enterPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "in "};
static const lean_object* l_Lean_Parser_Tactic_Conv_enterPattern___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterPattern___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_enterPattern___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterPattern___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_enterPattern___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterPattern___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_enterPattern___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_enterPattern___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_enterPattern = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_enterArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "enterArg"};
static const lean_object* l_Lean_Parser_Tactic_Conv_enterArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enterArg___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_enterArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 39, 81, 184, 62, 123, 191, 109)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_enterArg___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enterArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__12_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_enterArg___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enterArg___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_enterArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_enterArg___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_enterArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_enterArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_enterArg;
static const lean_string_object l_Lean_Parser_Tactic_Conv_enter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "enter"};
static const lean_object* l_Lean_Parser_Tactic_Conv_enter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_enter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 212, 211, 21, 88, 173, 115, 108)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_enter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enter___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_enter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_enter___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enter___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_enter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_enter___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_simp___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_enter___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_enter___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_enter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_enter___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_enter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_enter___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_enter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_enter___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_enter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_enter___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_enter___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_enter___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_enter;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convApply___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "convApply_"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convApply___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 7, 29, 82, 157, 206, 45, 91)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convApply___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convApply___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "apply "};
static const lean_object* l_Lean_Parser_Tactic_Conv_convApply___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convApply___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convApply___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convApply___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convApply___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convApply___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convApply___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convApply__ = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convApply___00__closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_first___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 113, 181, 219, 229, 158, 34, 244)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_first___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "first "};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_first___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__4_value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_first___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__6_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_first___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__8_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_first___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__10_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__13_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_first___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__14_value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__13_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__16_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__17_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_first___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "| "};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__18_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__17_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__19_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__20_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__21_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__22 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__22_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__22_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__23_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__24_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__24_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__25_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_first___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__25_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_first___closed__26 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__26_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_first = (const lean_object*)&l_Lean_Parser_Tactic_Conv_first___closed__26_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convTry___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "convTry_"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTry___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 99, 115, 76, 123, 72, 244, 211)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTry___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convTry___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "try "};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTry___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTry___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTry___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTry___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTry___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convTry___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convTry___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convTry__ = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convTry___00__closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTry____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTry____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "conv_<;>_"};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 57, 152, 10, 187, 180, 111, 39)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " <;> "};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e__ = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_paren___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "convRepeat_"};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 38, 239, 209, 98, 101, 29, 196)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "repeat "};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_convRepeat__ = (const lean_object*)&l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "repeat"};
static const lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Conv_extractLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLets"};
static const lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 111, 123, 142, 92, 98, 88, 43)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_extractLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "extract_lets "};
static const lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_extractLets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_extractLets___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__4;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_extractLets___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 163, 83, 191, 48, 55, 64, 87)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_extractLets___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_extractLets___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_extractLets___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_extractLets___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_ext___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_extractLets___closed__9_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_extractLets___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_extractLets___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_extractLets___closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_extractLets;
static const lean_string_object l_Lean_Parser_Tactic_Conv_liftLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "liftLets"};
static const lean_object* l_Lean_Parser_Tactic_Conv_liftLets___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_liftLets___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_liftLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 68, 102, 93, 72, 158, 25, 211)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_liftLets___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_liftLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lift_lets "};
static const lean_object* l_Lean_Parser_Tactic_Conv_liftLets___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_liftLets___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_liftLets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_liftLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_liftLets___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_liftLets___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_liftLets___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_liftLets___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Conv_liftLets___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Conv_liftLets___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv_liftLets;
static const lean_string_object l_Lean_Parser_Tactic_Conv_letToHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letToHave"};
static const lean_object* l_Lean_Parser_Tactic_Conv_letToHave___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 168, 69, 201, 229, 158, 224, 21)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_letToHave___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_letToHave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let_to_have"};
static const lean_object* l_Lean_Parser_Tactic_Conv_letToHave___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_letToHave___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_letToHave___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_letToHave___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_letToHave___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_letToHave = (const lean_object*)&l_Lean_Parser_Tactic_Conv_letToHave___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(192, 39, 103, 162, 58, 5, 181, 114)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " at "};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__1_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_delta___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_conv___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_pattern___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_change___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_argArg___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__11_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__12_value),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_conv___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__0_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_conv___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_conv = (const lean_object*)&l_Lean_Parser_Tactic_Conv_conv___closed__14_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_normCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "normCast"};
static const lean_object* l_Lean_Parser_Tactic_Conv_normCast___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_normCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 210, 228, 19, 50, 14, 27, 75)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_normCast___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Conv_normCast___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "norm_cast"};
static const lean_object* l_Lean_Parser_Tactic_Conv_normCast___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_normCast___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_normCast___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Conv_normCast___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Conv_normCast___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Conv_normCast = (const lean_object*)&l_Lean_Parser_Tactic_Conv_normCast___closed__4_value;
static lean_object* _init_l_Lean_Parser_Category_conv(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_ext___closed__9(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = l_Lean_binderIdent;
v___x_463_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_ext___closed__8));
v___x_464_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_465_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_463_);
lean_ctor_set(v___x_465_, 2, v___x_462_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_ext___closed__10(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_ext___closed__9, &l_Lean_Parser_Tactic_Conv_ext___closed__9_once, _init_l_Lean_Parser_Tactic_Conv_ext___closed__9);
v___x_467_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_ext___closed__4));
v___x_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_ext___closed__11(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_469_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_ext___closed__10, &l_Lean_Parser_Tactic_Conv_ext___closed__10_once, _init_l_Lean_Parser_Tactic_Conv_ext___closed__10);
v___x_470_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_ext___closed__2));
v___x_471_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_472_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_ctor_set(v___x_472_, 2, v___x_469_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_ext___closed__12(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_473_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_ext___closed__11, &l_Lean_Parser_Tactic_Conv_ext___closed__11_once, _init_l_Lean_Parser_Tactic_Conv_ext___closed__11);
v___x_474_ = lean_unsigned_to_nat(1022u);
v___x_475_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_ext___closed__1));
v___x_476_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v___x_474_);
lean_ctor_set(v___x_476_, 2, v___x_473_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_ext(void){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_ext___closed__12, &l_Lean_Parser_Tactic_Conv_ext___closed__12_once, _init_l_Lean_Parser_Tactic_Conv_ext___closed__12);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__3(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = l_Lean_Parser_Tactic_optConfig;
v___x_592_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_rewrite___closed__2));
v___x_593_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_594_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
lean_ctor_set(v___x_594_, 2, v___x_591_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__4(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_595_ = l_Lean_Parser_Tactic_rwRuleSeq;
v___x_596_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_rewrite___closed__3, &l_Lean_Parser_Tactic_Conv_rewrite___closed__3_once, _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__3);
v___x_597_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_598_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
lean_ctor_set(v___x_598_, 2, v___x_595_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__5(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_599_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_rewrite___closed__4, &l_Lean_Parser_Tactic_Conv_rewrite___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__4);
v___x_600_ = lean_unsigned_to_nat(1022u);
v___x_601_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_rewrite___closed__1));
v___x_602_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
lean_ctor_set(v___x_602_, 2, v___x_599_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_rewrite(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_rewrite___closed__5, &l_Lean_Parser_Tactic_Conv_rewrite___closed__5_once, _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__5);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__3(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_614_ = l_Lean_Parser_Tactic_optConfig;
v___x_615_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__2));
v___x_616_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_617_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
lean_ctor_set(v___x_617_, 2, v___x_614_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__4(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = l_Lean_Parser_Tactic_discharger;
v___x_619_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_argArg___closed__3));
v___x_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
return v___x_620_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__5(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_621_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__4, &l_Lean_Parser_Tactic_Conv_simp___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__4);
v___x_622_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__3, &l_Lean_Parser_Tactic_Conv_simp___closed__3_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__3);
v___x_623_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_624_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v___x_622_);
lean_ctor_set(v___x_624_, 2, v___x_621_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__9(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_632_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__8));
v___x_633_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__5, &l_Lean_Parser_Tactic_Conv_simp___closed__5_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__5);
v___x_634_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_635_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
lean_ctor_set(v___x_635_, 2, v___x_632_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__12(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_639_ = l_Lean_Parser_Tactic_simpLemma;
v___x_640_ = l_Lean_Parser_Tactic_simpErase;
v___x_641_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq___closed__3));
v___x_642_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
lean_ctor_set(v___x_642_, 2, v___x_639_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__13(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_643_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__12, &l_Lean_Parser_Tactic_Conv_simp___closed__12_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__12);
v___x_644_ = l_Lean_Parser_Tactic_simpStar;
v___x_645_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq___closed__3));
v___x_646_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
lean_ctor_set(v___x_646_, 2, v___x_643_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__17(void){
_start:
{
uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_651_ = 0;
v___x_652_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__16));
v___x_653_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__14));
v___x_654_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__13, &l_Lean_Parser_Tactic_Conv_simp___closed__13_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__13);
v___x_655_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
lean_ctor_set(v___x_655_, 2, v___x_652_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*3, v___x_651_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__18(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__17, &l_Lean_Parser_Tactic_Conv_simp___closed__17_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__17);
v___x_657_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5));
v___x_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___x_656_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__19(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_659_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__18, &l_Lean_Parser_Tactic_Conv_simp___closed__18_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__18);
v___x_660_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__11));
v___x_661_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_662_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v___x_660_);
lean_ctor_set(v___x_662_, 2, v___x_659_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__22(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_666_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__21));
v___x_667_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__19, &l_Lean_Parser_Tactic_Conv_simp___closed__19_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__19);
v___x_668_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_669_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v___x_667_);
lean_ctor_set(v___x_669_, 2, v___x_666_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__23(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__22, &l_Lean_Parser_Tactic_Conv_simp___closed__22_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__22);
v___x_671_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_argArg___closed__3));
v___x_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_670_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__24(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_673_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__23, &l_Lean_Parser_Tactic_Conv_simp___closed__23_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__23);
v___x_674_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__9, &l_Lean_Parser_Tactic_Conv_simp___closed__9_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__9);
v___x_675_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_676_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___x_674_);
lean_ctor_set(v___x_676_, 2, v___x_673_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp___closed__25(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_677_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__24, &l_Lean_Parser_Tactic_Conv_simp___closed__24_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__24);
v___x_678_ = lean_unsigned_to_nat(1022u);
v___x_679_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__1));
v___x_680_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_678_);
lean_ctor_set(v___x_680_, 2, v___x_677_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simp(void){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__25, &l_Lean_Parser_Tactic_Conv_simp___closed__25_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__25);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__4(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_693_ = l_Lean_Parser_Tactic_optConfig;
v___x_694_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simpTrace___closed__3));
v___x_695_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_696_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_694_);
lean_ctor_set(v___x_696_, 2, v___x_693_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__5(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_697_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__4, &l_Lean_Parser_Tactic_Conv_simp___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__4);
v___x_698_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simpTrace___closed__4, &l_Lean_Parser_Tactic_Conv_simpTrace___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__4);
v___x_699_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_700_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_698_);
lean_ctor_set(v___x_700_, 2, v___x_697_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__6(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_701_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__8));
v___x_702_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simpTrace___closed__5, &l_Lean_Parser_Tactic_Conv_simpTrace___closed__5_once, _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__5);
v___x_703_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_704_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_702_);
lean_ctor_set(v___x_704_, 2, v___x_701_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__7(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = l_Lean_Parser_Tactic_simpArgs;
v___x_706_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_argArg___closed__3));
v___x_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___x_705_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__8(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_708_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simpTrace___closed__7, &l_Lean_Parser_Tactic_Conv_simpTrace___closed__7_once, _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__7);
v___x_709_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simpTrace___closed__6, &l_Lean_Parser_Tactic_Conv_simpTrace___closed__6_once, _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__6);
v___x_710_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_711_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___x_709_);
lean_ctor_set(v___x_711_, 2, v___x_708_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__9(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_712_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simpTrace___closed__8, &l_Lean_Parser_Tactic_Conv_simpTrace___closed__8_once, _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__8);
v___x_713_ = lean_unsigned_to_nat(1022u);
v___x_714_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simpTrace___closed__1));
v___x_715_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
lean_ctor_set(v___x_715_, 2, v___x_712_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_simpTrace(void){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simpTrace___closed__9, &l_Lean_Parser_Tactic_Conv_simpTrace___closed__9_once, _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__9);
return v___x_716_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__3(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = l_Lean_Parser_Tactic_optConfig;
v___x_728_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_dsimp___closed__2));
v___x_729_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_730_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
lean_ctor_set(v___x_730_, 2, v___x_727_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__4(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_731_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__4, &l_Lean_Parser_Tactic_Conv_simp___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__4);
v___x_732_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimp___closed__3, &l_Lean_Parser_Tactic_Conv_dsimp___closed__3_once, _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__3);
v___x_733_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_734_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
lean_ctor_set(v___x_734_, 2, v___x_731_);
return v___x_734_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__5(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_735_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__8));
v___x_736_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimp___closed__4, &l_Lean_Parser_Tactic_Conv_dsimp___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__4);
v___x_737_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_738_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
lean_ctor_set(v___x_738_, 2, v___x_735_);
return v___x_738_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__6(void){
_start:
{
uint8_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_739_ = 0;
v___x_740_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__16));
v___x_741_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__14));
v___x_742_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_simp___closed__12, &l_Lean_Parser_Tactic_Conv_simp___closed__12_once, _init_l_Lean_Parser_Tactic_Conv_simp___closed__12);
v___x_743_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
lean_ctor_set(v___x_743_, 2, v___x_740_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*3, v___x_739_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__7(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimp___closed__6, &l_Lean_Parser_Tactic_Conv_dsimp___closed__6_once, _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__6);
v___x_745_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5));
v___x_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__8(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_747_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimp___closed__7, &l_Lean_Parser_Tactic_Conv_dsimp___closed__7_once, _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__7);
v___x_748_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__11));
v___x_749_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_750_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
lean_ctor_set(v___x_750_, 2, v___x_747_);
return v___x_750_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__9(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_751_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__21));
v___x_752_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimp___closed__8, &l_Lean_Parser_Tactic_Conv_dsimp___closed__8_once, _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__8);
v___x_753_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_754_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
lean_ctor_set(v___x_754_, 2, v___x_751_);
return v___x_754_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__10(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimp___closed__9, &l_Lean_Parser_Tactic_Conv_dsimp___closed__9_once, _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__9);
v___x_756_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_argArg___closed__3));
v___x_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v___x_755_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__11(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_758_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimp___closed__10, &l_Lean_Parser_Tactic_Conv_dsimp___closed__10_once, _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__10);
v___x_759_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimp___closed__5, &l_Lean_Parser_Tactic_Conv_dsimp___closed__5_once, _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__5);
v___x_760_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_761_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___x_759_);
lean_ctor_set(v___x_761_, 2, v___x_758_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__12(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_762_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimp___closed__11, &l_Lean_Parser_Tactic_Conv_dsimp___closed__11_once, _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__11);
v___x_763_ = lean_unsigned_to_nat(1022u);
v___x_764_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_dsimp___closed__1));
v___x_765_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
lean_ctor_set(v___x_765_, 2, v___x_762_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimp(void){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimp___closed__12, &l_Lean_Parser_Tactic_Conv_dsimp___closed__12_once, _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__12);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_778_ = l_Lean_Parser_Tactic_optConfig;
v___x_779_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3));
v___x_780_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_781_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_779_);
lean_ctor_set(v___x_781_, 2, v___x_778_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_782_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__8));
v___x_783_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4, &l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4);
v___x_784_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_785_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v___x_783_);
lean_ctor_set(v___x_785_, 2, v___x_782_);
return v___x_785_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = l_Lean_Parser_Tactic_dsimpArgs;
v___x_787_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_argArg___closed__3));
v___x_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___x_786_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_789_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6, &l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6_once, _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6);
v___x_790_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5, &l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5_once, _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5);
v___x_791_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_792_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___x_790_);
lean_ctor_set(v___x_792_, 2, v___x_789_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_793_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7, &l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7_once, _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7);
v___x_794_ = lean_unsigned_to_nat(1022u);
v___x_795_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1));
v___x_796_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___x_794_);
lean_ctor_set(v___x_796_, 2, v___x_793_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_dsimpTrace(void){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8, &l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8_once, _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1(lean_object* v_x_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convRfl___closed__1));
v___x_1002_ = l_Lean_Syntax_isOfKind(v_x_998_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_box(1);
v___x_1004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v_a_1000_);
return v___x_1004_;
}
else
{
lean_object* v_ref_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_ref_1005_ = lean_ctor_get(v_a_999_, 5);
v___x_1006_ = 0;
v___x_1007_ = l_Lean_SourceInfo_fromRef(v_ref_1005_, v___x_1006_);
v___x_1008_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1));
v___x_1009_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2));
lean_inc(v___x_1007_);
v___x_1010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_1007_);
v___x_1012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1007_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1));
v___x_1014_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3));
v___x_1015_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1016_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7));
v___x_1017_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convRfl___closed__2));
lean_inc(v___x_1007_);
v___x_1018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1007_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
lean_inc(v___x_1007_);
v___x_1019_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1016_, v___x_1018_);
lean_inc(v___x_1007_);
v___x_1020_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1015_, v___x_1019_);
lean_inc(v___x_1007_);
v___x_1021_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1014_, v___x_1020_);
lean_inc(v___x_1007_);
v___x_1022_ = l_Lean_Syntax_node1(v___x_1007_, v___x_1013_, v___x_1021_);
v___x_1023_ = l_Lean_Syntax_node3(v___x_1007_, v___x_1008_, v___x_1010_, v___x_1012_, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_a_1000_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___boxed(lean_object* v_x_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1(v_x_1025_, v_a_1026_, v_a_1027_);
lean_dec_ref(v_a_1026_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1(lean_object* v_x_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convDone___closed__1));
v___x_1054_ = l_Lean_Syntax_isOfKind(v_x_1050_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_box(1);
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v_a_1052_);
return v___x_1056_;
}
else
{
lean_object* v_ref_1057_; uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_ref_1057_ = lean_ctor_get(v_a_1051_, 5);
v___x_1058_ = 0;
v___x_1059_ = l_Lean_SourceInfo_fromRef(v_ref_1057_, v___x_1058_);
v___x_1060_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1));
v___x_1061_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2));
lean_inc(v___x_1059_);
v___x_1062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1059_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_1059_);
v___x_1064_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1059_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1));
v___x_1066_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3));
v___x_1067_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1068_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convDone___closed__2));
v___x_1069_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0));
lean_inc(v___x_1059_);
v___x_1070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1059_);
lean_ctor_set(v___x_1070_, 1, v___x_1068_);
lean_inc(v___x_1059_);
v___x_1071_ = l_Lean_Syntax_node1(v___x_1059_, v___x_1069_, v___x_1070_);
lean_inc(v___x_1059_);
v___x_1072_ = l_Lean_Syntax_node1(v___x_1059_, v___x_1067_, v___x_1071_);
lean_inc(v___x_1059_);
v___x_1073_ = l_Lean_Syntax_node1(v___x_1059_, v___x_1066_, v___x_1072_);
lean_inc(v___x_1059_);
v___x_1074_ = l_Lean_Syntax_node1(v___x_1059_, v___x_1065_, v___x_1073_);
v___x_1075_ = l_Lean_Syntax_node3(v___x_1059_, v___x_1060_, v___x_1062_, v___x_1064_, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v_a_1052_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___boxed(lean_object* v_x_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1(v_x_1077_, v_a_1078_, v_a_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1(lean_object* v_x_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1));
v___x_1107_ = l_Lean_Syntax_isOfKind(v_x_1103_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_box(1);
v___x_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_a_1105_);
return v___x_1109_;
}
else
{
lean_object* v_ref_1110_; uint8_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_ref_1110_ = lean_ctor_get(v_a_1104_, 5);
v___x_1111_ = 0;
v___x_1112_ = l_Lean_SourceInfo_fromRef(v_ref_1110_, v___x_1111_);
v___x_1113_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1));
v___x_1114_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2));
lean_inc(v___x_1112_);
v___x_1115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1112_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_1112_);
v___x_1117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1112_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1));
v___x_1119_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3));
v___x_1120_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1121_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1));
v___x_1122_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2));
lean_inc(v___x_1112_);
v___x_1123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1112_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
lean_inc(v___x_1112_);
v___x_1124_ = l_Lean_Syntax_node1(v___x_1112_, v___x_1121_, v___x_1123_);
lean_inc(v___x_1112_);
v___x_1125_ = l_Lean_Syntax_node1(v___x_1112_, v___x_1120_, v___x_1124_);
lean_inc(v___x_1112_);
v___x_1126_ = l_Lean_Syntax_node1(v___x_1112_, v___x_1119_, v___x_1125_);
lean_inc(v___x_1112_);
v___x_1127_ = l_Lean_Syntax_node1(v___x_1112_, v___x_1118_, v___x_1126_);
v___x_1128_ = l_Lean_Syntax_node3(v___x_1112_, v___x_1113_, v___x_1115_, v___x_1117_, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v_a_1105_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___boxed(lean_object* v_x_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1(v_x_1130_, v_a_1131_, v_a_1132_);
lean_dec_ref(v_a_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1(lean_object* v_x_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_allGoals___closed__1));
lean_inc(v_x_1160_);
v___x_1164_ = l_Lean_Syntax_isOfKind(v_x_1160_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec(v_x_1160_);
v___x_1165_ = lean_box(1);
v___x_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v_a_1162_);
return v___x_1166_;
}
else
{
lean_object* v_ref_1167_; lean_object* v___x_1168_; lean_object* v_tk_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_ref_1167_ = lean_ctor_get(v_a_1161_, 5);
v___x_1168_ = lean_unsigned_to_nat(0u);
v_tk_1169_ = l_Lean_Syntax_getArg(v_x_1160_, v___x_1168_);
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = l_Lean_Syntax_getArg(v_x_1160_, v___x_1170_);
lean_dec(v_x_1160_);
v___x_1172_ = 0;
v___x_1173_ = l_Lean_SourceInfo_fromRef(v_ref_1167_, v___x_1172_);
v___x_1174_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1));
v___x_1175_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2));
lean_inc(v___x_1173_);
v___x_1176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1173_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_1173_);
v___x_1178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1173_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1));
v___x_1180_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3));
v___x_1181_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1182_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0));
v___x_1183_ = l_Lean_SourceInfo_fromRef(v_tk_1169_, v___x_1164_);
lean_dec(v_tk_1169_);
v___x_1184_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1));
v___x_1185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__1));
v___x_1187_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__2));
lean_inc(v___x_1173_);
v___x_1188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1173_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
lean_inc_ref(v___x_1178_);
lean_inc(v___x_1173_);
v___x_1189_ = l_Lean_Syntax_node3(v___x_1173_, v___x_1186_, v___x_1188_, v___x_1178_, v___x_1171_);
lean_inc(v___x_1173_);
v___x_1190_ = l_Lean_Syntax_node1(v___x_1173_, v___x_1181_, v___x_1189_);
lean_inc(v___x_1173_);
v___x_1191_ = l_Lean_Syntax_node1(v___x_1173_, v___x_1180_, v___x_1190_);
lean_inc(v___x_1173_);
v___x_1192_ = l_Lean_Syntax_node1(v___x_1173_, v___x_1179_, v___x_1191_);
lean_inc(v___x_1173_);
v___x_1193_ = l_Lean_Syntax_node2(v___x_1173_, v___x_1182_, v___x_1185_, v___x_1192_);
lean_inc(v___x_1173_);
v___x_1194_ = l_Lean_Syntax_node1(v___x_1173_, v___x_1181_, v___x_1193_);
lean_inc(v___x_1173_);
v___x_1195_ = l_Lean_Syntax_node1(v___x_1173_, v___x_1180_, v___x_1194_);
lean_inc(v___x_1173_);
v___x_1196_ = l_Lean_Syntax_node1(v___x_1173_, v___x_1179_, v___x_1195_);
v___x_1197_ = l_Lean_Syntax_node3(v___x_1173_, v___x_1174_, v___x_1176_, v___x_1178_, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v_a_1162_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___boxed(lean_object* v_x_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1(v_x_1199_, v_a_1200_, v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1(lean_object* v_x_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1));
lean_inc(v_x_1229_);
v___x_1233_ = l_Lean_Syntax_isOfKind(v_x_1229_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec(v_x_1229_);
v___x_1234_ = lean_box(1);
v___x_1235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v_a_1231_);
return v___x_1235_;
}
else
{
lean_object* v_ref_1236_; lean_object* v___x_1237_; lean_object* v_tk_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_ref_1236_ = lean_ctor_get(v_a_1230_, 5);
v___x_1237_ = lean_unsigned_to_nat(0u);
v_tk_1238_ = l_Lean_Syntax_getArg(v_x_1229_, v___x_1237_);
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = l_Lean_Syntax_getArg(v_x_1229_, v___x_1239_);
lean_dec(v_x_1229_);
v___x_1241_ = 0;
v___x_1242_ = l_Lean_SourceInfo_fromRef(v_ref_1236_, v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1));
v___x_1244_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2));
lean_inc(v___x_1242_);
v___x_1245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1242_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_1242_);
v___x_1247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1242_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1));
v___x_1249_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3));
v___x_1250_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1251_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0));
v___x_1252_ = l_Lean_SourceInfo_fromRef(v_tk_1238_, v___x_1233_);
lean_dec(v_tk_1238_);
v___x_1253_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1));
v___x_1254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__1));
v___x_1256_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__2));
lean_inc(v___x_1242_);
v___x_1257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1242_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
lean_inc_ref(v___x_1247_);
lean_inc(v___x_1242_);
v___x_1258_ = l_Lean_Syntax_node3(v___x_1242_, v___x_1255_, v___x_1257_, v___x_1247_, v___x_1240_);
lean_inc(v___x_1242_);
v___x_1259_ = l_Lean_Syntax_node1(v___x_1242_, v___x_1250_, v___x_1258_);
lean_inc(v___x_1242_);
v___x_1260_ = l_Lean_Syntax_node1(v___x_1242_, v___x_1249_, v___x_1259_);
lean_inc(v___x_1242_);
v___x_1261_ = l_Lean_Syntax_node1(v___x_1242_, v___x_1248_, v___x_1260_);
lean_inc(v___x_1242_);
v___x_1262_ = l_Lean_Syntax_node2(v___x_1242_, v___x_1251_, v___x_1254_, v___x_1261_);
lean_inc(v___x_1242_);
v___x_1263_ = l_Lean_Syntax_node1(v___x_1242_, v___x_1250_, v___x_1262_);
lean_inc(v___x_1242_);
v___x_1264_ = l_Lean_Syntax_node1(v___x_1242_, v___x_1249_, v___x_1263_);
lean_inc(v___x_1242_);
v___x_1265_ = l_Lean_Syntax_node1(v___x_1242_, v___x_1248_, v___x_1264_);
v___x_1266_ = l_Lean_Syntax_node3(v___x_1242_, v___x_1243_, v___x_1245_, v___x_1247_, v___x_1265_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v_a_1231_);
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___boxed(lean_object* v_x_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1(v_x_1268_, v_a_1269_, v_a_1270_);
lean_dec_ref(v_a_1269_);
return v_res_1271_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_case___closed__6(void){
_start:
{
uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1286_ = 0;
v___x_1287_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case___closed__5));
v___x_1288_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case___closed__4));
v___x_1289_ = l_Lean_Parser_Tactic_caseArg;
v___x_1290_ = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___x_1288_);
lean_ctor_set(v___x_1290_, 2, v___x_1287_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*3, v___x_1286_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_case___closed__7(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1291_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_case___closed__6, &l_Lean_Parser_Tactic_Conv_case___closed__6_once, _init_l_Lean_Parser_Tactic_Conv_case___closed__6);
v___x_1292_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case___closed__3));
v___x_1293_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1294_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v___x_1292_);
lean_ctor_set(v___x_1294_, 2, v___x_1291_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_case___closed__8(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1295_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5));
v___x_1296_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_case___closed__7, &l_Lean_Parser_Tactic_Conv_case___closed__7_once, _init_l_Lean_Parser_Tactic_Conv_case___closed__7);
v___x_1297_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1298_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v___x_1296_);
lean_ctor_set(v___x_1298_, 2, v___x_1295_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_case___closed__9(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1299_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq));
v___x_1300_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_case___closed__8, &l_Lean_Parser_Tactic_Conv_case___closed__8_once, _init_l_Lean_Parser_Tactic_Conv_case___closed__8);
v___x_1301_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1302_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1300_);
lean_ctor_set(v___x_1302_, 2, v___x_1299_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_case___closed__10(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1303_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_case___closed__9, &l_Lean_Parser_Tactic_Conv_case___closed__9_once, _init_l_Lean_Parser_Tactic_Conv_case___closed__9);
v___x_1304_ = lean_unsigned_to_nat(1022u);
v___x_1305_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case___closed__1));
v___x_1306_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v___x_1304_);
lean_ctor_set(v___x_1306_, 2, v___x_1303_);
return v___x_1306_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_case(void){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_case___closed__10, &l_Lean_Parser_Tactic_Conv_case___closed__10_once, _init_l_Lean_Parser_Tactic_Conv_case___closed__10);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1(void){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Array_mkArray0(lean_box(0));
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1(lean_object* v_x_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1318_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case___closed__0));
v___x_1319_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case___closed__1));
lean_inc(v_x_1315_);
v___x_1320_ = l_Lean_Syntax_isOfKind(v_x_1315_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v_x_1315_);
v___x_1321_ = lean_box(1);
v___x_1322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v_a_1317_);
return v___x_1322_;
}
else
{
lean_object* v_ref_1323_; lean_object* v___x_1324_; lean_object* v_tk_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v_arr_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_ref_1323_ = lean_ctor_get(v_a_1316_, 5);
v___x_1324_ = lean_unsigned_to_nat(0u);
v_tk_1325_ = l_Lean_Syntax_getArg(v_x_1315_, v___x_1324_);
v___x_1326_ = lean_unsigned_to_nat(1u);
v___x_1327_ = l_Lean_Syntax_getArg(v_x_1315_, v___x_1326_);
v___x_1328_ = lean_unsigned_to_nat(2u);
v_arr_1329_ = l_Lean_Syntax_getArg(v_x_1315_, v___x_1328_);
v___x_1330_ = lean_unsigned_to_nat(3u);
v___x_1331_ = l_Lean_Syntax_getArg(v_x_1315_, v___x_1330_);
lean_dec(v_x_1315_);
v___x_1332_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq___closed__1));
v___x_1333_ = l_Lean_Syntax_getArgs(v___x_1327_);
lean_dec(v___x_1327_);
v___x_1334_ = 0;
v___x_1335_ = l_Lean_SourceInfo_fromRef(v_ref_1323_, v___x_1334_);
v___x_1336_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1));
v___x_1337_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2));
lean_inc(v___x_1335_);
v___x_1338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1335_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_1335_);
v___x_1340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1335_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1));
v___x_1342_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3));
v___x_1343_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1344_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0));
v___x_1345_ = l_Lean_SourceInfo_fromRef(v_tk_1325_, v___x_1320_);
lean_dec(v_tk_1325_);
v___x_1346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___x_1318_);
v___x_1347_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1, &l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once, _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
v___x_1348_ = l_Array_append___redArg(v___x_1347_, v___x_1333_);
lean_dec_ref(v___x_1333_);
lean_inc(v___x_1335_);
v___x_1349_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1335_);
lean_ctor_set(v___x_1349_, 1, v___x_1343_);
lean_ctor_set(v___x_1349_, 2, v___x_1348_);
v___x_1350_ = l_Lean_SourceInfo_fromRef(v_arr_1329_, v___x_1320_);
lean_dec(v_arr_1329_);
v___x_1351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v___x_1339_);
v___x_1352_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__1));
v___x_1353_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__2));
lean_inc(v___x_1335_);
v___x_1354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1335_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3));
v___x_1356_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_paren___closed__1));
v___x_1357_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_occs___closed__4));
lean_inc(v___x_1335_);
v___x_1358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1335_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__13));
lean_inc(v___x_1335_);
v___x_1360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1335_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
lean_inc(v___x_1335_);
v___x_1361_ = l_Lean_Syntax_node3(v___x_1335_, v___x_1356_, v___x_1358_, v___x_1331_, v___x_1360_);
v___x_1362_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2));
lean_inc(v___x_1335_);
v___x_1363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1335_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_allGoals___closed__1));
v___x_1365_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1));
lean_inc(v___x_1335_);
v___x_1366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1335_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convRfl___closed__1));
v___x_1368_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convRfl___closed__2));
lean_inc(v___x_1335_);
v___x_1369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1335_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
lean_inc(v___x_1335_);
v___x_1370_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1367_, v___x_1369_);
lean_inc(v___x_1335_);
v___x_1371_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1343_, v___x_1370_);
lean_inc(v___x_1335_);
v___x_1372_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1355_, v___x_1371_);
lean_inc(v___x_1335_);
v___x_1373_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1332_, v___x_1372_);
lean_inc(v___x_1335_);
v___x_1374_ = l_Lean_Syntax_node2(v___x_1335_, v___x_1364_, v___x_1366_, v___x_1373_);
lean_inc(v___x_1335_);
v___x_1375_ = l_Lean_Syntax_node3(v___x_1335_, v___x_1343_, v___x_1361_, v___x_1363_, v___x_1374_);
lean_inc(v___x_1335_);
v___x_1376_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1355_, v___x_1375_);
lean_inc(v___x_1335_);
v___x_1377_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1332_, v___x_1376_);
lean_inc_ref(v___x_1340_);
lean_inc(v___x_1335_);
v___x_1378_ = l_Lean_Syntax_node3(v___x_1335_, v___x_1352_, v___x_1354_, v___x_1340_, v___x_1377_);
lean_inc(v___x_1335_);
v___x_1379_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1343_, v___x_1378_);
lean_inc(v___x_1335_);
v___x_1380_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1342_, v___x_1379_);
lean_inc(v___x_1335_);
v___x_1381_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1341_, v___x_1380_);
lean_inc(v___x_1335_);
v___x_1382_ = l_Lean_Syntax_node4(v___x_1335_, v___x_1344_, v___x_1346_, v___x_1349_, v___x_1351_, v___x_1381_);
lean_inc(v___x_1335_);
v___x_1383_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1343_, v___x_1382_);
lean_inc(v___x_1335_);
v___x_1384_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1342_, v___x_1383_);
lean_inc(v___x_1335_);
v___x_1385_ = l_Lean_Syntax_node1(v___x_1335_, v___x_1341_, v___x_1384_);
v___x_1386_ = l_Lean_Syntax_node3(v___x_1335_, v___x_1336_, v___x_1338_, v___x_1340_, v___x_1385_);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
lean_ctor_set(v___x_1387_, 1, v_a_1317_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___boxed(lean_object* v_x_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1(v_x_1388_, v_a_1389_, v_a_1390_);
lean_dec_ref(v_a_1389_);
return v_res_1391_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__4(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1403_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_case___closed__6, &l_Lean_Parser_Tactic_Conv_case___closed__6_once, _init_l_Lean_Parser_Tactic_Conv_case___closed__6);
v___x_1404_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case_x27___closed__3));
v___x_1405_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1406_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v___x_1404_);
lean_ctor_set(v___x_1406_, 2, v___x_1403_);
return v___x_1406_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__5(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1407_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5));
v___x_1408_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_case_x27___closed__4, &l_Lean_Parser_Tactic_Conv_case_x27___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__4);
v___x_1409_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1410_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v___x_1408_);
lean_ctor_set(v___x_1410_, 2, v___x_1407_);
return v___x_1410_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__6(void){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1411_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq));
v___x_1412_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_case_x27___closed__5, &l_Lean_Parser_Tactic_Conv_case_x27___closed__5_once, _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__5);
v___x_1413_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1414_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v___x_1412_);
lean_ctor_set(v___x_1414_, 2, v___x_1411_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__7(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1415_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_case_x27___closed__6, &l_Lean_Parser_Tactic_Conv_case_x27___closed__6_once, _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__6);
v___x_1416_ = lean_unsigned_to_nat(1022u);
v___x_1417_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case_x27___closed__1));
v___x_1418_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v___x_1416_);
lean_ctor_set(v___x_1418_, 2, v___x_1415_);
return v___x_1418_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_case_x27(void){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_case_x27___closed__7, &l_Lean_Parser_Tactic_Conv_case_x27___closed__7_once, _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__7);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1(lean_object* v_x_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case_x27___closed__0));
v___x_1429_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case_x27___closed__1));
lean_inc(v_x_1425_);
v___x_1430_ = l_Lean_Syntax_isOfKind(v_x_1425_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec(v_x_1425_);
v___x_1431_ = lean_box(1);
v___x_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_a_1427_);
return v___x_1432_;
}
else
{
lean_object* v_ref_1433_; lean_object* v___x_1434_; lean_object* v_tk_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v_arr_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_ref_1433_ = lean_ctor_get(v_a_1426_, 5);
v___x_1434_ = lean_unsigned_to_nat(0u);
v_tk_1435_ = l_Lean_Syntax_getArg(v_x_1425_, v___x_1434_);
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = l_Lean_Syntax_getArg(v_x_1425_, v___x_1436_);
v___x_1438_ = lean_unsigned_to_nat(2u);
v_arr_1439_ = l_Lean_Syntax_getArg(v_x_1425_, v___x_1438_);
v___x_1440_ = lean_unsigned_to_nat(3u);
v___x_1441_ = l_Lean_Syntax_getArg(v_x_1425_, v___x_1440_);
lean_dec(v_x_1425_);
v___x_1442_ = l_Lean_Syntax_getArgs(v___x_1437_);
lean_dec(v___x_1437_);
v___x_1443_ = 0;
v___x_1444_ = l_Lean_SourceInfo_fromRef(v_ref_1433_, v___x_1443_);
v___x_1445_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1));
v___x_1446_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2));
lean_inc(v___x_1444_);
v___x_1447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1444_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_1444_);
v___x_1449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1444_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1));
v___x_1451_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3));
v___x_1452_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1453_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0));
v___x_1454_ = l_Lean_SourceInfo_fromRef(v_tk_1435_, v___x_1430_);
lean_dec(v_tk_1435_);
v___x_1455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___x_1428_);
v___x_1456_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1, &l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once, _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
v___x_1457_ = l_Array_append___redArg(v___x_1456_, v___x_1442_);
lean_dec_ref(v___x_1442_);
lean_inc(v___x_1444_);
v___x_1458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1444_);
lean_ctor_set(v___x_1458_, 1, v___x_1452_);
lean_ctor_set(v___x_1458_, 2, v___x_1457_);
v___x_1459_ = l_Lean_SourceInfo_fromRef(v_arr_1439_, v___x_1430_);
lean_dec(v_arr_1439_);
v___x_1460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v___x_1448_);
v___x_1461_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__1));
v___x_1462_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__2));
lean_inc(v___x_1444_);
v___x_1463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1444_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
lean_inc_ref(v___x_1449_);
lean_inc(v___x_1444_);
v___x_1464_ = l_Lean_Syntax_node3(v___x_1444_, v___x_1461_, v___x_1463_, v___x_1449_, v___x_1441_);
lean_inc(v___x_1444_);
v___x_1465_ = l_Lean_Syntax_node1(v___x_1444_, v___x_1452_, v___x_1464_);
lean_inc(v___x_1444_);
v___x_1466_ = l_Lean_Syntax_node1(v___x_1444_, v___x_1451_, v___x_1465_);
lean_inc(v___x_1444_);
v___x_1467_ = l_Lean_Syntax_node1(v___x_1444_, v___x_1450_, v___x_1466_);
lean_inc(v___x_1444_);
v___x_1468_ = l_Lean_Syntax_node4(v___x_1444_, v___x_1453_, v___x_1455_, v___x_1458_, v___x_1460_, v___x_1467_);
lean_inc(v___x_1444_);
v___x_1469_ = l_Lean_Syntax_node1(v___x_1444_, v___x_1452_, v___x_1468_);
lean_inc(v___x_1444_);
v___x_1470_ = l_Lean_Syntax_node1(v___x_1444_, v___x_1451_, v___x_1469_);
lean_inc(v___x_1444_);
v___x_1471_ = l_Lean_Syntax_node1(v___x_1444_, v___x_1450_, v___x_1470_);
v___x_1472_ = l_Lean_Syntax_node3(v___x_1444_, v___x_1445_, v___x_1447_, v___x_1449_, v___x_1471_);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v_a_1427_);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___boxed(lean_object* v_x_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1(v_x_1474_, v_a_1475_, v_a_1476_);
lean_dec_ref(v_a_1475_);
return v_res_1477_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1489_ = l_Lean_binderIdent;
v___x_1490_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10));
v___x_1491_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1492_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___x_1490_);
lean_ctor_set(v___x_1492_, 2, v___x_1489_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4, &l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4_once, _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4);
v___x_1494_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_ext___closed__4));
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1493_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1496_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5, &l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5_once, _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5);
v___x_1497_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3));
v___x_1498_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1499_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v___x_1497_);
lean_ctor_set(v___x_1499_, 2, v___x_1496_);
return v___x_1499_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1500_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5));
v___x_1501_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6, &l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6_once, _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6);
v___x_1502_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1503_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
lean_ctor_set(v___x_1503_, 1, v___x_1501_);
lean_ctor_set(v___x_1503_, 2, v___x_1500_);
return v___x_1503_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1504_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq));
v___x_1505_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7, &l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7_once, _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7);
v___x_1506_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1507_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v___x_1505_);
lean_ctor_set(v___x_1507_, 2, v___x_1504_);
return v___x_1507_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1508_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8, &l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8_once, _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8);
v___x_1509_ = lean_unsigned_to_nat(1022u);
v___x_1510_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1));
v___x_1511_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v___x_1509_);
lean_ctor_set(v___x_1511_, 2, v___x_1508_);
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__(void){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9, &l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9_once, _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1(lean_object* v_x_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1));
lean_inc(v_x_1530_);
v___x_1534_ = l_Lean_Syntax_isOfKind(v_x_1530_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_x_1530_);
v___x_1535_ = lean_box(1);
v___x_1536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v_a_1532_);
return v___x_1536_;
}
else
{
lean_object* v_ref_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v_args_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_ref_1537_ = lean_ctor_get(v_a_1531_, 5);
v___x_1538_ = lean_unsigned_to_nat(1u);
v___x_1539_ = l_Lean_Syntax_getArg(v_x_1530_, v___x_1538_);
v___x_1540_ = lean_unsigned_to_nat(3u);
v___x_1541_ = l_Lean_Syntax_getArg(v_x_1530_, v___x_1540_);
lean_dec(v_x_1530_);
v___x_1542_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1));
v_args_1543_ = l_Lean_Syntax_getArgs(v___x_1539_);
lean_dec(v___x_1539_);
v___x_1544_ = 0;
v___x_1545_ = l_Lean_SourceInfo_fromRef(v_ref_1537_, v___x_1544_);
v___x_1546_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case___closed__0));
v___x_1547_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case___closed__1));
lean_inc(v___x_1545_);
v___x_1548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1545_);
lean_ctor_set(v___x_1548_, 1, v___x_1546_);
v___x_1549_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1550_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3));
v___x_1551_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5));
v___x_1552_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6));
lean_inc(v___x_1545_);
v___x_1553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1545_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
lean_inc(v___x_1545_);
v___x_1554_ = l_Lean_Syntax_node1(v___x_1545_, v___x_1551_, v___x_1553_);
lean_inc(v___x_1545_);
v___x_1555_ = l_Lean_Syntax_node1(v___x_1545_, v___x_1542_, v___x_1554_);
v___x_1556_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1, &l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once, _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
v___x_1557_ = l_Array_append___redArg(v___x_1556_, v_args_1543_);
lean_dec_ref(v_args_1543_);
lean_inc(v___x_1545_);
v___x_1558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1545_);
lean_ctor_set(v___x_1558_, 1, v___x_1549_);
lean_ctor_set(v___x_1558_, 2, v___x_1557_);
lean_inc(v___x_1545_);
v___x_1559_ = l_Lean_Syntax_node2(v___x_1545_, v___x_1550_, v___x_1555_, v___x_1558_);
lean_inc(v___x_1545_);
v___x_1560_ = l_Lean_Syntax_node1(v___x_1545_, v___x_1549_, v___x_1559_);
v___x_1561_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_1545_);
v___x_1562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1545_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_Syntax_node4(v___x_1545_, v___x_1547_, v___x_1548_, v___x_1560_, v___x_1562_, v___x_1541_);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v_a_1532_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___boxed(lean_object* v_x_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1(v_x_1565_, v_a_1566_, v_a_1567_);
lean_dec_ref(v_a_1566_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1(lean_object* v_x_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1597_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_focus___closed__0));
v___x_1598_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_focus___closed__1));
lean_inc(v_x_1594_);
v___x_1599_ = l_Lean_Syntax_isOfKind(v_x_1594_, v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v_x_1594_);
v___x_1600_ = lean_box(1);
v___x_1601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v_a_1596_);
return v___x_1601_;
}
else
{
lean_object* v_ref_1602_; lean_object* v___x_1603_; lean_object* v_tk_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_ref_1602_ = lean_ctor_get(v_a_1595_, 5);
v___x_1603_ = lean_unsigned_to_nat(0u);
v_tk_1604_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1603_);
v___x_1605_ = lean_unsigned_to_nat(1u);
v___x_1606_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1605_);
lean_dec(v_x_1594_);
v___x_1607_ = 0;
v___x_1608_ = l_Lean_SourceInfo_fromRef(v_ref_1602_, v___x_1607_);
v___x_1609_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1));
v___x_1610_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2));
lean_inc(v___x_1608_);
v___x_1611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1608_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_1608_);
v___x_1613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1608_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1));
v___x_1615_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3));
v___x_1616_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1617_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0));
v___x_1618_ = l_Lean_SourceInfo_fromRef(v_tk_1604_, v___x_1599_);
lean_dec(v_tk_1604_);
v___x_1619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v___x_1597_);
v___x_1620_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__1));
v___x_1621_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__2));
lean_inc(v___x_1608_);
v___x_1622_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1608_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
lean_inc_ref(v___x_1613_);
lean_inc(v___x_1608_);
v___x_1623_ = l_Lean_Syntax_node3(v___x_1608_, v___x_1620_, v___x_1622_, v___x_1613_, v___x_1606_);
lean_inc(v___x_1608_);
v___x_1624_ = l_Lean_Syntax_node1(v___x_1608_, v___x_1616_, v___x_1623_);
lean_inc(v___x_1608_);
v___x_1625_ = l_Lean_Syntax_node1(v___x_1608_, v___x_1615_, v___x_1624_);
lean_inc(v___x_1608_);
v___x_1626_ = l_Lean_Syntax_node1(v___x_1608_, v___x_1614_, v___x_1625_);
lean_inc(v___x_1608_);
v___x_1627_ = l_Lean_Syntax_node2(v___x_1608_, v___x_1617_, v___x_1619_, v___x_1626_);
lean_inc(v___x_1608_);
v___x_1628_ = l_Lean_Syntax_node1(v___x_1608_, v___x_1616_, v___x_1627_);
lean_inc(v___x_1608_);
v___x_1629_ = l_Lean_Syntax_node1(v___x_1608_, v___x_1615_, v___x_1628_);
lean_inc(v___x_1608_);
v___x_1630_ = l_Lean_Syntax_node1(v___x_1608_, v___x_1614_, v___x_1629_);
v___x_1631_ = l_Lean_Syntax_node3(v___x_1608_, v___x_1609_, v___x_1611_, v___x_1613_, v___x_1630_);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v_a_1596_);
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___boxed(lean_object* v_x_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1(v_x_1633_, v_a_1634_, v_a_1635_);
lean_dec_ref(v_a_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv_xb7____1(lean_object* v_x_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1));
lean_inc(v_x_1682_);
v___x_1686_ = l_Lean_Syntax_isOfKind(v_x_1682_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v_x_1682_);
v___x_1687_ = lean_box(1);
v___x_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v_a_1684_);
return v___x_1688_;
}
else
{
lean_object* v_ref_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_ref_1689_ = lean_ctor_get(v_a_1683_, 5);
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = l_Lean_Syntax_getArg(v_x_1682_, v___x_1690_);
v___x_1692_ = lean_unsigned_to_nat(1u);
v___x_1693_ = l_Lean_Syntax_getArg(v_x_1682_, v___x_1692_);
lean_dec(v_x_1682_);
v___x_1694_ = 0;
v___x_1695_ = l_Lean_SourceInfo_fromRef(v_ref_1689_, v___x_1694_);
v___x_1696_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1));
v___x_1697_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1));
v___x_1698_ = l_Lean_SourceInfo_fromRef(v___x_1691_, v___x_1686_);
lean_dec(v___x_1691_);
v___x_1699_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2));
v___x_1700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1702_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_paren___closed__1));
v___x_1703_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_occs___closed__4));
lean_inc(v___x_1695_);
v___x_1704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1695_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v___x_1705_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__13));
lean_inc(v___x_1695_);
v___x_1706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1695_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
lean_inc(v___x_1695_);
v___x_1707_ = l_Lean_Syntax_node3(v___x_1695_, v___x_1702_, v___x_1704_, v___x_1693_, v___x_1706_);
lean_inc(v___x_1695_);
v___x_1708_ = l_Lean_Syntax_node1(v___x_1695_, v___x_1701_, v___x_1707_);
v___x_1709_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11));
lean_inc(v___x_1695_);
v___x_1710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1695_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
lean_inc(v___x_1695_);
v___x_1711_ = l_Lean_Syntax_node3(v___x_1695_, v___x_1697_, v___x_1700_, v___x_1708_, v___x_1710_);
v___x_1712_ = l_Lean_Syntax_node1(v___x_1695_, v___x_1696_, v___x_1711_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v_a_1684_);
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv_xb7____1___boxed(lean_object* v_x_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv_xb7____1(v_x_1714_, v_a_1715_, v_a_1716_);
lean_dec_ref(v_a_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1(lean_object* v_x_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1));
lean_inc(v_x_1744_);
v___x_1748_ = l_Lean_Syntax_isOfKind(v_x_1744_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec(v_x_1744_);
v___x_1749_ = lean_box(1);
v___x_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v_a_1746_);
return v___x_1750_;
}
else
{
lean_object* v_ref_1751_; lean_object* v___x_1752_; lean_object* v_tk_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_ref_1751_ = lean_ctor_get(v_a_1745_, 5);
v___x_1752_ = lean_unsigned_to_nat(0u);
v_tk_1753_ = l_Lean_Syntax_getArg(v_x_1744_, v___x_1752_);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = l_Lean_Syntax_getArg(v_x_1744_, v___x_1754_);
lean_dec(v_x_1744_);
v___x_1756_ = 0;
v___x_1757_ = l_Lean_SourceInfo_fromRef(v_ref_1751_, v___x_1756_);
v___x_1758_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1));
v___x_1759_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2));
lean_inc(v___x_1757_);
v___x_1760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1757_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_1757_);
v___x_1762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1757_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1));
v___x_1764_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3));
v___x_1765_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1766_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0));
v___x_1767_ = l_Lean_SourceInfo_fromRef(v_tk_1753_, v___x_1748_);
lean_dec(v_tk_1753_);
v___x_1768_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1));
v___x_1769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__1));
v___x_1771_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__2));
lean_inc(v___x_1757_);
v___x_1772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1757_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
lean_inc_ref(v___x_1762_);
lean_inc(v___x_1757_);
v___x_1773_ = l_Lean_Syntax_node3(v___x_1757_, v___x_1770_, v___x_1772_, v___x_1762_, v___x_1755_);
lean_inc(v___x_1757_);
v___x_1774_ = l_Lean_Syntax_node1(v___x_1757_, v___x_1765_, v___x_1773_);
lean_inc(v___x_1757_);
v___x_1775_ = l_Lean_Syntax_node1(v___x_1757_, v___x_1764_, v___x_1774_);
lean_inc(v___x_1757_);
v___x_1776_ = l_Lean_Syntax_node1(v___x_1757_, v___x_1763_, v___x_1775_);
lean_inc(v___x_1757_);
v___x_1777_ = l_Lean_Syntax_node2(v___x_1757_, v___x_1766_, v___x_1769_, v___x_1776_);
lean_inc(v___x_1757_);
v___x_1778_ = l_Lean_Syntax_node1(v___x_1757_, v___x_1765_, v___x_1777_);
lean_inc(v___x_1757_);
v___x_1779_ = l_Lean_Syntax_node1(v___x_1757_, v___x_1764_, v___x_1778_);
lean_inc(v___x_1757_);
v___x_1780_ = l_Lean_Syntax_node1(v___x_1757_, v___x_1763_, v___x_1779_);
v___x_1781_ = l_Lean_Syntax_node3(v___x_1757_, v___x_1758_, v___x_1760_, v___x_1762_, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v_a_1746_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___boxed(lean_object* v_x_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1(v_x_1783_, v_a_1784_, v_a_1785_);
lean_dec_ref(v_a_1784_);
return v_res_1786_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1798_ = l_Lean_Parser_Tactic_optConfig;
v___x_1799_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3));
v___x_1800_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1801_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___x_1799_);
lean_ctor_set(v___x_1801_, 2, v___x_1798_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = l_Lean_Parser_Tactic_rwRuleSeq;
v___x_1803_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4, &l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4_once, _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4);
v___x_1804_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1805_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v___x_1803_);
lean_ctor_set(v___x_1805_, 2, v___x_1802_);
return v___x_1805_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1806_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5, &l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5_once, _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5);
v___x_1807_ = lean_unsigned_to_nat(1022u);
v___x_1808_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1));
v___x_1809_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v___x_1807_);
lean_ctor_set(v___x_1809_, 2, v___x_1806_);
return v___x_1809_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convRw____(void){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6, &l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6_once, _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRw______1(lean_object* v_x_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1));
lean_inc(v_x_1811_);
v___x_1815_ = l_Lean_Syntax_isOfKind(v_x_1811_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec(v_x_1811_);
v___x_1816_ = lean_box(1);
v___x_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v_a_1813_);
return v___x_1817_;
}
else
{
lean_object* v_ref_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_ref_1818_ = lean_ctor_get(v_a_1812_, 5);
v___x_1819_ = lean_unsigned_to_nat(1u);
v___x_1820_ = l_Lean_Syntax_getArg(v_x_1811_, v___x_1819_);
v___x_1821_ = lean_unsigned_to_nat(2u);
v___x_1822_ = l_Lean_Syntax_getArg(v_x_1811_, v___x_1821_);
lean_dec(v_x_1811_);
v___x_1823_ = 0;
v___x_1824_ = l_Lean_SourceInfo_fromRef(v_ref_1818_, v___x_1823_);
v___x_1825_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_rewrite___closed__0));
v___x_1826_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_rewrite___closed__1));
lean_inc(v___x_1824_);
v___x_1827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1824_);
lean_ctor_set(v___x_1827_, 1, v___x_1825_);
v___x_1828_ = l_Lean_Syntax_node3(v___x_1824_, v___x_1826_, v___x_1827_, v___x_1820_, v___x_1822_);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v_a_1813_);
return v___x_1829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRw______1___boxed(lean_object* v_x_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRw______1(v_x_1830_, v_a_1831_, v_a_1832_);
lean_dec_ref(v_a_1831_);
return v_res_1833_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1845_ = l_Lean_Parser_Tactic_optConfig;
v___x_1846_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3));
v___x_1847_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1848_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v___x_1846_);
lean_ctor_set(v___x_1848_, 2, v___x_1845_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1849_ = l_Lean_Parser_Tactic_rwRuleSeq;
v___x_1850_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4, &l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4_once, _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4);
v___x_1851_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_1852_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v___x_1850_);
lean_ctor_set(v___x_1852_, 2, v___x_1849_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1853_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5, &l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5_once, _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5);
v___x_1854_ = lean_unsigned_to_nat(1022u);
v___x_1855_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1));
v___x_1856_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v___x_1854_);
lean_ctor_set(v___x_1856_, 2, v___x_1853_);
return v___x_1856_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convErw____(void){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6, &l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6_once, _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0(size_t v_sz_1858_, size_t v_i_1859_, lean_object* v_bs_1860_){
_start:
{
uint8_t v___x_1861_; 
v___x_1861_ = lean_usize_dec_lt(v_i_1859_, v_sz_1858_);
if (v___x_1861_ == 0)
{
return v_bs_1860_;
}
else
{
lean_object* v_v_1862_; lean_object* v___x_1863_; lean_object* v_bs_x27_1864_; size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v_v_1862_ = lean_array_uget(v_bs_1860_, v_i_1859_);
v___x_1863_ = lean_unsigned_to_nat(0u);
v_bs_x27_1864_ = lean_array_uset(v_bs_1860_, v_i_1859_, v___x_1863_);
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_add(v_i_1859_, v___x_1865_);
v___x_1867_ = lean_array_uset(v_bs_x27_1864_, v_i_1859_, v_v_1862_);
v_i_1859_ = v___x_1866_;
v_bs_1860_ = v___x_1867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0___boxed(lean_object* v_sz_1869_, lean_object* v_i_1870_, lean_object* v_bs_1871_){
_start:
{
size_t v_sz_boxed_1872_; size_t v_i_boxed_1873_; lean_object* v_res_1874_; 
v_sz_boxed_1872_ = lean_unbox_usize(v_sz_1869_);
lean_dec(v_sz_1869_);
v_i_boxed_1873_ = lean_unbox_usize(v_i_1870_);
lean_dec(v_i_1870_);
v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0(v_sz_boxed_1872_, v_i_boxed_1873_, v_bs_1871_);
return v_res_1874_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6));
v___x_1895_ = l_String_toRawSubstring_x27(v___x_1894_);
return v___x_1895_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13));
v___x_1908_ = l_String_toRawSubstring_x27(v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1(lean_object* v_x_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1));
lean_inc(v_x_1926_);
v___x_1930_ = l_Lean_Syntax_isOfKind(v_x_1926_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec_ref(v_a_1927_);
lean_dec(v_x_1926_);
v___x_1931_ = lean_box(1);
v___x_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v_a_1928_);
return v___x_1932_;
}
else
{
lean_object* v_quotContext_1933_; lean_object* v_currMacroScope_1934_; lean_object* v_ref_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; size_t v_sz_1949_; size_t v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_quotContext_1933_ = lean_ctor_get(v_a_1927_, 1);
lean_inc(v_quotContext_1933_);
v_currMacroScope_1934_ = lean_ctor_get(v_a_1927_, 2);
lean_inc(v_currMacroScope_1934_);
v_ref_1935_ = lean_ctor_get(v_a_1927_, 5);
lean_inc(v_ref_1935_);
lean_dec_ref(v_a_1927_);
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = l_Lean_Syntax_getArg(v_x_1926_, v___x_1936_);
v___x_1938_ = lean_unsigned_to_nat(2u);
v___x_1939_ = l_Lean_Syntax_getArg(v_x_1926_, v___x_1938_);
lean_dec(v_x_1926_);
v___x_1940_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1));
v___x_1941_ = 0;
v___x_1942_ = l_Lean_SourceInfo_fromRef(v_ref_1935_, v___x_1941_);
lean_dec(v_ref_1935_);
v___x_1943_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1));
v___x_1944_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2));
lean_inc(v___x_1942_);
v___x_1945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1942_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_1947_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1, &l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once, _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
v___x_1948_ = l_Lean_Parser_Tactic_getConfigItems(v___x_1937_);
v_sz_1949_ = lean_array_size(v___x_1948_);
v___x_1950_ = ((size_t)0ULL);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0(v_sz_1949_, v___x_1950_, v___x_1948_);
v___x_1952_ = l_Array_append___redArg(v___x_1947_, v___x_1951_);
lean_dec_ref(v___x_1951_);
v___x_1953_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3));
v___x_1954_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5));
v___x_1955_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_occs___closed__4));
lean_inc(v___x_1942_);
v___x_1956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1942_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7, &l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7_once, _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7);
v___x_1958_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8));
lean_inc(v_currMacroScope_1934_);
lean_inc(v_quotContext_1933_);
v___x_1959_ = l_Lean_addMacroScope(v_quotContext_1933_, v___x_1958_, v_currMacroScope_1934_);
v___x_1960_ = lean_box(0);
lean_inc(v___x_1942_);
v___x_1961_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1942_);
lean_ctor_set(v___x_1961_, 1, v___x_1957_);
lean_ctor_set(v___x_1961_, 2, v___x_1959_);
lean_ctor_set(v___x_1961_, 3, v___x_1960_);
v___x_1962_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9));
lean_inc(v___x_1942_);
v___x_1963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1942_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11));
v___x_1965_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12));
lean_inc(v___x_1942_);
v___x_1966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1942_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14, &l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14_once, _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14);
v___x_1968_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15));
v___x_1969_ = l_Lean_addMacroScope(v_quotContext_1933_, v___x_1968_, v_currMacroScope_1934_);
v___x_1970_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21));
lean_inc(v___x_1942_);
v___x_1971_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1942_);
lean_ctor_set(v___x_1971_, 1, v___x_1967_);
lean_ctor_set(v___x_1971_, 2, v___x_1969_);
lean_ctor_set(v___x_1971_, 3, v___x_1970_);
lean_inc(v___x_1942_);
v___x_1972_ = l_Lean_Syntax_node2(v___x_1942_, v___x_1964_, v___x_1966_, v___x_1971_);
v___x_1973_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__13));
lean_inc(v___x_1942_);
v___x_1974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1942_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
lean_inc(v___x_1942_);
v___x_1975_ = l_Lean_Syntax_node5(v___x_1942_, v___x_1954_, v___x_1956_, v___x_1961_, v___x_1963_, v___x_1972_, v___x_1974_);
lean_inc(v___x_1942_);
v___x_1976_ = l_Lean_Syntax_node1(v___x_1942_, v___x_1953_, v___x_1975_);
v___x_1977_ = lean_array_push(v___x_1952_, v___x_1976_);
lean_inc(v___x_1942_);
v___x_1978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1942_);
lean_ctor_set(v___x_1978_, 1, v___x_1946_);
lean_ctor_set(v___x_1978_, 2, v___x_1977_);
lean_inc(v___x_1942_);
v___x_1979_ = l_Lean_Syntax_node1(v___x_1942_, v___x_1940_, v___x_1978_);
v___x_1980_ = l_Lean_Syntax_node3(v___x_1942_, v___x_1943_, v___x_1945_, v___x_1979_, v___x_1939_);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v_a_1928_);
return v___x_1981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convArgs__1(lean_object* v_x_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convArgs___closed__1));
v___x_2002_ = l_Lean_Syntax_isOfKind(v_x_1998_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_box(1);
v___x_2004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v_a_2000_);
return v___x_2004_;
}
else
{
lean_object* v_ref_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_ref_2005_ = lean_ctor_get(v_a_1999_, 5);
v___x_2006_ = 0;
v___x_2007_ = l_Lean_SourceInfo_fromRef(v_ref_2005_, v___x_2006_);
v___x_2008_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_congr___closed__0));
v___x_2009_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_congr___closed__1));
lean_inc(v___x_2007_);
v___x_2010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2007_);
lean_ctor_set(v___x_2010_, 1, v___x_2008_);
v___x_2011_ = l_Lean_Syntax_node1(v___x_2007_, v___x_2009_, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
lean_ctor_set(v___x_2012_, 1, v_a_2000_);
return v___x_2012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convArgs__1___boxed(lean_object* v_x_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convArgs__1(v_x_2013_, v_a_2014_, v_a_2015_);
lean_dec_ref(v_a_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convLeft__1(lean_object* v_x_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convLeft___closed__1));
v___x_2037_ = l_Lean_Syntax_isOfKind(v_x_2033_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_box(1);
v___x_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
lean_ctor_set(v___x_2039_, 1, v_a_2035_);
return v___x_2039_;
}
else
{
lean_object* v_ref_2040_; uint8_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_ref_2040_ = lean_ctor_get(v_a_2034_, 5);
v___x_2041_ = 0;
v___x_2042_ = l_Lean_SourceInfo_fromRef(v_ref_2040_, v___x_2041_);
v___x_2043_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_lhs___closed__0));
v___x_2044_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_lhs___closed__1));
lean_inc(v___x_2042_);
v___x_2045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2042_);
lean_ctor_set(v___x_2045_, 1, v___x_2043_);
v___x_2046_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2044_, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set(v___x_2047_, 1, v_a_2035_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convLeft__1___boxed(lean_object* v_x_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convLeft__1(v_x_2048_, v_a_2049_, v_a_2050_);
lean_dec_ref(v_a_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRight__1(lean_object* v_x_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convRight___closed__1));
v___x_2072_ = l_Lean_Syntax_isOfKind(v_x_2068_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_box(1);
v___x_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_ctor_set(v___x_2074_, 1, v_a_2070_);
return v___x_2074_;
}
else
{
lean_object* v_ref_2075_; uint8_t v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_ref_2075_ = lean_ctor_get(v_a_2069_, 5);
v___x_2076_ = 0;
v___x_2077_ = l_Lean_SourceInfo_fromRef(v_ref_2075_, v___x_2076_);
v___x_2078_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_rhs___closed__0));
v___x_2079_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_rhs___closed__1));
lean_inc(v___x_2077_);
v___x_2080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2077_);
lean_ctor_set(v___x_2080_, 1, v___x_2078_);
v___x_2081_ = l_Lean_Syntax_node1(v___x_2077_, v___x_2079_, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v_a_2070_);
return v___x_2082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRight__1___boxed(lean_object* v_x_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRight__1(v_x_2083_, v_a_2084_, v_a_2085_);
lean_dec_ref(v_a_2084_);
return v_res_2086_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2098_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_ext___closed__10, &l_Lean_Parser_Tactic_Conv_ext___closed__10_once, _init_l_Lean_Parser_Tactic_Conv_ext___closed__10);
v___x_2099_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3));
v___x_2100_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_2101_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2099_);
lean_ctor_set(v___x_2101_, 2, v___x_2098_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2102_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4, &l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4_once, _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4);
v___x_2103_ = lean_unsigned_to_nat(1022u);
v___x_2104_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1));
v___x_2105_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___x_2103_);
lean_ctor_set(v___x_2105_, 2, v___x_2102_);
return v___x_2105_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_convIntro______(void){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5, &l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5_once, _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convIntro________1(lean_object* v_x_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1));
lean_inc(v_x_2107_);
v___x_2111_ = l_Lean_Syntax_isOfKind(v_x_2107_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v_x_2107_);
v___x_2112_ = lean_box(1);
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v_a_2109_);
return v___x_2113_;
}
else
{
lean_object* v_ref_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v_xs_2117_; uint8_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_ref_2114_ = lean_ctor_get(v_a_2108_, 5);
v___x_2115_ = lean_unsigned_to_nat(1u);
v___x_2116_ = l_Lean_Syntax_getArg(v_x_2107_, v___x_2115_);
lean_dec(v_x_2107_);
v_xs_2117_ = l_Lean_Syntax_getArgs(v___x_2116_);
lean_dec(v___x_2116_);
v___x_2118_ = 0;
v___x_2119_ = l_Lean_SourceInfo_fromRef(v_ref_2114_, v___x_2118_);
v___x_2120_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_ext___closed__0));
v___x_2121_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_ext___closed__1));
lean_inc(v___x_2119_);
v___x_2122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2119_);
lean_ctor_set(v___x_2122_, 1, v___x_2120_);
v___x_2123_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_2124_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1, &l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once, _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
v___x_2125_ = l_Array_append___redArg(v___x_2124_, v_xs_2117_);
lean_dec_ref(v_xs_2117_);
lean_inc(v___x_2119_);
v___x_2126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2119_);
lean_ctor_set(v___x_2126_, 1, v___x_2123_);
lean_ctor_set(v___x_2126_, 2, v___x_2125_);
v___x_2127_ = l_Lean_Syntax_node2(v___x_2119_, v___x_2121_, v___x_2122_, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v_a_2109_);
return v___x_2128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convIntro________1___boxed(lean_object* v_x_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convIntro________1(v_x_2129_, v_a_2130_, v_a_2131_);
lean_dec_ref(v_a_2130_);
return v_res_2132_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__3(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2167_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_enterArg___closed__2));
v___x_2168_ = l_Lean_binderIdent;
v___x_2169_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq___closed__3));
v___x_2170_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v___x_2168_);
lean_ctor_set(v___x_2170_, 2, v___x_2167_);
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__4(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2171_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_enterArg___closed__3, &l_Lean_Parser_Tactic_Conv_enterArg___closed__3_once, _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__3);
v___x_2172_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_enterArg___closed__1));
v___x_2173_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_enterArg___closed__0));
v___x_2174_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v___x_2172_);
lean_ctor_set(v___x_2174_, 2, v___x_2171_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_enterArg(void){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_enterArg___closed__4, &l_Lean_Parser_Tactic_Conv_enterArg___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__4);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_enter___closed__4(void){
_start:
{
uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2190_ = 0;
v___x_2191_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__16));
v___x_2192_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__14));
v___x_2193_ = l_Lean_Parser_Tactic_Conv_enterArg;
v___x_2194_ = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v___x_2192_);
lean_ctor_set(v___x_2194_, 2, v___x_2191_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*3, v___x_2190_);
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_enter___closed__5(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_enter___closed__4, &l_Lean_Parser_Tactic_Conv_enter___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_enter___closed__4);
v___x_2196_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5));
v___x_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
lean_ctor_set(v___x_2197_, 1, v___x_2195_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_enter___closed__6(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_enter___closed__5, &l_Lean_Parser_Tactic_Conv_enter___closed__5_once, _init_l_Lean_Parser_Tactic_Conv_enter___closed__5);
v___x_2199_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_enter___closed__3));
v___x_2200_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_2201_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v___x_2199_);
lean_ctor_set(v___x_2201_, 2, v___x_2198_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_enter___closed__7(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_simp___closed__21));
v___x_2203_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_enter___closed__6, &l_Lean_Parser_Tactic_Conv_enter___closed__6_once, _init_l_Lean_Parser_Tactic_Conv_enter___closed__6);
v___x_2204_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_2205_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v___x_2203_);
lean_ctor_set(v___x_2205_, 2, v___x_2202_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_enter___closed__8(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_enter___closed__7, &l_Lean_Parser_Tactic_Conv_enter___closed__7_once, _init_l_Lean_Parser_Tactic_Conv_enter___closed__7);
v___x_2207_ = lean_unsigned_to_nat(1024u);
v___x_2208_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_enter___closed__1));
v___x_2209_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2207_);
lean_ctor_set(v___x_2209_, 2, v___x_2206_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_enter(void){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_enter___closed__8, &l_Lean_Parser_Tactic_Conv_enter___closed__8_once, _init_l_Lean_Parser_Tactic_Conv_enter___closed__8);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1(lean_object* v_x_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1));
lean_inc(v_x_2237_);
v___x_2241_ = l_Lean_Syntax_isOfKind(v_x_2237_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_dec(v_x_2237_);
v___x_2242_ = lean_box(1);
v___x_2243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v_a_2239_);
return v___x_2243_;
}
else
{
lean_object* v_ref_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_ref_2244_ = lean_ctor_get(v_a_2238_, 5);
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = l_Lean_Syntax_getArg(v_x_2237_, v___x_2245_);
lean_dec(v_x_2237_);
v___x_2247_ = 0;
v___x_2248_ = l_Lean_SourceInfo_fromRef(v_ref_2244_, v___x_2247_);
v___x_2249_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1));
v___x_2250_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2));
lean_inc(v___x_2248_);
v___x_2251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2248_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_2248_);
v___x_2253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2248_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1));
v___x_2255_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3));
v___x_2256_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_2257_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0));
v___x_2258_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1));
lean_inc(v___x_2248_);
v___x_2259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2248_);
lean_ctor_set(v___x_2259_, 1, v___x_2257_);
lean_inc(v___x_2248_);
v___x_2260_ = l_Lean_Syntax_node2(v___x_2248_, v___x_2258_, v___x_2259_, v___x_2246_);
lean_inc(v___x_2248_);
v___x_2261_ = l_Lean_Syntax_node1(v___x_2248_, v___x_2256_, v___x_2260_);
lean_inc(v___x_2248_);
v___x_2262_ = l_Lean_Syntax_node1(v___x_2248_, v___x_2255_, v___x_2261_);
lean_inc(v___x_2248_);
v___x_2263_ = l_Lean_Syntax_node1(v___x_2248_, v___x_2254_, v___x_2262_);
v___x_2264_ = l_Lean_Syntax_node3(v___x_2248_, v___x_2249_, v___x_2251_, v___x_2253_, v___x_2263_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v_a_2239_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___boxed(lean_object* v_x_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1(v_x_2266_, v_a_2267_, v_a_2268_);
lean_dec_ref(v_a_2267_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTry____1(lean_object* v_x_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1));
lean_inc(v_x_2356_);
v___x_2360_ = l_Lean_Syntax_isOfKind(v_x_2356_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec(v_x_2356_);
v___x_2361_ = lean_box(1);
v___x_2362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
lean_ctor_set(v___x_2362_, 1, v_a_2358_);
return v___x_2362_;
}
else
{
lean_object* v_ref_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_ref_2363_ = lean_ctor_get(v_a_2357_, 5);
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = l_Lean_Syntax_getArg(v_x_2356_, v___x_2364_);
lean_dec(v_x_2356_);
v___x_2366_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq___closed__1));
v___x_2367_ = 0;
v___x_2368_ = l_Lean_SourceInfo_fromRef(v_ref_2363_, v___x_2367_);
v___x_2369_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_first___closed__0));
v___x_2370_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_first___closed__1));
lean_inc(v___x_2368_);
v___x_2371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2368_);
lean_ctor_set(v___x_2371_, 1, v___x_2369_);
v___x_2372_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_2373_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_first___closed__7));
v___x_2374_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case___closed__4));
lean_inc(v___x_2368_);
v___x_2375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2368_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
lean_inc_ref(v___x_2375_);
lean_inc(v___x_2368_);
v___x_2376_ = l_Lean_Syntax_node2(v___x_2368_, v___x_2373_, v___x_2375_, v___x_2365_);
v___x_2377_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3));
v___x_2378_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_skip___closed__0));
v___x_2379_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_skip___closed__1));
lean_inc(v___x_2368_);
v___x_2380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2368_);
lean_ctor_set(v___x_2380_, 1, v___x_2378_);
lean_inc(v___x_2368_);
v___x_2381_ = l_Lean_Syntax_node1(v___x_2368_, v___x_2379_, v___x_2380_);
lean_inc(v___x_2368_);
v___x_2382_ = l_Lean_Syntax_node1(v___x_2368_, v___x_2372_, v___x_2381_);
lean_inc(v___x_2368_);
v___x_2383_ = l_Lean_Syntax_node1(v___x_2368_, v___x_2377_, v___x_2382_);
lean_inc(v___x_2368_);
v___x_2384_ = l_Lean_Syntax_node1(v___x_2368_, v___x_2366_, v___x_2383_);
lean_inc(v___x_2368_);
v___x_2385_ = l_Lean_Syntax_node2(v___x_2368_, v___x_2373_, v___x_2375_, v___x_2384_);
lean_inc(v___x_2368_);
v___x_2386_ = l_Lean_Syntax_node2(v___x_2368_, v___x_2372_, v___x_2376_, v___x_2385_);
v___x_2387_ = l_Lean_Syntax_node2(v___x_2368_, v___x_2370_, v___x_2371_, v___x_2386_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
lean_ctor_set(v___x_2388_, 1, v_a_2358_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTry____1___boxed(lean_object* v_x_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTry____1(v_x_2389_, v_a_2390_, v_a_2391_);
lean_dec_ref(v_a_2390_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1(lean_object* v_x_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2428_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1));
lean_inc(v_x_2425_);
v___x_2429_ = l_Lean_Syntax_isOfKind(v_x_2425_, v___x_2428_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_dec(v_x_2425_);
v___x_2430_ = lean_box(1);
v___x_2431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
lean_ctor_set(v___x_2431_, 1, v_a_2427_);
return v___x_2431_;
}
else
{
lean_object* v_ref_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v_tk_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_ref_2432_ = lean_ctor_get(v_a_2426_, 5);
v___x_2433_ = lean_unsigned_to_nat(0u);
v___x_2434_ = l_Lean_Syntax_getArg(v_x_2425_, v___x_2433_);
v___x_2435_ = lean_unsigned_to_nat(1u);
v_tk_2436_ = l_Lean_Syntax_getArg(v_x_2425_, v___x_2435_);
v___x_2437_ = lean_unsigned_to_nat(2u);
v___x_2438_ = l_Lean_Syntax_getArg(v_x_2425_, v___x_2437_);
lean_dec(v_x_2425_);
v___x_2439_ = 0;
v___x_2440_ = l_Lean_SourceInfo_fromRef(v_ref_2432_, v___x_2439_);
v___x_2441_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1));
v___x_2442_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2));
lean_inc(v___x_2440_);
v___x_2443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2440_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0));
lean_inc(v___x_2440_);
v___x_2445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2440_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1));
v___x_2447_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3));
v___x_2448_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_2449_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1));
v___x_2450_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2));
v___x_2451_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_occs___closed__4));
lean_inc(v___x_2440_);
v___x_2452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2440_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__1));
v___x_2454_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convTactic___closed__2));
lean_inc(v___x_2440_);
v___x_2455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2440_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq___closed__1));
v___x_2457_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3));
lean_inc(v___x_2440_);
v___x_2458_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2448_, v___x_2434_);
lean_inc(v___x_2440_);
v___x_2459_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2457_, v___x_2458_);
lean_inc(v___x_2440_);
v___x_2460_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2456_, v___x_2459_);
lean_inc_ref(v___x_2445_);
lean_inc_ref(v___x_2455_);
lean_inc(v___x_2440_);
v___x_2461_ = l_Lean_Syntax_node3(v___x_2440_, v___x_2453_, v___x_2455_, v___x_2445_, v___x_2460_);
lean_inc(v___x_2440_);
v___x_2462_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2448_, v___x_2461_);
lean_inc(v___x_2440_);
v___x_2463_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2447_, v___x_2462_);
lean_inc(v___x_2440_);
v___x_2464_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2446_, v___x_2463_);
v___x_2465_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__13));
lean_inc(v___x_2440_);
v___x_2466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2440_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
lean_inc_ref(v___x_2466_);
lean_inc_ref(v___x_2452_);
lean_inc(v___x_2440_);
v___x_2467_ = l_Lean_Syntax_node3(v___x_2440_, v___x_2450_, v___x_2452_, v___x_2464_, v___x_2466_);
v___x_2468_ = l_Lean_SourceInfo_fromRef(v_tk_2436_, v___x_2429_);
lean_dec(v_tk_2436_);
v___x_2469_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3));
v___x_2470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2468_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
lean_inc(v___x_2440_);
v___x_2471_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2448_, v___x_2438_);
lean_inc(v___x_2440_);
v___x_2472_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2457_, v___x_2471_);
lean_inc(v___x_2440_);
v___x_2473_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2456_, v___x_2472_);
lean_inc_ref(v___x_2445_);
lean_inc(v___x_2440_);
v___x_2474_ = l_Lean_Syntax_node3(v___x_2440_, v___x_2453_, v___x_2455_, v___x_2445_, v___x_2473_);
lean_inc(v___x_2440_);
v___x_2475_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2448_, v___x_2474_);
lean_inc(v___x_2440_);
v___x_2476_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2447_, v___x_2475_);
lean_inc(v___x_2440_);
v___x_2477_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2446_, v___x_2476_);
lean_inc(v___x_2440_);
v___x_2478_ = l_Lean_Syntax_node3(v___x_2440_, v___x_2450_, v___x_2452_, v___x_2477_, v___x_2466_);
lean_inc(v___x_2440_);
v___x_2479_ = l_Lean_Syntax_node3(v___x_2440_, v___x_2449_, v___x_2467_, v___x_2470_, v___x_2478_);
lean_inc(v___x_2440_);
v___x_2480_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2448_, v___x_2479_);
lean_inc(v___x_2440_);
v___x_2481_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2447_, v___x_2480_);
lean_inc(v___x_2440_);
v___x_2482_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2446_, v___x_2481_);
v___x_2483_ = l_Lean_Syntax_node3(v___x_2440_, v___x_2441_, v___x_2443_, v___x_2445_, v___x_2482_);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
lean_ctor_set(v___x_2484_, 1, v_a_2427_);
return v___x_2484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___boxed(lean_object* v_x_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1(v_x_2485_, v_a_2486_, v_a_2487_);
lean_dec_ref(v_a_2486_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1(lean_object* v_x_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2513_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1));
lean_inc(v_x_2510_);
v___x_2514_ = l_Lean_Syntax_isOfKind(v_x_2510_, v___x_2513_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_dec(v_x_2510_);
v___x_2515_ = lean_box(1);
v___x_2516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
lean_ctor_set(v___x_2516_, 1, v_a_2512_);
return v___x_2516_;
}
else
{
lean_object* v_ref_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_ref_2517_ = lean_ctor_get(v_a_2511_, 5);
v___x_2518_ = lean_unsigned_to_nat(1u);
v___x_2519_ = l_Lean_Syntax_getArg(v_x_2510_, v___x_2518_);
lean_dec(v_x_2510_);
v___x_2520_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq___closed__1));
v___x_2521_ = 0;
v___x_2522_ = l_Lean_SourceInfo_fromRef(v_ref_2517_, v___x_2521_);
v___x_2523_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_first___closed__0));
v___x_2524_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_first___closed__1));
lean_inc(v___x_2522_);
v___x_2525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2522_);
lean_ctor_set(v___x_2525_, 1, v___x_2523_);
v___x_2526_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5));
v___x_2527_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_first___closed__7));
v___x_2528_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_case___closed__4));
lean_inc(v___x_2522_);
v___x_2529_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2522_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3));
v___x_2531_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_paren___closed__1));
v___x_2532_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_occs___closed__4));
lean_inc(v___x_2522_);
v___x_2533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2522_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__13));
lean_inc(v___x_2522_);
v___x_2535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2522_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
lean_inc(v___x_2519_);
lean_inc(v___x_2522_);
v___x_2536_ = l_Lean_Syntax_node3(v___x_2522_, v___x_2531_, v___x_2533_, v___x_2519_, v___x_2535_);
v___x_2537_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2));
lean_inc(v___x_2522_);
v___x_2538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2522_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0));
lean_inc(v___x_2522_);
v___x_2540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2522_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
lean_inc(v___x_2522_);
v___x_2541_ = l_Lean_Syntax_node2(v___x_2522_, v___x_2513_, v___x_2540_, v___x_2519_);
lean_inc(v___x_2522_);
v___x_2542_ = l_Lean_Syntax_node3(v___x_2522_, v___x_2526_, v___x_2536_, v___x_2538_, v___x_2541_);
lean_inc(v___x_2522_);
v___x_2543_ = l_Lean_Syntax_node1(v___x_2522_, v___x_2530_, v___x_2542_);
lean_inc(v___x_2522_);
v___x_2544_ = l_Lean_Syntax_node1(v___x_2522_, v___x_2520_, v___x_2543_);
lean_inc_ref(v___x_2529_);
lean_inc(v___x_2522_);
v___x_2545_ = l_Lean_Syntax_node2(v___x_2522_, v___x_2527_, v___x_2529_, v___x_2544_);
v___x_2546_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_skip___closed__0));
v___x_2547_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_skip___closed__1));
lean_inc(v___x_2522_);
v___x_2548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2522_);
lean_ctor_set(v___x_2548_, 1, v___x_2546_);
lean_inc(v___x_2522_);
v___x_2549_ = l_Lean_Syntax_node1(v___x_2522_, v___x_2547_, v___x_2548_);
lean_inc(v___x_2522_);
v___x_2550_ = l_Lean_Syntax_node1(v___x_2522_, v___x_2526_, v___x_2549_);
lean_inc(v___x_2522_);
v___x_2551_ = l_Lean_Syntax_node1(v___x_2522_, v___x_2530_, v___x_2550_);
lean_inc(v___x_2522_);
v___x_2552_ = l_Lean_Syntax_node1(v___x_2522_, v___x_2520_, v___x_2551_);
lean_inc(v___x_2522_);
v___x_2553_ = l_Lean_Syntax_node2(v___x_2522_, v___x_2527_, v___x_2529_, v___x_2552_);
lean_inc(v___x_2522_);
v___x_2554_ = l_Lean_Syntax_node2(v___x_2522_, v___x_2526_, v___x_2545_, v___x_2553_);
v___x_2555_ = l_Lean_Syntax_node2(v___x_2522_, v___x_2524_, v___x_2525_, v___x_2554_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
lean_ctor_set(v___x_2556_, 1, v_a_2512_);
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___boxed(lean_object* v_x_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1(v_x_2557_, v_a_2558_, v_a_2559_);
lean_dec_ref(v_a_2558_);
return v_res_2560_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__4(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2572_ = l_Lean_Parser_Tactic_optConfig;
v___x_2573_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_extractLets___closed__3));
v___x_2574_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_2575_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___x_2573_);
lean_ctor_set(v___x_2575_, 2, v___x_2572_);
return v___x_2575_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__10(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2591_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_extractLets___closed__9));
v___x_2592_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_extractLets___closed__4, &l_Lean_Parser_Tactic_Conv_extractLets___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__4);
v___x_2593_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_2594_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v___x_2592_);
lean_ctor_set(v___x_2594_, 2, v___x_2591_);
return v___x_2594_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__11(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2595_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_extractLets___closed__10, &l_Lean_Parser_Tactic_Conv_extractLets___closed__10_once, _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__10);
v___x_2596_ = lean_unsigned_to_nat(1022u);
v___x_2597_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_extractLets___closed__1));
v___x_2598_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v___x_2596_);
lean_ctor_set(v___x_2598_, 2, v___x_2595_);
return v___x_2598_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_extractLets(void){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_extractLets___closed__11, &l_Lean_Parser_Tactic_Conv_extractLets___closed__11_once, _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__11);
return v___x_2599_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__4(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2611_ = l_Lean_Parser_Tactic_optConfig;
v___x_2612_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_liftLets___closed__3));
v___x_2613_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8));
v___x_2614_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v___x_2612_);
lean_ctor_set(v___x_2614_, 2, v___x_2611_);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__5(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2615_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_liftLets___closed__4, &l_Lean_Parser_Tactic_Conv_liftLets___closed__4_once, _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__4);
v___x_2616_ = lean_unsigned_to_nat(1022u);
v___x_2617_ = ((lean_object*)(l_Lean_Parser_Tactic_Conv_liftLets___closed__1));
v___x_2618_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
lean_ctor_set(v___x_2618_, 1, v___x_2616_);
lean_ctor_set(v___x_2618_, 2, v___x_2615_);
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Conv_liftLets(void){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = lean_obj_once(&l_Lean_Parser_Tactic_Conv_liftLets___closed__5, &l_Lean_Parser_Tactic_Conv_liftLets___closed__5_once, _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__5);
return v___x_2619_;
}
}
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Conv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Conv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Category_conv = _init_l_Lean_Parser_Category_conv();
lean_mark_persistent(l_Lean_Parser_Category_conv);
l_Lean_Parser_Tactic_Conv_ext = _init_l_Lean_Parser_Tactic_Conv_ext();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_ext);
l_Lean_Parser_Tactic_Conv_rewrite = _init_l_Lean_Parser_Tactic_Conv_rewrite();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_rewrite);
l_Lean_Parser_Tactic_Conv_simp = _init_l_Lean_Parser_Tactic_Conv_simp();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_simp);
l_Lean_Parser_Tactic_Conv_simpTrace = _init_l_Lean_Parser_Tactic_Conv_simpTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_simpTrace);
l_Lean_Parser_Tactic_Conv_dsimp = _init_l_Lean_Parser_Tactic_Conv_dsimp();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_dsimp);
l_Lean_Parser_Tactic_Conv_dsimpTrace = _init_l_Lean_Parser_Tactic_Conv_dsimpTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_dsimpTrace);
l_Lean_Parser_Tactic_Conv_case = _init_l_Lean_Parser_Tactic_Conv_case();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_case);
l_Lean_Parser_Tactic_Conv_case_x27 = _init_l_Lean_Parser_Tactic_Conv_case_x27();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_case_x27);
l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__ = _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__);
l_Lean_Parser_Tactic_Conv_convRw____ = _init_l_Lean_Parser_Tactic_Conv_convRw____();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convRw____);
l_Lean_Parser_Tactic_Conv_convErw____ = _init_l_Lean_Parser_Tactic_Conv_convErw____();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convErw____);
l_Lean_Parser_Tactic_Conv_convIntro______ = _init_l_Lean_Parser_Tactic_Conv_convIntro______();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convIntro______);
l_Lean_Parser_Tactic_Conv_enterArg = _init_l_Lean_Parser_Tactic_Conv_enterArg();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_enterArg);
l_Lean_Parser_Tactic_Conv_enter = _init_l_Lean_Parser_Tactic_Conv_enter();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_enter);
l_Lean_Parser_Tactic_Conv_extractLets = _init_l_Lean_Parser_Tactic_Conv_extractLets();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_extractLets);
l_Lean_Parser_Tactic_Conv_liftLets = _init_l_Lean_Parser_Tactic_Conv_liftLets();
lean_mark_persistent(l_Lean_Parser_Tactic_Conv_liftLets);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Tactics(uint8_t builtin);
lean_object* initialize_Init_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Conv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Conv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Conv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Conv(builtin);
}
#ifdef __cplusplus
}
#endif
