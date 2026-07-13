// Lean compiler output
// Module: Init.Grind.Interactive
// Imports: public import Init.Grind.Attr
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
extern lean_object* l_Lean_binderIdent;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Attr_grindMod;
extern lean_object* l_Lean_Parser_Tactic_configItem;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_appendCore___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_rwRuleSeq;
extern lean_object* l_Lean_Parser_Tactic_caseArg;
static const lean_string_object l_Lean_Parser_Tactic_anchor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "anchor"};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_anchor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_anchor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_anchor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 155, 228, 98, 168, 72, 115, 174)}};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_anchor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_anchor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_anchor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noWs"};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__9_value),LEAN_SCALAR_PTR_LITERAL(92, 29, 204, 148, 167, 109, 242, 21)}};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic_anchor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__13_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__12_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_anchor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__16_value)}};
static const lean_object* l_Lean_Parser_Tactic_anchor___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__17_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_anchor = (const lean_object*)&l_Lean_Parser_Tactic_anchor___closed__17_value;
static const lean_string_object l_Lean_Parser_Tactic_grindLemma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindLemma"};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 180, 24, 243, 113, 54, 79, 133)}};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_grindLemma___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppGroup"};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemma___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__2_value),LEAN_SCALAR_PTR_LITERAL(149, 180, 65, 169, 196, 28, 141, 221)}};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_grindLemma___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemma___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__4_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_grindLemma___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemma___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__6_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemma___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grindLemma___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindLemma___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_grindLemma___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindLemma___closed__10;
static const lean_string_object l_Lean_Parser_Tactic_grindLemma___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemma___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__11_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemma___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_grindLemma___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__13_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grindLemma___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindLemma___closed__14;
static lean_once_cell_t l_Lean_Parser_Tactic_grindLemma___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindLemma___closed__15;
static lean_once_cell_t l_Lean_Parser_Tactic_grindLemma___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindLemma___closed__16;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindLemma;
static const lean_string_object l_Lean_Parser_Tactic_grindLemmaMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLemmaMin"};
static const lean_object* l_Lean_Parser_Tactic_grindLemmaMin___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemmaMin___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_grindLemmaMin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 124, 255, 191, 121, 182, 88, 219)}};
static const lean_object* l_Lean_Parser_Tactic_grindLemmaMin___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_grindLemmaMin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l_Lean_Parser_Tactic_grindLemmaMin___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemmaMin___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindLemmaMin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemmaMin___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_grindLemmaMin___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_grindLemmaMin___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grindLemmaMin___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindLemmaMin___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_grindLemmaMin___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindLemmaMin___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_grindLemmaMin___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindLemmaMin___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_grindLemmaMin___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindLemmaMin___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindLemmaMin;
static const lean_string_object l_Lean_Parser_Tactic_grindErase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindErase"};
static const lean_object* l_Lean_Parser_Tactic_grindErase___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindErase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 172, 113, 174, 15, 5, 26, 121)}};
static const lean_object* l_Lean_Parser_Tactic_grindErase___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_grindErase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Parser_Tactic_grindErase___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindErase___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_grindErase___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_grindErase___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_Tactic_grindErase___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindErase___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_Tactic_grindErase___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindErase___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_grindErase___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindErase___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_grindErase___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindErase___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_grindErase___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_grindErase = (const lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_grindParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindParam"};
static const lean_object* l_Lean_Parser_Tactic_grindParam___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_grindParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 144, 208, 205, 52, 106, 220, 83)}};
static const lean_object* l_Lean_Parser_Tactic_grindParam___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_grindParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Parser_Tactic_grindParam___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Parser_Tactic_grindParam___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grindParam___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_grindParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_grindParam___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_grindParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grindParam;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grind_filter"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(195, 37, 150, 156, 133, 238, 188, 206)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 142, 161, 65, 42, 54, 137, 29)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "`(grind_filter| "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(195, 37, 150, 156, 133, 238, 188, 206)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_quot = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_grind__filter;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grind_filter_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 183, 54, 132, 193, 221, 83, 246)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grind_filterGen<_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 91, 104, 32, 61, 131, 243, 196)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "gen"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " < "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grind_filterGen=_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 110, 208, 13, 150, 123, 60, 151)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "grind_filterGen!=_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 149, 94, 94, 69, 234, 169, 170)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " != "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 17, .m_data = "grind_filterGen≤_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 191, 11, 181, 243, 245, 215, 191)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≤ "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "grind_filterGen<=_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 96, 49, 75, 137, 142, 109, 186)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " <= "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grind_filterGen>_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 245, 163, 142, 72, 168, 216, 63)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " > "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 17, .m_data = "grind_filterGen≥_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 138, 8, 224, 7, 211, 129, 34)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≥ "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "grind_filterGen>=_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 129, 153, 143, 173, 111, 170, 63)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " >= "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grind_filter(_)"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 150, 229, 147, 17, 198, 129, 17)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grind_filter_&&_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 18, 222, 93, 166, 92, 88, 35)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " && "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grind_filter_||_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 127, 248, 101, 151, 207, 64, 193)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " || "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grind_filter!_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 240, 71, 91, 236, 83, 171, 27)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemmaMin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7_value),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__filter_x21__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindFilter"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindFilter___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 133, 155, 61, 50, 240, 42, 169)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindFilter___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindFilter___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindFilter___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindFilter___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindFilter___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindFilter___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindFilter___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grindFilter = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_quot___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(13, 180, 177, 196, 78, 54, 222, 84)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_quot___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "`(grind| "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_quot___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_quot___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_quot___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_quot___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind_quot = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_grind;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindStep"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 239, 5, 217, 230, 199, 187, 87)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grindStep = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grindSeq1Indented"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 114, 22, 139, 17, 175, 241, 184)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "sepBy1IndentSemicolon"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(22, 113, 252, 92, 83, 246, 160, 172)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq1Indented = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grindSeqBracketed"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 10, 37, 72, 63, 213, 137, 199)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sepByIndentSemicolon"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__6_value),LEAN_SCALAR_PTR_LITERAL(139, 141, 160, 225, 89, 107, 71, 117)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grindSeqBracketed = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__14_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__14_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grindSeq = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_paren___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Parser_Tactic_Grind_paren___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_paren___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 134, 107, 245, 63, 193, 1, 88)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_paren___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_paren___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_paren___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_paren___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_paren___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_paren___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_paren___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_paren___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_paren___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_paren = (const lean_object*)&l_Lean_Parser_Tactic_Grind_paren___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_skip___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l_Lean_Parser_Tactic_Grind_skip___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_skip___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 95, 123, 110, 162, 109, 248, 53)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_skip___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_skip___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_skip___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_skip___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_skip___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_skip = (const lean_object*)&l_Lean_Parser_Tactic_Grind_skip___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_lia___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Parser_Tactic_Grind_lia___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_lia___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 14, 196, 226, 73, 38, 159, 13)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_lia___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_lia___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_lia___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_lia___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_lia___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_lia = (const lean_object*)&l_Lean_Parser_Tactic_Grind_lia___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_ring___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ring"};
static const lean_object* l_Lean_Parser_Tactic_Grind_ring___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ring___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 12, 164, 69, 244, 1, 113, 234)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_ring___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ring___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_ring___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ring___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_ring___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_ring = (const lean_object*)&l_Lean_Parser_Tactic_Grind_ring___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_ac___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ac"};
static const lean_object* l_Lean_Parser_Tactic_Grind_ac___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ac___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 101, 98, 118, 98, 241, 140, 11)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_ac___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ac___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_ac___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_ac___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_ac___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_ac = (const lean_object*)&l_Lean_Parser_Tactic_Grind_ac___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_linarith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linarith"};
static const lean_object* l_Lean_Parser_Tactic_Grind_linarith___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_linarith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 138, 142, 132, 28, 165, 234, 226)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_linarith___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_linarith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_linarith___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_linarith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_linarith___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_linarith = (const lean_object*)&l_Lean_Parser_Tactic_Grind_linarith___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_sorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sorry"};
static const lean_object* l_Lean_Parser_Tactic_Grind_sorry___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_sorry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 71, 141, 15, 124, 86, 0, 175)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_sorry___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_sorry___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_sorry___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_sorry___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_sorry___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_sorry = (const lean_object*)&l_Lean_Parser_Tactic_Grind_sorry___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_thmNs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "thmNs"};
static const lean_object* l_Lean_Parser_Tactic_Grind_thmNs___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 18, 142, 106, 37, 179, 0, 161)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_thmNs___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_thmNs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l_Lean_Parser_Tactic_Grind_thmNs___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thmNs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_thmNs___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thmNs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_thmNs___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thmNs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_thmNs___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_thmNs = (const lean_object*)&l_Lean_Parser_Tactic_Grind_thmNs___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_thm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l_Lean_Parser_Tactic_Grind_thm___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_thm___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_thm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_thm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 175, 92, 250, 215, 173, 92, 62)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_thm___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_thm___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_thm___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_thm___closed__2;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_thm___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_thm___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_thm___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_thm___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_thm___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_thm___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_thm;
static const lean_string_object l_Lean_Parser_Tactic_Grind_instantiate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "instantiate"};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 223, 197, 126, 28, 51, 106, 179)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_instantiate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " only"};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_instantiate___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " approx"};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_instantiate___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_instantiate___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__13_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_instantiate___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__15_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_instantiate___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__16;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_instantiate___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__17;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_instantiate___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__18;
static const lean_string_object l_Lean_Parser_Tactic_Grind_instantiate___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_instantiate___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__19_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__20_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_instantiate___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__21;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_instantiate___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__22;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_instantiate___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__23;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_instantiate___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_instantiate___closed__24;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_instantiate;
static const lean_string_object l_Lean_Parser_Tactic_Grind_use___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "use"};
static const lean_object* l_Lean_Parser_Tactic_Grind_use___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_use___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_use___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_use___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 64, 35, 249, 247, 52, 171, 66)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_use___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_use___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_use___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_use___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_use___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_use___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_use___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_use___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_use___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_use___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_use___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_use___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_use___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_use___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_use___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_use___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_use;
static const lean_string_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3;
static const lean_string_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Grind_showAsserted___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "showAsserted"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showAsserted___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 9, 52, 210, 246, 83, 42, 129)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showAsserted___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showAsserted___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "show_asserted"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showAsserted___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showAsserted___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showAsserted___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showAsserted___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showAsserted___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showAsserted___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showAsserted___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showAsserted___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showAsserted___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_showAsserted = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showAsserted___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showTrue"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTrue___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 221, 230, 107, 62, 158, 128, 182)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTrue___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "show_true"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTrue___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTrue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTrue___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTrue___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTrue___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTrue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTrue___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_showTrue = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTrue___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showFalse"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showFalse___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 23, 10, 157, 249, 80, 147, 23)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showFalse___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showFalse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "show_false"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showFalse___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showFalse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showFalse___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showFalse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showFalse___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showFalse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showFalse___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showFalse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showFalse___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_showFalse = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showFalse___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showEqcs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showEqcs"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showEqcs___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 148, 3, 250, 60, 240, 18, 216)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showEqcs___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showEqcs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "show_eqcs"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showEqcs___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showEqcs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showEqcs___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showEqcs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showEqcs___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showEqcs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showEqcs___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showEqcs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showEqcs___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_showEqcs = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showEqcs___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showCases"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showCases___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 129, 48, 5, 176, 175, 163, 129)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showCases___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "show_cases"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showCases___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showCases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showCases___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showCases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showCases___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showCases___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showCases___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showCases___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showCases___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_showCases = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showCases___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showState"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showState___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 80, 82, 248, 223, 67, 174, 140)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showState___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showState___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "show_state"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showState___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showState___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showState___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showState___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showState___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showState___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showState___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showState___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showState___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_showState = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showState___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showLocalThms___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "showLocalThms"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showLocalThms___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 164, 136, 213, 0, 240, 18, 240)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showLocalThms___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "show_local_thms"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showLocalThms___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showLocalThms___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showLocalThms___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showLocalThms___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showLocalThms___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_showLocalThms = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showLocalThms___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showTerm"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTerm___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 150, 74, 14, 71, 142, 109, 156)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTerm___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "show_term "};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTerm___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTerm___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTerm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTerm___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showTerm___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showTerm___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_showTerm = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showTerm___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "showGoals"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showGoals___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 134, 23, 147, 3, 222, 47, 68)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showGoals___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_showGoals___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "show_goals"};
static const lean_object* l_Lean_Parser_Tactic_Grind_showGoals___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showGoals___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showGoals___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_showGoals___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_showGoals___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_showGoals = (const lean_object*)&l_Lean_Parser_Tactic_Grind_showGoals___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grind_ref"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 189, 209, 190, 183, 163, 99, 90)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(19, 15, 170, 103, 45, 23, 243, 97)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "`(grind_ref| "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 189, 209, 190, 183, 163, 99, 90)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_quot = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_grind__ref;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_ref_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 234, 46, 225, 9, 69, 165, 154)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__17_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grind_ref__/__"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 78, 76, 1, 128, 192, 165, 233)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__17_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref_____x2f____ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_____x2f_____00__closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grind_ref__1"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 215, 110, 75, 133, 130, 84, 131)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind__ref____1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_cases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_Lean_Parser_Tactic_Grind_cases___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_cases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 233, 158, 17, 45, 135, 214, 137)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_cases___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_cases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cases "};
static const lean_object* l_Lean_Parser_Tactic_Grind_cases___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_cases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_cases___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_cases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_cases___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_cases___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_cases___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_cases = (const lean_object*)&l_Lean_Parser_Tactic_Grind_cases___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_casesTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "casesTrace"};
static const lean_object* l_Lean_Parser_Tactic_Grind_casesTrace___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 50, 184, 173, 128, 245, 159, 246)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_casesTrace___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_casesTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cases\?"};
static const lean_object* l_Lean_Parser_Tactic_Grind_casesTrace___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_casesTrace___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_casesTrace___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesTrace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_casesTrace___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_casesTrace = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesTrace___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_casesNext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "casesNext"};
static const lean_object* l_Lean_Parser_Tactic_Grind_casesNext___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 188, 72, 37, 244, 29, 48, 15)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_casesNext___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_casesNext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cases_next"};
static const lean_object* l_Lean_Parser_Tactic_Grind_casesNext___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesNext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_casesNext___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_casesNext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_casesNext___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_casesNext = (const lean_object*)&l_Lean_Parser_Tactic_Grind_casesNext___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_done___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Lean_Parser_Tactic_Grind_done___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_done___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 96, 222, 221, 183, 249, 85, 65)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_done___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_done___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_done___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_done___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_done___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_done = (const lean_object*)&l_Lean_Parser_Tactic_Grind_done___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_finish___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "finish"};
static const lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finish___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 141, 128, 132, 58, 161, 38, 215)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finish___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_finish___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finish___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__4_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finish___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finish___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finish___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__7;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finish___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finish___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finish___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finish___closed__10_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finish___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finish___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__12;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finish___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finish___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__14;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finish___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__15;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finish___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__16;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finish___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__17;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finish___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finish___closed__18;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_finish;
static const lean_string_object l_Lean_Parser_Tactic_Grind_finishTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "finishTrace"};
static const lean_object* l_Lean_Parser_Tactic_Grind_finishTrace___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finishTrace___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_finishTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 104, 221, 59, 99, 114, 168, 144)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_finishTrace___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_finishTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "finish\?"};
static const lean_object* l_Lean_Parser_Tactic_Grind_finishTrace___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finishTrace___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_finishTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_finishTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_finishTrace___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_finishTrace___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finishTrace___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finishTrace___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finishTrace___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finishTrace___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finishTrace___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finishTrace___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_finishTrace___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_finishTrace___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_finishTrace;
static const lean_string_object l_Lean_Parser_Tactic_Grind_have___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l_Lean_Parser_Tactic_Grind_have___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_have___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 36, 229, 233, 71, 216, 202, 183)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_have___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_have___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_have___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_have___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Parser_Tactic_Grind_have___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_have___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__3_value),LEAN_SCALAR_PTR_LITERAL(237, 158, 72, 239, 156, 118, 8, 209)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_have___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_have___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_have___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_have___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_have___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_have___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_have___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_have = (const lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "nestedTacticCore"};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 148, 190, 235, 218, 2, 248, 160)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_nestedTacticCore = (const lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_allGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l_Lean_Parser_Tactic_Grind_allGoals___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 176, 42, 44, 172, 202, 38, 34)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_allGoals___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_allGoals___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "all_goals "};
static const lean_object* l_Lean_Parser_Tactic_Grind_allGoals___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_allGoals___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_allGoals___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_allGoals___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_allGoals___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_allGoals___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_allGoals___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_allGoals = (const lean_object*)&l_Lean_Parser_Tactic_Grind_allGoals___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_focus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "focus"};
static const lean_object* l_Lean_Parser_Tactic_Grind_focus___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_focus___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 68, 95, 128, 15, 244, 165, 139)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_focus___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_focus___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "focus "};
static const lean_object* l_Lean_Parser_Tactic_Grind_focus___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_focus___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_focus___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_focus___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_focus___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_focus___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_focus___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_focus = (const lean_object*)&l_Lean_Parser_Tactic_Grind_focus___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_next___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "next"};
static const lean_object* l_Lean_Parser_Tactic_Grind_next___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_next___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_next___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_next___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 67, 127, 148, 132, 17, 131, 108)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_next___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_next___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_next___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next "};
static const lean_object* l_Lean_Parser_Tactic_Grind_next___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_next___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_next___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_next___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_next___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_next___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_next___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_next___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_next___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_next___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_next___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_next___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_next___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_next___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_next___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_next___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_next;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 7, .m_data = "grind·_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 208, 22, 131, 194, 122, 241, 171)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "· "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind_xb7__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Grind_case___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "case"};
static const lean_object* l_Lean_Parser_Tactic_Grind_case___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_case___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_case___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_case___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_case___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_case___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 173, 21, 189, 81, 211, 125, 169)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_case___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_case___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case "};
static const lean_object* l_Lean_Parser_Tactic_Grind_case___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_case___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_case___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_case___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " | "};
static const lean_object* l_Lean_Parser_Tactic_Grind_case___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_case___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_case___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_case___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_case___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_case___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_case___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_case___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_case___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_case___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_case___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_case___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_case___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_case___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_case;
static const lean_string_object l_Lean_Parser_Tactic_Grind_anyGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "anyGoals"};
static const lean_object* l_Lean_Parser_Tactic_Grind_anyGoals___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 3, 10, 44, 226, 136, 80, 42)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_anyGoals___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_anyGoals___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "any_goals "};
static const lean_object* l_Lean_Parser_Tactic_Grind_anyGoals___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_anyGoals___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_anyGoals___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_anyGoals___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_anyGoals___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_anyGoals___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_anyGoals___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_anyGoals = (const lean_object*)&l_Lean_Parser_Tactic_Grind_anyGoals___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "withAnnotateState"};
static const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 242, 153, 188, 185, 49, 129, 186)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "with_annotate_state "};
static const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rawStx"};
static const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 156, 151, 53, 25, 160, 240, 109)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_withAnnotateState = (const lean_object*)&l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_<;>_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 7, 229, 204, 205, 179, 221, 240)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " <;> "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__4_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "with_annotate_state"};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "all_goals"};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Grind_first___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 60, 110, 192, 46, 198, 252, 25)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_first___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "first "};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_first___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__4_value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_first___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__6_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_first___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__8_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_first___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__10_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_first___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__12_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__11_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_first___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__16_value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__17_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__15_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__18_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__19_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__20_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__21_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__22 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__22_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__22_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__23_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__24_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__24_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__25_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__25_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__26 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__26_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__26_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__27 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__27_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_first___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__27_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_first___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__28_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_first = (const lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__28_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindTry___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindTry_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindTry___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 12, 37, 83, 85, 34, 35, 178)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindTry___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "try "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindTry___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindTry___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindTry___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindTry___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindTry___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindTry___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindTry___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grindTry__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindTry___00__closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "failIfSuccess"};
static const lean_object* l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 235, 219, 147, 187, 132, 195, 48)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fail_if_success "};
static const lean_object* l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_failIfSuccess = (const lean_object*)&l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindAdmit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindAdmit"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindAdmit___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 4, 78, 211, 20, 59, 62, 79)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindAdmit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "admit"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindAdmit___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindAdmit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindAdmit___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindAdmit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindAdmit___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grindAdmit = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindAdmit___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Grind_fail___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fail"};
static const lean_object* l_Lean_Parser_Tactic_Grind_fail___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 42, 125, 152, 218, 230, 194, 180)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_fail___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_fail___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_fail___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Parser_Tactic_Grind_fail___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_fail___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_fail___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_fail___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_fail___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_fail___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_fail___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_fail___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_fail = (const lean_object*)&l_Lean_Parser_Tactic_Grind_fail___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindRepeat_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 93, 145, 161, 123, 119, 39, 92)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "repeat "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grindRepeat__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "repeat"};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Grind_renameI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "renameI"};
static const lean_object* l_Lean_Parser_Tactic_Grind_renameI___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_renameI___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 25, 204, 129, 223, 148, 21, 212)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_renameI___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_renameI___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rename_i"};
static const lean_object* l_Lean_Parser_Tactic_Grind_renameI___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_renameI___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_renameI___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_renameI___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_renameI___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__4_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_renameI___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_renameI___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_renameI___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_renameI___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_renameI___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_renameI___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_renameI___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_renameI___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_renameI;
static const lean_string_object l_Lean_Parser_Tactic_Grind_exposeNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "exposeNames"};
static const lean_object* l_Lean_Parser_Tactic_Grind_exposeNames___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 247, 107, 86, 17, 53, 198, 157)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_exposeNames___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_exposeNames___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "expose_names"};
static const lean_object* l_Lean_Parser_Tactic_Grind_exposeNames___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_exposeNames___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_exposeNames___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_exposeNames___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_exposeNames___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_exposeNames = (const lean_object*)&l_Lean_Parser_Tactic_Grind_exposeNames___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_setOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "setOption"};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 132, 183, 171, 34, 48, 139, 102)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_setOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "set_option "};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_setOption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__11_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__11_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_setOption___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optionValue"};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__13_value),LEAN_SCALAR_PTR_LITERAL(141, 41, 7, 49, 139, 45, 101, 137)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__12_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__16_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_setOption___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__17_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__16_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__18_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__19_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setOption___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__20_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setOption___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__21_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_setOption = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setOption___closed__21_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_setConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "setConfig"};
static const lean_object* l_Lean_Parser_Tactic_Grind_setConfig___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setConfig___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_setConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 24, 145, 44, 206, 52, 130, 57)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setConfig___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_setConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "set_config "};
static const lean_object* l_Lean_Parser_Tactic_Grind_setConfig___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setConfig___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_setConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_setConfig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_setConfig___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_setConfig___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_setConfig___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_setConfig___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_setConfig___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_setConfig___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_setConfig___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_setConfig___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_setConfig___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_setConfig___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_setConfig___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_setConfig___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_setConfig;
static const lean_string_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "haveSilent"};
static const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 40, 33, 99, 54, 221, 176, 65)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_have___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_haveSilent___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_haveSilent = (const lean_object*)&l_Lean_Parser_Tactic_Grind_haveSilent___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_mbtc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mbtc"};
static const lean_object* l_Lean_Parser_Tactic_Grind_mbtc___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 68, 23, 157, 222, 224, 232, 238)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_mbtc___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_mbtc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_mbtc___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_mbtc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_mbtc___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_mbtc = (const lean_object*)&l_Lean_Parser_Tactic_Grind_mbtc___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "symIntro"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 177, 203, 220, 6, 189, 203, 250)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_first___closed__20_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntro___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntro___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntro___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__12_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__13_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__11_value),LEAN_SCALAR_PTR_LITERAL(97, 134, 219, 90, 90, 45, 96, 32)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__11_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__11_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__13_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntro___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__12_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__17_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__16_value),LEAN_SCALAR_PTR_LITERAL(234, 149, 90, 50, 108, 230, 18, 172)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__16_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__16_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__17_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__18_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__15_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__19_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__20_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__21_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__22 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__22_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__22_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntro___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__23_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__24_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_symIntro___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__25;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_symIntro___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__26;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_symIntro___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_symIntro___closed__27;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_symIntro;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntroLight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "symIntroLight"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntroLight___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 188, 225, 186, 156, 62, 173, 87)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntroLight___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntroLight___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntroLight___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "~"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntroLight___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntroLight___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntroLight___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntroLight___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntroLight___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__5_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_symIntroLight;
static const lean_string_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntros___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "symIntros"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntros___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 175, 114, 140, 112, 61, 143, 32)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntros___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntros___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "intros"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntros___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntros___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntros___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntros___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__23_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntros___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntros___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntros___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_symIntros = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "symIntrosLight"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 124, 219, 142, 239, 75, 103, 85)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntros___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_symIntrosLight = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Grind_symApply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "symApply"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symApply___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symApply___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 244, 96, 104, 113, 83, 151, 74)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symApply___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symApply___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "apply "};
static const lean_object* l_Lean_Parser_Tactic_Grind_symApply___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symApply___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symApply___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symApply___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symApply___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symApply___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symApply___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_symApply = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symApply___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symInternalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "symInternalize"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symInternalize___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 99, 88, 106, 108, 255, 121, 14)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symInternalize___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symInternalize___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symInternalize___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symInternalize___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symInternalize___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_symInternalize = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalize___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "symInternalizeAll"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 177, 44, 29, 183, 33, 46, 54)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "internalize_all"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_symInternalizeAll = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symByContra___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "symByContra"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symByContra___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 214, 28, 119, 209, 102, 217, 193)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symByContra___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symByContra___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "by_contra"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symByContra___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symByContra___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symByContra___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symByContra___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symByContra___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_symByContra = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symByContra___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "symSimp"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 109, 151, 25, 234, 136, 56, 252)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symSimp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_renameI___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__13_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__15_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__12_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__20_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symSimp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symSimp___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__12_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_symSimp = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "symDSimp"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 250, 158, 59, 57, 156, 255, 54)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symSimp___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symIntro___closed__12_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__6_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(46, 123, 149, 63, 0, 221, 179, 78)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_grindErase___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__13_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__15_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__12_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__11_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_instantiate___closed__20_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symDSimp___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__15_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_symDSimp = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symDSimp___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symRw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "symRw"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symRw___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symRw___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symRw___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symRw___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symRw___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symRw___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symRw___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symRw___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symRw___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symRw___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symRw___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symRw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 41, 80, 24, 116, 161, 83, 223)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symRw___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symRw___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symRw___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rw "};
static const lean_object* l_Lean_Parser_Tactic_Grind_symRw___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symRw___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symRw___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symRw___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symRw___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symRw___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_symRw___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_symRw___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_symRw___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_symRw___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_symRw;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindExact___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindExact_"};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindExact___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 67, 233, 5, 161, 243, 203, 153)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_grindExact___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "exact "};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindExact___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindExact___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindExact___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindExact___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindExact___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindExact___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindExact___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grindExact__ = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindExact___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Grind_symCbv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "symCbv"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symCbv___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symCbv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symCbv___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symCbv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symCbv___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symCbv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 127, 132, 126, 172, 148, 105, 118)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symCbv___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symCbv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symCbv___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symCbv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symCbv___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symCbv___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symCbv___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_symCbv = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symCbv___closed__4_value;
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma___closed__9(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__8));
v___x_57_ = l_Lean_Parser_Attr_grindMod;
v___x_58_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_59_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma___closed__10(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Lean_Parser_Tactic_grindLemma___closed__9, &l_Lean_Parser_Tactic_grindLemma___closed__9_once, _init_l_Lean_Parser_Tactic_grindLemma___closed__9);
v___x_61_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__5));
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma___closed__14(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__13));
v___x_70_ = lean_obj_once(&l_Lean_Parser_Tactic_grindLemma___closed__10, &l_Lean_Parser_Tactic_grindLemma___closed__10_once, _init_l_Lean_Parser_Tactic_grindLemma___closed__10);
v___x_71_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_72_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_69_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma___closed__15(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_obj_once(&l_Lean_Parser_Tactic_grindLemma___closed__14, &l_Lean_Parser_Tactic_grindLemma___closed__14_once, _init_l_Lean_Parser_Tactic_grindLemma___closed__14);
v___x_74_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__3));
v___x_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma___closed__16(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = lean_obj_once(&l_Lean_Parser_Tactic_grindLemma___closed__15, &l_Lean_Parser_Tactic_grindLemma___closed__15_once, _init_l_Lean_Parser_Tactic_grindLemma___closed__15);
v___x_77_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__1));
v___x_78_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__0));
v___x_79_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_76_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemma(void){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Parser_Tactic_grindLemma___closed__16, &l_Lean_Parser_Tactic_grindLemma___closed__16_once, _init_l_Lean_Parser_Tactic_grindLemma___closed__16);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__4(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = lean_obj_once(&l_Lean_Parser_Tactic_grindLemma___closed__10, &l_Lean_Parser_Tactic_grindLemma___closed__10_once, _init_l_Lean_Parser_Tactic_grindLemma___closed__10);
v___x_91_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemmaMin___closed__3));
v___x_92_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_93_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
lean_ctor_set(v___x_93_, 2, v___x_90_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__5(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_94_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__13));
v___x_95_ = lean_obj_once(&l_Lean_Parser_Tactic_grindLemmaMin___closed__4, &l_Lean_Parser_Tactic_grindLemmaMin___closed__4_once, _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__4);
v___x_96_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_97_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
lean_ctor_set(v___x_97_, 2, v___x_94_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__6(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = lean_obj_once(&l_Lean_Parser_Tactic_grindLemmaMin___closed__5, &l_Lean_Parser_Tactic_grindLemmaMin___closed__5_once, _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__5);
v___x_99_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__3));
v___x_100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__7(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_101_ = lean_obj_once(&l_Lean_Parser_Tactic_grindLemmaMin___closed__6, &l_Lean_Parser_Tactic_grindLemmaMin___closed__6_once, _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__6);
v___x_102_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemmaMin___closed__1));
v___x_103_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemmaMin___closed__0));
v___x_104_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_101_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindLemmaMin(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Parser_Tactic_grindLemmaMin___closed__7, &l_Lean_Parser_Tactic_grindLemmaMin___closed__7_once, _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__7);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__4(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_138_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor));
v___x_139_ = l_Lean_Parser_Tactic_grindLemma;
v___x_140_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_141_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
lean_ctor_set(v___x_141_, 2, v___x_138_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__5(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = lean_obj_once(&l_Lean_Parser_Tactic_grindParam___closed__4, &l_Lean_Parser_Tactic_grindParam___closed__4_once, _init_l_Lean_Parser_Tactic_grindParam___closed__4);
v___x_143_ = l_Lean_Parser_Tactic_grindLemmaMin;
v___x_144_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_145_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
lean_ctor_set(v___x_145_, 2, v___x_142_);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__6(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = lean_obj_once(&l_Lean_Parser_Tactic_grindParam___closed__5, &l_Lean_Parser_Tactic_grindParam___closed__5_once, _init_l_Lean_Parser_Tactic_grindParam___closed__5);
v___x_147_ = ((lean_object*)(l_Lean_Parser_Tactic_grindErase));
v___x_148_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_149_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
lean_ctor_set(v___x_149_, 2, v___x_146_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__7(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_obj_once(&l_Lean_Parser_Tactic_grindParam___closed__6, &l_Lean_Parser_Tactic_grindParam___closed__6_once, _init_l_Lean_Parser_Tactic_grindParam___closed__6);
v___x_151_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__1));
v___x_152_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__0));
v___x_153_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
lean_ctor_set(v___x_153_, 2, v___x_150_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_once(&l_Lean_Parser_Tactic_grindParam___closed__7, &l_Lean_Parser_Tactic_grindParam___closed__7_once, _init_l_Lean_Parser_Tactic_grindParam___closed__7);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Parser_Category_grind__filter(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(0);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Parser_Category_grind(void){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_box(0);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_thm___closed__2(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_791_ = l_Lean_Parser_Tactic_grindLemma;
v___x_792_ = l_Lean_Parser_Tactic_grindLemmaMin;
v___x_793_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_794_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___x_792_);
lean_ctor_set(v___x_794_, 2, v___x_791_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_thm___closed__3(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_795_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_thm___closed__2, &l_Lean_Parser_Tactic_Grind_thm___closed__2_once, _init_l_Lean_Parser_Tactic_Grind_thm___closed__2);
v___x_796_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_thmNs));
v___x_797_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_798_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___x_796_);
lean_ctor_set(v___x_798_, 2, v___x_795_);
return v___x_798_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_thm___closed__4(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_799_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_thm___closed__3, &l_Lean_Parser_Tactic_Grind_thm___closed__3_once, _init_l_Lean_Parser_Tactic_Grind_thm___closed__3);
v___x_800_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor));
v___x_801_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_802_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v___x_800_);
lean_ctor_set(v___x_802_, 2, v___x_799_);
return v___x_802_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_thm___closed__5(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_803_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_thm___closed__4, &l_Lean_Parser_Tactic_Grind_thm___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_thm___closed__4);
v___x_804_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_thm___closed__1));
v___x_805_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_thm___closed__0));
v___x_806_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___x_804_);
lean_ctor_set(v___x_806_, 2, v___x_803_);
return v___x_806_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_thm(void){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_thm___closed__5, &l_Lean_Parser_Tactic_Grind_thm___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_thm___closed__5);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__16(void){
_start:
{
uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_847_ = 1;
v___x_848_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__15));
v___x_849_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__13));
v___x_850_ = l_Lean_Parser_Tactic_Grind_thm;
v___x_851_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_849_);
lean_ctor_set(v___x_851_, 2, v___x_848_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*3, v___x_847_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__17(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__16, &l_Lean_Parser_Tactic_Grind_instantiate___closed__16_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__16);
v___x_853_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5));
v___x_854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_852_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__18(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_855_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__17, &l_Lean_Parser_Tactic_Grind_instantiate___closed__17_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__17);
v___x_856_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__12));
v___x_857_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_858_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
lean_ctor_set(v___x_858_, 2, v___x_855_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__21(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_862_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__20));
v___x_863_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__18, &l_Lean_Parser_Tactic_Grind_instantiate___closed__18_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__18);
v___x_864_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_865_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_863_);
lean_ctor_set(v___x_865_, 2, v___x_862_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__22(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__21, &l_Lean_Parser_Tactic_Grind_instantiate___closed__21_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__21);
v___x_867_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__5));
v___x_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v___x_866_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__23(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_869_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__22, &l_Lean_Parser_Tactic_Grind_instantiate___closed__22_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__22);
v___x_870_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__10));
v___x_871_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_872_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_870_);
lean_ctor_set(v___x_872_, 2, v___x_869_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__24(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_873_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__23, &l_Lean_Parser_Tactic_Grind_instantiate___closed__23_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__23);
v___x_874_ = lean_unsigned_to_nat(1022u);
v___x_875_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__1));
v___x_876_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_874_);
lean_ctor_set(v___x_876_, 2, v___x_873_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate(void){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__24, &l_Lean_Parser_Tactic_Grind_instantiate___closed__24_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__24);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_use___closed__4(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_892_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__17, &l_Lean_Parser_Tactic_Grind_instantiate___closed__17_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__17);
v___x_893_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_use___closed__3));
v___x_894_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_895_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_893_);
lean_ctor_set(v___x_895_, 2, v___x_892_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_use___closed__5(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_896_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__20));
v___x_897_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_use___closed__4, &l_Lean_Parser_Tactic_Grind_use___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_use___closed__4);
v___x_898_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_899_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v___x_897_);
lean_ctor_set(v___x_899_, 2, v___x_896_);
return v___x_899_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_use___closed__6(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_900_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_use___closed__5, &l_Lean_Parser_Tactic_Grind_use___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_use___closed__5);
v___x_901_ = lean_unsigned_to_nat(1024u);
v___x_902_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_use___closed__1));
v___x_903_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_901_);
lean_ctor_set(v___x_903_, 2, v___x_900_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_use(void){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_use___closed__6, &l_Lean_Parser_Tactic_Grind_use___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_use___closed__6);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3(void){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Array_mkArray0(lean_box(0));
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1(lean_object* v_x_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_914_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_use___closed__1));
lean_inc(v_x_911_);
v___x_915_ = l_Lean_Syntax_isOfKind(v_x_911_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec(v_x_911_);
v___x_916_ = lean_box(1);
v___x_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v_a_913_);
return v___x_917_;
}
else
{
lean_object* v_ref_918_; lean_object* v___x_919_; lean_object* v_u_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_ref_918_ = lean_ctor_get(v_a_912_, 5);
v___x_919_ = lean_unsigned_to_nat(0u);
v_u_920_ = l_Lean_Syntax_getArg(v_x_911_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(2u);
v___x_922_ = l_Lean_Syntax_getArg(v_x_911_, v___x_921_);
lean_dec(v_x_911_);
v___x_923_ = l_Lean_Syntax_getArgs(v___x_922_);
lean_dec(v___x_922_);
v___x_924_ = 0;
v___x_925_ = l_Lean_SourceInfo_fromRef(v_ref_918_, v___x_924_);
v___x_926_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__0));
v___x_927_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__1));
v___x_928_ = l_Lean_SourceInfo_fromRef(v_u_920_, v___x_915_);
lean_dec(v_u_920_);
v___x_929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_926_);
v___x_930_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_931_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__2));
lean_inc_n(v___x_925_, 7);
v___x_932_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_925_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_Syntax_node1(v___x_925_, v___x_930_, v___x_932_);
v___x_934_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
v___x_935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_935_, 0, v___x_925_);
lean_ctor_set(v___x_935_, 1, v___x_930_);
lean_ctor_set(v___x_935_, 2, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__4));
v___x_937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_925_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Array_appendCore___redArg(v___x_934_, v___x_923_);
lean_dec_ref(v___x_923_);
v___x_939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_939_, 0, v___x_925_);
lean_ctor_set(v___x_939_, 1, v___x_930_);
lean_ctor_set(v___x_939_, 2, v___x_938_);
v___x_940_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__19));
v___x_941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_925_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Lean_Syntax_node3(v___x_925_, v___x_930_, v___x_937_, v___x_939_, v___x_941_);
v___x_943_ = l_Lean_Syntax_node4(v___x_925_, v___x_927_, v___x_929_, v___x_933_, v___x_935_, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_a_913_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___boxed(lean_object* v_x_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1(v_x_945_, v_a_946_, v_a_947_);
lean_dec_ref(v_a_946_);
return v_res_948_;
}
}
static lean_object* _init_l_Lean_Parser_Category_grind__ref(void){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_box(0);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__5(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1314_ = l_Lean_Parser_Tactic_configItem;
v___x_1315_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__8));
v___x_1316_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1317_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v___x_1315_);
lean_ctor_set(v___x_1317_, 2, v___x_1314_);
return v___x_1317_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__6(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__5, &l_Lean_Parser_Tactic_Grind_finish___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__5);
v___x_1319_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__4));
v___x_1320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v___x_1318_);
return v___x_1320_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__7(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1321_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__6, &l_Lean_Parser_Tactic_Grind_finish___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__6);
v___x_1322_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__2));
v___x_1323_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1324_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v___x_1322_);
lean_ctor_set(v___x_1324_, 2, v___x_1321_);
return v___x_1324_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__11(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1335_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__10));
v___x_1336_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__7, &l_Lean_Parser_Tactic_Grind_finish___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__7);
v___x_1337_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1338_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v___x_1336_);
lean_ctor_set(v___x_1338_, 2, v___x_1335_);
return v___x_1338_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__12(void){
_start:
{
uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1339_ = 0;
v___x_1340_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__15));
v___x_1341_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__13));
v___x_1342_ = l_Lean_Parser_Tactic_grindParam;
v___x_1343_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v___x_1341_);
lean_ctor_set(v___x_1343_, 2, v___x_1340_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*3, v___x_1339_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__13(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__12, &l_Lean_Parser_Tactic_Grind_finish___closed__12_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__12);
v___x_1345_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5));
v___x_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___x_1344_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__14(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1347_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__13, &l_Lean_Parser_Tactic_Grind_finish___closed__13_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__13);
v___x_1348_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__12));
v___x_1349_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1350_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___x_1348_);
lean_ctor_set(v___x_1350_, 2, v___x_1347_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__15(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1351_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__20));
v___x_1352_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__14, &l_Lean_Parser_Tactic_Grind_finish___closed__14_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__14);
v___x_1353_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1354_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v___x_1352_);
lean_ctor_set(v___x_1354_, 2, v___x_1351_);
return v___x_1354_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__16(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__15, &l_Lean_Parser_Tactic_Grind_finish___closed__15_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__15);
v___x_1356_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__5));
v___x_1357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v___x_1355_);
return v___x_1357_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__17(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1358_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__16, &l_Lean_Parser_Tactic_Grind_finish___closed__16_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__16);
v___x_1359_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__11, &l_Lean_Parser_Tactic_Grind_finish___closed__11_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__11);
v___x_1360_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1361_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v___x_1359_);
lean_ctor_set(v___x_1361_, 2, v___x_1358_);
return v___x_1361_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__18(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1362_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__17, &l_Lean_Parser_Tactic_Grind_finish___closed__17_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__17);
v___x_1363_ = lean_unsigned_to_nat(1022u);
v___x_1364_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__1));
v___x_1365_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v___x_1363_);
lean_ctor_set(v___x_1365_, 2, v___x_1362_);
return v___x_1365_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish(void){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__18, &l_Lean_Parser_Tactic_Grind_finish___closed__18_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__18);
return v___x_1366_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__4(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1378_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__6, &l_Lean_Parser_Tactic_Grind_finish___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__6);
v___x_1379_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finishTrace___closed__3));
v___x_1380_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1381_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set(v___x_1381_, 1, v___x_1379_);
lean_ctor_set(v___x_1381_, 2, v___x_1378_);
return v___x_1381_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__5(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1382_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__10));
v___x_1383_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__4, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__4);
v___x_1384_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1385_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
lean_ctor_set(v___x_1385_, 1, v___x_1383_);
lean_ctor_set(v___x_1385_, 2, v___x_1382_);
return v___x_1385_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__6(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1386_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__16, &l_Lean_Parser_Tactic_Grind_finish___closed__16_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__16);
v___x_1387_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__5, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__5);
v___x_1388_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1389_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v___x_1387_);
lean_ctor_set(v___x_1389_, 2, v___x_1386_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__7(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1390_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__6, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__6);
v___x_1391_ = lean_unsigned_to_nat(1022u);
v___x_1392_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finishTrace___closed__1));
v___x_1393_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_ctor_set(v___x_1393_, 1, v___x_1391_);
lean_ctor_set(v___x_1393_, 2, v___x_1390_);
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace(void){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__7, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__7);
return v___x_1394_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__4(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = l_Lean_binderIdent;
v___x_1503_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__4));
v___x_1504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v___x_1502_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__5(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1505_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__4, &l_Lean_Parser_Tactic_Grind_next___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__4);
v___x_1506_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__3));
v___x_1507_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1508_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___x_1506_);
lean_ctor_set(v___x_1508_, 2, v___x_1505_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__6(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1509_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5));
v___x_1510_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__5, &l_Lean_Parser_Tactic_Grind_next___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__5);
v___x_1511_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1512_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v___x_1510_);
lean_ctor_set(v___x_1512_, 2, v___x_1509_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__7(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq));
v___x_1514_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__6, &l_Lean_Parser_Tactic_Grind_next___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__6);
v___x_1515_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1516_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v___x_1514_);
lean_ctor_set(v___x_1516_, 2, v___x_1513_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__8(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1517_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__7, &l_Lean_Parser_Tactic_Grind_next___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__7);
v___x_1518_ = lean_unsigned_to_nat(1022u);
v___x_1519_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__1));
v___x_1520_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v___x_1518_);
lean_ctor_set(v___x_1520_, 2, v___x_1517_);
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next(void){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__8, &l_Lean_Parser_Tactic_Grind_next___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__8);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1(lean_object* v_x_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1));
lean_inc(v_x_1545_);
v___x_1549_ = l_Lean_Syntax_isOfKind(v_x_1545_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec(v_x_1545_);
v___x_1550_ = lean_box(1);
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v_a_1547_);
return v___x_1551_;
}
else
{
lean_object* v_ref_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_ref_1552_ = lean_ctor_get(v_a_1546_, 5);
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = l_Lean_Syntax_getArg(v_x_1545_, v___x_1553_);
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = l_Lean_Syntax_getArg(v_x_1545_, v___x_1555_);
lean_dec(v_x_1545_);
v___x_1557_ = 0;
v___x_1558_ = l_Lean_SourceInfo_fromRef(v_ref_1552_, v___x_1557_);
v___x_1559_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__0));
v___x_1560_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__1));
v___x_1561_ = l_Lean_SourceInfo_fromRef(v___x_1554_, v___x_1549_);
lean_dec(v___x_1554_);
lean_inc(v___x_1561_);
v___x_1562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v___x_1559_);
v___x_1563_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_1564_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
lean_inc(v___x_1558_);
v___x_1565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1558_);
lean_ctor_set(v___x_1565_, 1, v___x_1563_);
lean_ctor_set(v___x_1565_, 2, v___x_1564_);
v___x_1566_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0));
v___x_1567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1561_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = l_Lean_Syntax_node4(v___x_1558_, v___x_1560_, v___x_1562_, v___x_1565_, v___x_1567_, v___x_1556_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
lean_ctor_set(v___x_1569_, 1, v_a_1547_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___boxed(lean_object* v_x_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1(v_x_1570_, v_a_1571_, v_a_1572_);
lean_dec_ref(v_a_1571_);
return v_res_1573_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case___closed__6(void){
_start:
{
uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1588_ = 0;
v___x_1589_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_case___closed__5));
v___x_1590_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_case___closed__4));
v___x_1591_ = l_Lean_Parser_Tactic_caseArg;
v___x_1592_ = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v___x_1590_);
lean_ctor_set(v___x_1592_, 2, v___x_1589_);
lean_ctor_set_uint8(v___x_1592_, sizeof(void*)*3, v___x_1588_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case___closed__7(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1593_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_case___closed__6, &l_Lean_Parser_Tactic_Grind_case___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_case___closed__6);
v___x_1594_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_case___closed__3));
v___x_1595_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1596_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v___x_1594_);
lean_ctor_set(v___x_1596_, 2, v___x_1593_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case___closed__8(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1597_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5));
v___x_1598_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_case___closed__7, &l_Lean_Parser_Tactic_Grind_case___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_case___closed__7);
v___x_1599_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1600_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v___x_1598_);
lean_ctor_set(v___x_1600_, 2, v___x_1597_);
return v___x_1600_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case___closed__9(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1601_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq));
v___x_1602_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_case___closed__8, &l_Lean_Parser_Tactic_Grind_case___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_case___closed__8);
v___x_1603_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1604_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v___x_1602_);
lean_ctor_set(v___x_1604_, 2, v___x_1601_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case___closed__10(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1605_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_case___closed__9, &l_Lean_Parser_Tactic_Grind_case___closed__9_once, _init_l_Lean_Parser_Tactic_Grind_case___closed__9);
v___x_1606_ = lean_unsigned_to_nat(1022u);
v___x_1607_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_case___closed__1));
v___x_1608_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v___x_1606_);
lean_ctor_set(v___x_1608_, 2, v___x_1605_);
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case(void){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_case___closed__10, &l_Lean_Parser_Tactic_Grind_case___closed__10_once, _init_l_Lean_Parser_Tactic_Grind_case___closed__10);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1(lean_object* v_x_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1692_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1));
lean_inc(v_x_1689_);
v___x_1693_ = l_Lean_Syntax_isOfKind(v_x_1689_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v_x_1689_);
v___x_1694_ = lean_box(1);
v___x_1695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v_a_1691_);
return v___x_1695_;
}
else
{
lean_object* v_ref_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_tk_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_ref_1696_ = lean_ctor_get(v_a_1690_, 5);
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = l_Lean_Syntax_getArg(v_x_1689_, v___x_1697_);
v___x_1699_ = lean_unsigned_to_nat(1u);
v_tk_1700_ = l_Lean_Syntax_getArg(v_x_1689_, v___x_1699_);
v___x_1701_ = lean_unsigned_to_nat(2u);
v___x_1702_ = l_Lean_Syntax_getArg(v_x_1689_, v___x_1701_);
lean_dec(v_x_1689_);
v___x_1703_ = 0;
v___x_1704_ = l_Lean_SourceInfo_fromRef(v_ref_1696_, v___x_1703_);
v___x_1705_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_focus___closed__0));
v___x_1706_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_focus___closed__1));
lean_inc_n(v___x_1704_, 18);
v___x_1707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1704_);
lean_ctor_set(v___x_1707_, 1, v___x_1705_);
v___x_1708_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1));
v___x_1709_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1));
v___x_1710_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_1711_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindStep___closed__1));
v___x_1712_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
v___x_1713_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1704_);
lean_ctor_set(v___x_1713_, 1, v___x_1710_);
lean_ctor_set(v___x_1713_, 2, v___x_1712_);
lean_inc_ref_n(v___x_1713_, 5);
v___x_1714_ = l_Lean_Syntax_node2(v___x_1704_, v___x_1711_, v___x_1698_, v___x_1713_);
v___x_1715_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1));
v___x_1716_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__0));
v___x_1717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1704_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__0));
v___x_1719_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__1));
v___x_1720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1704_);
lean_ctor_set(v___x_1720_, 1, v___x_1718_);
v___x_1721_ = l_Lean_Syntax_node1(v___x_1704_, v___x_1719_, v___x_1720_);
v___x_1722_ = l_Lean_Syntax_node3(v___x_1704_, v___x_1715_, v___x_1717_, v_tk_1700_, v___x_1721_);
v___x_1723_ = l_Lean_Syntax_node2(v___x_1704_, v___x_1711_, v___x_1722_, v___x_1713_);
v___x_1724_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_allGoals___closed__1));
v___x_1725_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__1));
v___x_1726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1704_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = l_Lean_Syntax_node2(v___x_1704_, v___x_1711_, v___x_1702_, v___x_1713_);
v___x_1728_ = l_Lean_Syntax_node1(v___x_1704_, v___x_1710_, v___x_1727_);
v___x_1729_ = l_Lean_Syntax_node1(v___x_1704_, v___x_1709_, v___x_1728_);
v___x_1730_ = l_Lean_Syntax_node1(v___x_1704_, v___x_1708_, v___x_1729_);
v___x_1731_ = l_Lean_Syntax_node2(v___x_1704_, v___x_1724_, v___x_1726_, v___x_1730_);
v___x_1732_ = l_Lean_Syntax_node2(v___x_1704_, v___x_1711_, v___x_1731_, v___x_1713_);
v___x_1733_ = l_Lean_Syntax_node5(v___x_1704_, v___x_1710_, v___x_1714_, v___x_1713_, v___x_1723_, v___x_1713_, v___x_1732_);
v___x_1734_ = l_Lean_Syntax_node1(v___x_1704_, v___x_1709_, v___x_1733_);
v___x_1735_ = l_Lean_Syntax_node1(v___x_1704_, v___x_1708_, v___x_1734_);
v___x_1736_ = l_Lean_Syntax_node2(v___x_1704_, v___x_1706_, v___x_1707_, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
lean_ctor_set(v___x_1737_, 1, v_a_1691_);
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___boxed(lean_object* v_x_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1(v_x_1738_, v_a_1739_, v_a_1740_);
lean_dec_ref(v_a_1739_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1(lean_object* v_x_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1));
lean_inc(v_x_1834_);
v___x_1838_ = l_Lean_Syntax_isOfKind(v_x_1834_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec(v_x_1834_);
v___x_1839_ = lean_box(1);
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
lean_ctor_set(v___x_1840_, 1, v_a_1836_);
return v___x_1840_;
}
else
{
lean_object* v_ref_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_ref_1841_ = lean_ctor_get(v_a_1835_, 5);
v___x_1842_ = lean_unsigned_to_nat(1u);
v___x_1843_ = l_Lean_Syntax_getArg(v_x_1834_, v___x_1842_);
lean_dec(v_x_1834_);
v___x_1844_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1));
v___x_1845_ = 0;
v___x_1846_ = l_Lean_SourceInfo_fromRef(v_ref_1841_, v___x_1845_);
v___x_1847_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__0));
v___x_1848_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__1));
lean_inc_n(v___x_1846_, 13);
v___x_1849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1846_);
lean_ctor_set(v___x_1849_, 1, v___x_1847_);
v___x_1850_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_1851_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__9));
v___x_1852_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
v___x_1853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1846_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
v___x_1855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1846_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
lean_inc_ref(v___x_1855_);
lean_inc_ref(v___x_1853_);
v___x_1856_ = l_Lean_Syntax_node3(v___x_1846_, v___x_1851_, v___x_1853_, v___x_1843_, v___x_1855_);
v___x_1857_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1));
v___x_1858_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindStep___closed__1));
v___x_1859_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__0));
v___x_1860_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__1));
v___x_1861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1846_);
lean_ctor_set(v___x_1861_, 1, v___x_1859_);
v___x_1862_ = l_Lean_Syntax_node1(v___x_1846_, v___x_1860_, v___x_1861_);
v___x_1863_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
v___x_1864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1846_);
lean_ctor_set(v___x_1864_, 1, v___x_1850_);
lean_ctor_set(v___x_1864_, 2, v___x_1863_);
v___x_1865_ = l_Lean_Syntax_node2(v___x_1846_, v___x_1858_, v___x_1862_, v___x_1864_);
v___x_1866_ = l_Lean_Syntax_node1(v___x_1846_, v___x_1850_, v___x_1865_);
v___x_1867_ = l_Lean_Syntax_node1(v___x_1846_, v___x_1857_, v___x_1866_);
v___x_1868_ = l_Lean_Syntax_node1(v___x_1846_, v___x_1844_, v___x_1867_);
v___x_1869_ = l_Lean_Syntax_node3(v___x_1846_, v___x_1851_, v___x_1853_, v___x_1868_, v___x_1855_);
v___x_1870_ = l_Lean_Syntax_node2(v___x_1846_, v___x_1850_, v___x_1856_, v___x_1869_);
v___x_1871_ = l_Lean_Syntax_node2(v___x_1846_, v___x_1848_, v___x_1849_, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_a_1836_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1___boxed(lean_object* v_x_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1(v_x_1873_, v_a_1874_, v_a_1875_);
lean_dec_ref(v_a_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1(lean_object* v_x_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1));
v___x_1917_ = l_Lean_Syntax_isOfKind(v_x_1913_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_box(1);
v___x_1919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v_a_1915_);
return v___x_1919_;
}
else
{
lean_object* v_ref_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_ref_1920_ = lean_ctor_get(v_a_1914_, 5);
v___x_1921_ = 0;
v___x_1922_ = l_Lean_SourceInfo_fromRef(v_ref_1920_, v___x_1921_);
v___x_1923_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_sorry___closed__0));
v___x_1924_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_sorry___closed__1));
lean_inc(v___x_1922_);
v___x_1925_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1922_);
lean_ctor_set(v___x_1925_, 1, v___x_1923_);
v___x_1926_ = l_Lean_Syntax_node1(v___x_1922_, v___x_1924_, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v_a_1915_);
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1___boxed(lean_object* v_x_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1(v_x_1928_, v_a_1929_, v_a_1930_);
lean_dec_ref(v_a_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1(lean_object* v_x_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1));
lean_inc(v_x_1985_);
v___x_1989_ = l_Lean_Syntax_isOfKind(v_x_1985_, v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec(v_x_1985_);
v___x_1990_ = lean_box(1);
v___x_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v_a_1987_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1992_ = lean_unsigned_to_nat(1u);
v___x_1993_ = l_Lean_Syntax_getArg(v_x_1985_, v___x_1992_);
lean_dec(v_x_1985_);
v___x_1994_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1));
lean_inc(v___x_1993_);
v___x_1995_ = l_Lean_Syntax_isOfKind(v___x_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(1);
v___x_1997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_a_1987_);
return v___x_1997_;
}
else
{
lean_object* v_ref_1998_; uint8_t v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v_ref_1998_ = lean_ctor_get(v_a_1986_, 5);
v___x_1999_ = 0;
v___x_2000_ = l_Lean_SourceInfo_fromRef(v_ref_1998_, v___x_1999_);
v___x_2001_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__0));
v___x_2002_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__1));
lean_inc_n(v___x_2000_, 22);
v___x_2003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2000_);
lean_ctor_set(v___x_2003_, 1, v___x_2001_);
v___x_2004_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_2005_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__9));
v___x_2006_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
v___x_2007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2000_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1));
v___x_2009_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindStep___closed__1));
v___x_2010_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_paren___closed__1));
v___x_2011_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
v___x_2012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2000_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
lean_inc_ref_n(v___x_2012_, 2);
lean_inc(v___x_1993_);
lean_inc_ref_n(v___x_2007_, 2);
v___x_2013_ = l_Lean_Syntax_node3(v___x_2000_, v___x_2010_, v___x_2007_, v___x_1993_, v___x_2012_);
v___x_2014_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
v___x_2015_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2000_);
lean_ctor_set(v___x_2015_, 1, v___x_2004_);
lean_ctor_set(v___x_2015_, 2, v___x_2014_);
lean_inc_ref_n(v___x_2015_, 2);
v___x_2016_ = l_Lean_Syntax_node2(v___x_2000_, v___x_2009_, v___x_2013_, v___x_2015_);
v___x_2017_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__0));
v___x_2018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2000_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
v___x_2019_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__1));
v___x_2020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2000_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = l_Lean_Syntax_node2(v___x_2000_, v___x_1988_, v___x_2020_, v___x_1993_);
v___x_2022_ = l_Lean_Syntax_node2(v___x_2000_, v___x_2009_, v___x_2021_, v___x_2015_);
v___x_2023_ = l_Lean_Syntax_node3(v___x_2000_, v___x_2004_, v___x_2016_, v___x_2018_, v___x_2022_);
v___x_2024_ = l_Lean_Syntax_node1(v___x_2000_, v___x_2008_, v___x_2023_);
v___x_2025_ = l_Lean_Syntax_node1(v___x_2000_, v___x_1994_, v___x_2024_);
v___x_2026_ = l_Lean_Syntax_node3(v___x_2000_, v___x_2005_, v___x_2007_, v___x_2025_, v___x_2012_);
v___x_2027_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__0));
v___x_2028_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__1));
v___x_2029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2000_);
lean_ctor_set(v___x_2029_, 1, v___x_2027_);
v___x_2030_ = l_Lean_Syntax_node1(v___x_2000_, v___x_2028_, v___x_2029_);
v___x_2031_ = l_Lean_Syntax_node2(v___x_2000_, v___x_2009_, v___x_2030_, v___x_2015_);
v___x_2032_ = l_Lean_Syntax_node1(v___x_2000_, v___x_2004_, v___x_2031_);
v___x_2033_ = l_Lean_Syntax_node1(v___x_2000_, v___x_2008_, v___x_2032_);
v___x_2034_ = l_Lean_Syntax_node1(v___x_2000_, v___x_1994_, v___x_2033_);
v___x_2035_ = l_Lean_Syntax_node3(v___x_2000_, v___x_2005_, v___x_2007_, v___x_2034_, v___x_2012_);
v___x_2036_ = l_Lean_Syntax_node2(v___x_2000_, v___x_2004_, v___x_2026_, v___x_2035_);
v___x_2037_ = l_Lean_Syntax_node2(v___x_2000_, v___x_2002_, v___x_2003_, v___x_2036_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set(v___x_2038_, 1, v_a_1987_);
return v___x_2038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___boxed(lean_object* v_x_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1(v_x_2039_, v_a_2040_, v_a_2041_);
lean_dec_ref(v_a_2040_);
return v_res_2042_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2058_ = l_Lean_binderIdent;
v___x_2059_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_renameI___closed__4));
v___x_2060_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2061_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v___x_2059_);
lean_ctor_set(v___x_2061_, 2, v___x_2058_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__6(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__5, &l_Lean_Parser_Tactic_Grind_renameI___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5);
v___x_2063_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__7));
v___x_2064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v___x_2062_);
return v___x_2064_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__7(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2065_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__6, &l_Lean_Parser_Tactic_Grind_renameI___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__6);
v___x_2066_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_renameI___closed__3));
v___x_2067_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2068_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v___x_2066_);
lean_ctor_set(v___x_2068_, 2, v___x_2065_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__8(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2069_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__7, &l_Lean_Parser_Tactic_Grind_renameI___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__7);
v___x_2070_ = lean_unsigned_to_nat(1022u);
v___x_2071_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_renameI___closed__1));
v___x_2072_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v___x_2070_);
lean_ctor_set(v___x_2072_, 2, v___x_2069_);
return v___x_2072_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI(void){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__8, &l_Lean_Parser_Tactic_Grind_renameI___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__8);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__4(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = l_Lean_Parser_Tactic_configItem;
v___x_2168_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__7));
v___x_2169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__5(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__4, &l_Lean_Parser_Tactic_Grind_setConfig___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__4);
v___x_2171_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_setConfig___closed__3));
v___x_2172_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2173_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
lean_ctor_set(v___x_2173_, 1, v___x_2171_);
lean_ctor_set(v___x_2173_, 2, v___x_2170_);
return v___x_2173_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__6(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2174_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_setOption___closed__18));
v___x_2175_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__5, &l_Lean_Parser_Tactic_Grind_setConfig___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__5);
v___x_2176_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2177_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___x_2175_);
lean_ctor_set(v___x_2177_, 2, v___x_2174_);
return v___x_2177_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__7(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2178_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq));
v___x_2179_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__6, &l_Lean_Parser_Tactic_Grind_setConfig___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__6);
v___x_2180_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2181_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v___x_2179_);
lean_ctor_set(v___x_2181_, 2, v___x_2178_);
return v___x_2181_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__8(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2182_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__7, &l_Lean_Parser_Tactic_Grind_setConfig___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__7);
v___x_2183_ = lean_unsigned_to_nat(1022u);
v___x_2184_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_setConfig___closed__1));
v___x_2185_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v___x_2183_);
lean_ctor_set(v___x_2185_, 2, v___x_2182_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig(void){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__8, &l_Lean_Parser_Tactic_Grind_setConfig___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__8);
return v___x_2186_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__5, &l_Lean_Parser_Tactic_Grind_renameI___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5);
v___x_2313_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__4));
v___x_2314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_ctor_set(v___x_2314_, 1, v___x_2312_);
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__26(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2315_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__25, &l_Lean_Parser_Tactic_Grind_symIntro___closed__25_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25);
v___x_2316_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__24));
v___x_2317_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2318_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v___x_2316_);
lean_ctor_set(v___x_2318_, 2, v___x_2315_);
return v___x_2318_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__27(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2319_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__26, &l_Lean_Parser_Tactic_Grind_symIntro___closed__26_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__26);
v___x_2320_ = lean_unsigned_to_nat(1022u);
v___x_2321_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__1));
v___x_2322_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v___x_2320_);
lean_ctor_set(v___x_2322_, 2, v___x_2319_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro(void){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__27, &l_Lean_Parser_Tactic_Grind_symIntro___closed__27_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__27);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2342_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__25, &l_Lean_Parser_Tactic_Grind_symIntro___closed__25_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25);
v___x_2343_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__5));
v___x_2344_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2345_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
lean_ctor_set(v___x_2345_, 1, v___x_2343_);
lean_ctor_set(v___x_2345_, 2, v___x_2342_);
return v___x_2345_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2346_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6, &l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6);
v___x_2347_ = lean_unsigned_to_nat(1022u);
v___x_2348_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1));
v___x_2349_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
lean_ctor_set(v___x_2349_, 1, v___x_2347_);
lean_ctor_set(v___x_2349_, 2, v___x_2346_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntroLight(void){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7, &l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1(lean_object* v_x_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2355_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1));
lean_inc(v_x_2352_);
v___x_2356_ = l_Lean_Syntax_isOfKind(v_x_2352_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_dec(v_x_2352_);
v___x_2357_ = lean_box(1);
v___x_2358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
lean_ctor_set(v___x_2358_, 1, v_a_2354_);
return v___x_2358_;
}
else
{
lean_object* v_ref_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v_ids_2362_; uint8_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v_ref_2359_ = lean_ctor_get(v_a_2353_, 5);
v___x_2360_ = lean_unsigned_to_nat(2u);
v___x_2361_ = l_Lean_Syntax_getArg(v_x_2352_, v___x_2360_);
lean_dec(v_x_2352_);
v_ids_2362_ = l_Lean_Syntax_getArgs(v___x_2361_);
lean_dec(v___x_2361_);
v___x_2363_ = 0;
v___x_2364_ = l_Lean_SourceInfo_fromRef(v_ref_2359_, v___x_2363_);
v___x_2365_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__1));
v___x_2366_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__2));
lean_inc_n(v___x_2364_, 9);
v___x_2367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2364_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_2369_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
v___x_2370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2364_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__5));
v___x_2372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2364_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0));
v___x_2374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2364_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__16));
v___x_2376_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__17));
v___x_2377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2364_);
lean_ctor_set(v___x_2377_, 1, v___x_2375_);
v___x_2378_ = l_Lean_Syntax_node1(v___x_2364_, v___x_2376_, v___x_2377_);
v___x_2379_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
v___x_2380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2364_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = l_Lean_Syntax_node5(v___x_2364_, v___x_2368_, v___x_2370_, v___x_2372_, v___x_2374_, v___x_2378_, v___x_2380_);
v___x_2382_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
v___x_2383_ = l_Array_appendCore___redArg(v___x_2382_, v_ids_2362_);
lean_dec_ref(v_ids_2362_);
v___x_2384_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2364_);
lean_ctor_set(v___x_2384_, 1, v___x_2368_);
lean_ctor_set(v___x_2384_, 2, v___x_2383_);
v___x_2385_ = l_Lean_Syntax_node3(v___x_2364_, v___x_2365_, v___x_2367_, v___x_2381_, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v_a_2354_);
return v___x_2386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___boxed(lean_object* v_x_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1(v_x_2387_, v_a_2388_, v_a_2389_);
lean_dec_ref(v_a_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1(lean_object* v_x_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2434_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1));
v___x_2435_ = l_Lean_Syntax_isOfKind(v_x_2431_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_box(1);
v___x_2437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
lean_ctor_set(v___x_2437_, 1, v_a_2433_);
return v___x_2437_;
}
else
{
lean_object* v_ref_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v_ref_2438_ = lean_ctor_get(v_a_2432_, 5);
v___x_2439_ = 0;
v___x_2440_ = l_Lean_SourceInfo_fromRef(v_ref_2438_, v___x_2439_);
v___x_2441_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntros___closed__1));
v___x_2442_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntros___closed__2));
lean_inc_n(v___x_2440_, 8);
v___x_2443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2440_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_2445_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
v___x_2446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2440_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__5));
v___x_2448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2440_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0));
v___x_2450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2440_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__16));
v___x_2452_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__17));
v___x_2453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2440_);
lean_ctor_set(v___x_2453_, 1, v___x_2451_);
v___x_2454_ = l_Lean_Syntax_node1(v___x_2440_, v___x_2452_, v___x_2453_);
v___x_2455_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
v___x_2456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2440_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = l_Lean_Syntax_node5(v___x_2440_, v___x_2444_, v___x_2446_, v___x_2448_, v___x_2450_, v___x_2454_, v___x_2456_);
v___x_2458_ = l_Lean_Syntax_node2(v___x_2440_, v___x_2441_, v___x_2443_, v___x_2457_);
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
lean_ctor_set(v___x_2459_, 1, v_a_2433_);
return v___x_2459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1___boxed(lean_object* v_x_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1(v_x_2460_, v_a_2461_, v_a_2462_);
lean_dec_ref(v_a_2461_);
return v_res_2463_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symRw___closed__4(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2651_ = l_Lean_Parser_Tactic_rwRuleSeq;
v___x_2652_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symRw___closed__3));
v___x_2653_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2654_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v___x_2652_);
lean_ctor_set(v___x_2654_, 2, v___x_2651_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symRw___closed__5(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2655_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symRw___closed__4, &l_Lean_Parser_Tactic_Grind_symRw___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_symRw___closed__4);
v___x_2656_ = lean_unsigned_to_nat(1022u);
v___x_2657_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symRw___closed__1));
v___x_2658_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
lean_ctor_set(v___x_2658_, 1, v___x_2656_);
lean_ctor_set(v___x_2658_, 2, v___x_2655_);
return v___x_2658_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symRw(void){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symRw___closed__5, &l_Lean_Parser_Tactic_Grind_symRw___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_symRw___closed__5);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1(lean_object* v_x_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2700_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1));
lean_inc(v_x_2697_);
v___x_2701_ = l_Lean_Syntax_isOfKind(v_x_2697_, v___x_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
lean_dec(v_x_2697_);
v___x_2702_ = lean_box(1);
v___x_2703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v_a_2699_);
return v___x_2703_;
}
else
{
lean_object* v_ref_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_ref_2704_ = lean_ctor_get(v_a_2698_, 5);
v___x_2705_ = lean_unsigned_to_nat(1u);
v___x_2706_ = l_Lean_Syntax_getArg(v_x_2697_, v___x_2705_);
lean_dec(v_x_2697_);
v___x_2707_ = 0;
v___x_2708_ = l_Lean_SourceInfo_fromRef(v_ref_2704_, v___x_2707_);
v___x_2709_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1));
v___x_2710_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2));
lean_inc_n(v___x_2708_, 7);
v___x_2711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2708_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0));
v___x_2713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2708_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0));
v___x_2715_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2));
v___x_2716_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_2717_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3));
v___x_2718_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4));
v___x_2719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2708_);
lean_ctor_set(v___x_2719_, 1, v___x_2717_);
v___x_2720_ = l_Lean_Syntax_node2(v___x_2708_, v___x_2718_, v___x_2719_, v___x_2706_);
v___x_2721_ = l_Lean_Syntax_node1(v___x_2708_, v___x_2716_, v___x_2720_);
v___x_2722_ = l_Lean_Syntax_node1(v___x_2708_, v___x_2715_, v___x_2721_);
v___x_2723_ = l_Lean_Syntax_node1(v___x_2708_, v___x_2714_, v___x_2722_);
v___x_2724_ = l_Lean_Syntax_node3(v___x_2708_, v___x_2709_, v___x_2711_, v___x_2713_, v___x_2723_);
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v_a_2699_);
return v___x_2725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___boxed(lean_object* v_x_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1(v_x_2726_, v_a_2727_, v_a_2728_);
lean_dec_ref(v_a_2727_);
return v_res_2729_;
}
}
lean_object* runtime_initialize_Init_Grind_Attr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Interactive(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Interactive(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Parser_Tactic_grindLemma = _init_l_Lean_Parser_Tactic_grindLemma();
lean_mark_persistent(l_Lean_Parser_Tactic_grindLemma);
l_Lean_Parser_Tactic_grindLemmaMin = _init_l_Lean_Parser_Tactic_grindLemmaMin();
lean_mark_persistent(l_Lean_Parser_Tactic_grindLemmaMin);
l_Lean_Parser_Tactic_grindParam = _init_l_Lean_Parser_Tactic_grindParam();
lean_mark_persistent(l_Lean_Parser_Tactic_grindParam);
l_Lean_Parser_Category_grind__filter = _init_l_Lean_Parser_Category_grind__filter();
lean_mark_persistent(l_Lean_Parser_Category_grind__filter);
l_Lean_Parser_Category_grind = _init_l_Lean_Parser_Category_grind();
lean_mark_persistent(l_Lean_Parser_Category_grind);
l_Lean_Parser_Tactic_Grind_thm = _init_l_Lean_Parser_Tactic_Grind_thm();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_thm);
l_Lean_Parser_Tactic_Grind_instantiate = _init_l_Lean_Parser_Tactic_Grind_instantiate();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_instantiate);
l_Lean_Parser_Tactic_Grind_use = _init_l_Lean_Parser_Tactic_Grind_use();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_use);
l_Lean_Parser_Category_grind__ref = _init_l_Lean_Parser_Category_grind__ref();
lean_mark_persistent(l_Lean_Parser_Category_grind__ref);
l_Lean_Parser_Tactic_Grind_finish = _init_l_Lean_Parser_Tactic_Grind_finish();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_finish);
l_Lean_Parser_Tactic_Grind_finishTrace = _init_l_Lean_Parser_Tactic_Grind_finishTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_finishTrace);
l_Lean_Parser_Tactic_Grind_next = _init_l_Lean_Parser_Tactic_Grind_next();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_next);
l_Lean_Parser_Tactic_Grind_case = _init_l_Lean_Parser_Tactic_Grind_case();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_case);
l_Lean_Parser_Tactic_Grind_renameI = _init_l_Lean_Parser_Tactic_Grind_renameI();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_renameI);
l_Lean_Parser_Tactic_Grind_setConfig = _init_l_Lean_Parser_Tactic_Grind_setConfig();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_setConfig);
l_Lean_Parser_Tactic_Grind_symIntro = _init_l_Lean_Parser_Tactic_Grind_symIntro();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_symIntro);
l_Lean_Parser_Tactic_Grind_symIntroLight = _init_l_Lean_Parser_Tactic_Grind_symIntroLight();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_symIntroLight);
l_Lean_Parser_Tactic_Grind_symRw = _init_l_Lean_Parser_Tactic_Grind_symRw();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_symRw);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Interactive(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Interactive(builtin);
}
#ifdef __cplusplus
}
#endif
