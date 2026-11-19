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
extern lean_object* l_Lean_Parser_Attr_grindMod;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_configItem;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_bvTypes;
extern lean_object* l_Lean_Parser_Tactic_optConfig;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
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
static const lean_string_object l_Lean_Parser_Tactic_grindParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l_Lean_Parser_Tactic_grindParam___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__4_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l_Lean_Parser_Tactic_grindParam___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_grindParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__17_value)}};
static const lean_object* l_Lean_Parser_Tactic_grindParam___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_grindParam___closed__6_value;
static lean_once_cell_t l_Lean_Parser_Tactic_grindParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_grindParam___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_grindParam___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_grindParam___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_grindParam___closed__10;
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
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_grindLemma___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindStep___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_grindStep___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_grindStep = (const lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__11_value;
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
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__11_value)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_Grind_grindStep___closed__11_value)}};
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
static const lean_string_object l_Lean_Parser_Tactic_Grind_symLiftLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "symLiftLets"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symLiftLets___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 83, 69, 73, 55, 43, 139, 70)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symLiftLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lift_lets"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symLiftLets___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLiftLets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symLiftLets___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLiftLets___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symLiftLets___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_symLiftLets = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLiftLets___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symLetToHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "symLetToHave"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symLetToHave___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 58, 253, 176, 149, 87, 6, 242)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_symLetToHave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let_to_have"};
static const lean_object* l_Lean_Parser_Tactic_Grind_symLetToHave___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLetToHave___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symLetToHave___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_symLetToHave___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_symLetToHave___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_Grind_symLetToHave = (const lean_object*)&l_Lean_Parser_Tactic_Grind_symLetToHave___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_bvNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvNormalize___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 26, 136, 123, 235, 182, 158, 80)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_bvNormalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvNormalize___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvNormalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvNormalize___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvNormalize___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvNormalize___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvNormalize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvNormalize___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvNormalize___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvNormalize___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_bvNormalize;
static const lean_string_object l_Lean_Parser_Tactic_Grind_bvDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bvDecide"};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvDecide___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecide___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecide___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecide___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecide___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecide___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecide___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecide___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecide___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecide___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 150, 103, 35, 70, 25, 10, 148)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvDecide___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecide___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_bvDecide___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvDecide___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecide___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecide___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvDecide___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecide___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvDecide___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvDecide___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvDecide___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvDecide___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvDecide___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvDecide___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_bvDecide;
static const lean_string_object l_Lean_Parser_Tactic_Grind_bvTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTrace"};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvTrace___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvTrace___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_bvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 142, 92, 236, 193, 5, 157, 115)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvTrace___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvTrace___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_bvTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "bv_decide\?"};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvTrace___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvTrace___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvTrace___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvTrace___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvTrace___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvTrace___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvTrace___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvTrace___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvTrace___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvTrace___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_bvTrace;
static const lean_string_object l_Lean_Parser_Tactic_Grind_bvCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvCheck___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvCheck___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvCheck___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvCheck___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvCheck___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvCheck___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvCheck___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvCheck___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvCheck___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvCheck___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_bvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 89, 115, 113, 62, 113, 141, 105)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvCheck___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvCheck___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_bvCheck___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_check"};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvCheck___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvCheck___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvCheck___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvCheck___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvCheck___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvCheck___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvCheck___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvCheck___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvCheck___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvCheck___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvCheck___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvCheck___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvCheck___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvCheck___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvCheck___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvCheck___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_bvCheck;
static const lean_string_object l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bvDecidePush"};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_anchor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 198, 224, 172, 164, 17, 35, 6)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "bv_decide_push"};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_bvDecidePush;
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
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__7(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = l_Lean_Parser_Tactic_grindLemma;
v___x_145_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__6));
v___x_146_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_147_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
lean_ctor_set(v___x_147_, 2, v___x_144_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__8(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_148_ = lean_obj_once(&l_Lean_Parser_Tactic_grindParam___closed__7, &l_Lean_Parser_Tactic_grindParam___closed__7_once, _init_l_Lean_Parser_Tactic_grindParam___closed__7);
v___x_149_ = l_Lean_Parser_Tactic_grindLemmaMin;
v___x_150_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_151_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
lean_ctor_set(v___x_151_, 2, v___x_148_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__9(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_152_ = lean_obj_once(&l_Lean_Parser_Tactic_grindParam___closed__8, &l_Lean_Parser_Tactic_grindParam___closed__8_once, _init_l_Lean_Parser_Tactic_grindParam___closed__8);
v___x_153_ = ((lean_object*)(l_Lean_Parser_Tactic_grindErase));
v___x_154_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_155_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_152_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam___closed__10(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = lean_obj_once(&l_Lean_Parser_Tactic_grindParam___closed__9, &l_Lean_Parser_Tactic_grindParam___closed__9_once, _init_l_Lean_Parser_Tactic_grindParam___closed__9);
v___x_157_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__1));
v___x_158_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__0));
v___x_159_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_156_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grindParam(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Lean_Parser_Tactic_grindParam___closed__10, &l_Lean_Parser_Tactic_grindParam___closed__10_once, _init_l_Lean_Parser_Tactic_grindParam___closed__10);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Parser_Category_grind__filter(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Parser_Category_grind(void){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(0);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_thm___closed__2(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_801_ = l_Lean_Parser_Tactic_grindLemma;
v___x_802_ = l_Lean_Parser_Tactic_grindLemmaMin;
v___x_803_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_804_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v___x_802_);
lean_ctor_set(v___x_804_, 2, v___x_801_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_thm___closed__3(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_805_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_thm___closed__2, &l_Lean_Parser_Tactic_Grind_thm___closed__2_once, _init_l_Lean_Parser_Tactic_Grind_thm___closed__2);
v___x_806_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_thmNs));
v___x_807_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_808_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
lean_ctor_set(v___x_808_, 2, v___x_805_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_thm___closed__4(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_809_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_thm___closed__3, &l_Lean_Parser_Tactic_Grind_thm___closed__3_once, _init_l_Lean_Parser_Tactic_Grind_thm___closed__3);
v___x_810_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor));
v___x_811_ = ((lean_object*)(l_Lean_Parser_Tactic_grindParam___closed__3));
v___x_812_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v___x_810_);
lean_ctor_set(v___x_812_, 2, v___x_809_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_thm___closed__5(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_813_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_thm___closed__4, &l_Lean_Parser_Tactic_Grind_thm___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_thm___closed__4);
v___x_814_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_thm___closed__1));
v___x_815_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_thm___closed__0));
v___x_816_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___x_814_);
lean_ctor_set(v___x_816_, 2, v___x_813_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_thm(void){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_thm___closed__5, &l_Lean_Parser_Tactic_Grind_thm___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_thm___closed__5);
return v___x_817_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__16(void){
_start:
{
uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_857_ = 1;
v___x_858_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__15));
v___x_859_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__13));
v___x_860_ = l_Lean_Parser_Tactic_Grind_thm;
v___x_861_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___x_859_);
lean_ctor_set(v___x_861_, 2, v___x_858_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3, v___x_857_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__17(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__16, &l_Lean_Parser_Tactic_Grind_instantiate___closed__16_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__16);
v___x_863_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5));
v___x_864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_862_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__18(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_865_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__17, &l_Lean_Parser_Tactic_Grind_instantiate___closed__17_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__17);
v___x_866_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__12));
v___x_867_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_868_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v___x_866_);
lean_ctor_set(v___x_868_, 2, v___x_865_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__21(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_872_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__20));
v___x_873_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__18, &l_Lean_Parser_Tactic_Grind_instantiate___closed__18_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__18);
v___x_874_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_875_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___x_873_);
lean_ctor_set(v___x_875_, 2, v___x_872_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__22(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__21, &l_Lean_Parser_Tactic_Grind_instantiate___closed__21_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__21);
v___x_877_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__5));
v___x_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_876_);
return v___x_878_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__23(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__22, &l_Lean_Parser_Tactic_Grind_instantiate___closed__22_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__22);
v___x_880_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__10));
v___x_881_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_882_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_880_);
lean_ctor_set(v___x_882_, 2, v___x_879_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__24(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_883_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__23, &l_Lean_Parser_Tactic_Grind_instantiate___closed__23_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__23);
v___x_884_ = lean_unsigned_to_nat(1022u);
v___x_885_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__1));
v___x_886_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
lean_ctor_set(v___x_886_, 2, v___x_883_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_instantiate(void){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__24, &l_Lean_Parser_Tactic_Grind_instantiate___closed__24_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__24);
return v___x_887_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_use___closed__4(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_902_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_instantiate___closed__17, &l_Lean_Parser_Tactic_Grind_instantiate___closed__17_once, _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__17);
v___x_903_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_use___closed__3));
v___x_904_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_905_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_903_);
lean_ctor_set(v___x_905_, 2, v___x_902_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_use___closed__5(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_906_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__20));
v___x_907_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_use___closed__4, &l_Lean_Parser_Tactic_Grind_use___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_use___closed__4);
v___x_908_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_909_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_907_);
lean_ctor_set(v___x_909_, 2, v___x_906_);
return v___x_909_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_use___closed__6(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_910_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_use___closed__5, &l_Lean_Parser_Tactic_Grind_use___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_use___closed__5);
v___x_911_ = lean_unsigned_to_nat(1024u);
v___x_912_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_use___closed__1));
v___x_913_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v___x_911_);
lean_ctor_set(v___x_913_, 2, v___x_910_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_use(void){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_use___closed__6, &l_Lean_Parser_Tactic_Grind_use___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_use___closed__6);
return v___x_914_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3(void){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Array_mkArray0___redArg();
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1(lean_object* v_x_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_use___closed__1));
lean_inc(v_x_921_);
v___x_925_ = l_Lean_Syntax_isOfKind(v_x_921_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_x_921_);
v___x_926_ = lean_box(1);
v___x_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_a_923_);
return v___x_927_;
}
else
{
lean_object* v_ref_928_; lean_object* v___x_929_; lean_object* v_u_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_ref_928_ = lean_ctor_get(v_a_922_, 5);
v___x_929_ = lean_unsigned_to_nat(0u);
v_u_930_ = l_Lean_Syntax_getArg(v_x_921_, v___x_929_);
v___x_931_ = lean_unsigned_to_nat(2u);
v___x_932_ = l_Lean_Syntax_getArg(v_x_921_, v___x_931_);
lean_dec(v_x_921_);
v___x_933_ = l_Lean_Syntax_getArgs(v___x_932_);
lean_dec(v___x_932_);
v___x_934_ = 0;
v___x_935_ = l_Lean_SourceInfo_fromRef(v_ref_928_, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__0));
v___x_937_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__1));
v___x_938_ = l_Lean_SourceInfo_fromRef(v_u_930_, v___x_925_);
lean_dec(v_u_930_);
v___x_939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_936_);
v___x_940_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_941_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__2));
lean_inc_n(v___x_935_, 7);
v___x_942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_935_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Lean_Syntax_node1(v___x_935_, v___x_940_, v___x_942_);
v___x_944_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
v___x_945_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_945_, 0, v___x_935_);
lean_ctor_set(v___x_945_, 1, v___x_940_);
lean_ctor_set(v___x_945_, 2, v___x_944_);
v___x_946_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__4));
v___x_947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_935_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = l_Array_appendCore___redArg(v___x_944_, v___x_933_);
lean_dec_ref(v___x_933_);
v___x_949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_949_, 0, v___x_935_);
lean_ctor_set(v___x_949_, 1, v___x_940_);
lean_ctor_set(v___x_949_, 2, v___x_948_);
v___x_950_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__19));
v___x_951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_935_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = l_Lean_Syntax_node3(v___x_935_, v___x_940_, v___x_947_, v___x_949_, v___x_951_);
v___x_953_ = l_Lean_Syntax_node4(v___x_935_, v___x_937_, v___x_939_, v___x_943_, v___x_945_, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v_a_923_);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___boxed(lean_object* v_x_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1(v_x_955_, v_a_956_, v_a_957_);
lean_dec_ref(v_a_956_);
return v_res_958_;
}
}
static lean_object* _init_l_Lean_Parser_Category_grind__ref(void){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_box(0);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__5(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1324_ = l_Lean_Parser_Tactic_configItem;
v___x_1325_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__8));
v___x_1326_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1327_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v___x_1325_);
lean_ctor_set(v___x_1327_, 2, v___x_1324_);
return v___x_1327_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__6(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__5, &l_Lean_Parser_Tactic_Grind_finish___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__5);
v___x_1329_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__4));
v___x_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v___x_1328_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__7(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1331_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__6, &l_Lean_Parser_Tactic_Grind_finish___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__6);
v___x_1332_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__2));
v___x_1333_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1334_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1332_);
lean_ctor_set(v___x_1334_, 2, v___x_1331_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__11(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1345_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__10));
v___x_1346_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__7, &l_Lean_Parser_Tactic_Grind_finish___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__7);
v___x_1347_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1348_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v___x_1346_);
lean_ctor_set(v___x_1348_, 2, v___x_1345_);
return v___x_1348_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__12(void){
_start:
{
uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1349_ = 0;
v___x_1350_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__15));
v___x_1351_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__13));
v___x_1352_ = l_Lean_Parser_Tactic_grindParam;
v___x_1353_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v___x_1351_);
lean_ctor_set(v___x_1353_, 2, v___x_1350_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3, v___x_1349_);
return v___x_1353_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__13(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__12, &l_Lean_Parser_Tactic_Grind_finish___closed__12_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__12);
v___x_1355_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5));
v___x_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set(v___x_1356_, 1, v___x_1354_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__14(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1357_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__13, &l_Lean_Parser_Tactic_Grind_finish___closed__13_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__13);
v___x_1358_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__12));
v___x_1359_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1360_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v___x_1358_);
lean_ctor_set(v___x_1360_, 2, v___x_1357_);
return v___x_1360_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__15(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1361_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__20));
v___x_1362_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__14, &l_Lean_Parser_Tactic_Grind_finish___closed__14_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__14);
v___x_1363_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1364_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v___x_1362_);
lean_ctor_set(v___x_1364_, 2, v___x_1361_);
return v___x_1364_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__16(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__15, &l_Lean_Parser_Tactic_Grind_finish___closed__15_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__15);
v___x_1366_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__5));
v___x_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v___x_1365_);
return v___x_1367_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__17(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1368_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__16, &l_Lean_Parser_Tactic_Grind_finish___closed__16_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__16);
v___x_1369_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__11, &l_Lean_Parser_Tactic_Grind_finish___closed__11_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__11);
v___x_1370_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1371_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v___x_1369_);
lean_ctor_set(v___x_1371_, 2, v___x_1368_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__18(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1372_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__17, &l_Lean_Parser_Tactic_Grind_finish___closed__17_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__17);
v___x_1373_ = lean_unsigned_to_nat(1022u);
v___x_1374_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__1));
v___x_1375_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___x_1373_);
lean_ctor_set(v___x_1375_, 2, v___x_1372_);
return v___x_1375_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish(void){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__18, &l_Lean_Parser_Tactic_Grind_finish___closed__18_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__18);
return v___x_1376_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__4(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1388_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__6, &l_Lean_Parser_Tactic_Grind_finish___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__6);
v___x_1389_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finishTrace___closed__3));
v___x_1390_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1391_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v___x_1389_);
lean_ctor_set(v___x_1391_, 2, v___x_1388_);
return v___x_1391_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__5(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1392_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__10));
v___x_1393_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__4, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__4);
v___x_1394_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1395_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v___x_1393_);
lean_ctor_set(v___x_1395_, 2, v___x_1392_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__6(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__16, &l_Lean_Parser_Tactic_Grind_finish___closed__16_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__16);
v___x_1397_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__5, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__5);
v___x_1398_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1399_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
lean_ctor_set(v___x_1399_, 1, v___x_1397_);
lean_ctor_set(v___x_1399_, 2, v___x_1396_);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__7(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1400_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__6, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__6);
v___x_1401_ = lean_unsigned_to_nat(1022u);
v___x_1402_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finishTrace___closed__1));
v___x_1403_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
lean_ctor_set(v___x_1403_, 1, v___x_1401_);
lean_ctor_set(v___x_1403_, 2, v___x_1400_);
return v___x_1403_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace(void){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__7, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__7);
return v___x_1404_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__4(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = l_Lean_binderIdent;
v___x_1513_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__4));
v___x_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___x_1512_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__5(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1515_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__4, &l_Lean_Parser_Tactic_Grind_next___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__4);
v___x_1516_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__3));
v___x_1517_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1518_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___x_1516_);
lean_ctor_set(v___x_1518_, 2, v___x_1515_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__6(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1519_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5));
v___x_1520_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__5, &l_Lean_Parser_Tactic_Grind_next___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__5);
v___x_1521_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1522_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v___x_1520_);
lean_ctor_set(v___x_1522_, 2, v___x_1519_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__7(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq));
v___x_1524_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__6, &l_Lean_Parser_Tactic_Grind_next___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__6);
v___x_1525_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1526_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1524_);
lean_ctor_set(v___x_1526_, 2, v___x_1523_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__8(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1527_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__7, &l_Lean_Parser_Tactic_Grind_next___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__7);
v___x_1528_ = lean_unsigned_to_nat(1022u);
v___x_1529_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__1));
v___x_1530_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v___x_1528_);
lean_ctor_set(v___x_1530_, 2, v___x_1527_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next(void){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__8, &l_Lean_Parser_Tactic_Grind_next___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__8);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1(lean_object* v_x_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1));
lean_inc(v_x_1555_);
v___x_1559_ = l_Lean_Syntax_isOfKind(v_x_1555_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v_x_1555_);
v___x_1560_ = lean_box(1);
v___x_1561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v_a_1557_);
return v___x_1561_;
}
else
{
lean_object* v_ref_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_ref_1562_ = lean_ctor_get(v_a_1556_, 5);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = l_Lean_Syntax_getArg(v_x_1555_, v___x_1563_);
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = l_Lean_Syntax_getArg(v_x_1555_, v___x_1565_);
lean_dec(v_x_1555_);
v___x_1567_ = 0;
v___x_1568_ = l_Lean_SourceInfo_fromRef(v_ref_1562_, v___x_1567_);
v___x_1569_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__0));
v___x_1570_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__1));
v___x_1571_ = l_Lean_SourceInfo_fromRef(v___x_1564_, v___x_1559_);
lean_dec(v___x_1564_);
lean_inc(v___x_1571_);
v___x_1572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___x_1569_);
v___x_1573_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_1574_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
lean_inc(v___x_1568_);
v___x_1575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1568_);
lean_ctor_set(v___x_1575_, 1, v___x_1573_);
lean_ctor_set(v___x_1575_, 2, v___x_1574_);
v___x_1576_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0));
v___x_1577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1571_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_Syntax_node4(v___x_1568_, v___x_1570_, v___x_1572_, v___x_1575_, v___x_1577_, v___x_1566_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v_a_1557_);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___boxed(lean_object* v_x_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1(v_x_1580_, v_a_1581_, v_a_1582_);
lean_dec_ref(v_a_1581_);
return v_res_1583_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case___closed__6(void){
_start:
{
uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1598_ = 0;
v___x_1599_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_case___closed__5));
v___x_1600_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_case___closed__4));
v___x_1601_ = l_Lean_Parser_Tactic_caseArg;
v___x_1602_ = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___x_1600_);
lean_ctor_set(v___x_1602_, 2, v___x_1599_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3, v___x_1598_);
return v___x_1602_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case___closed__7(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1603_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_case___closed__6, &l_Lean_Parser_Tactic_Grind_case___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_case___closed__6);
v___x_1604_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_case___closed__3));
v___x_1605_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1606_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___x_1604_);
lean_ctor_set(v___x_1606_, 2, v___x_1603_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case___closed__8(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1607_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5));
v___x_1608_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_case___closed__7, &l_Lean_Parser_Tactic_Grind_case___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_case___closed__7);
v___x_1609_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1610_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___x_1608_);
lean_ctor_set(v___x_1610_, 2, v___x_1607_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case___closed__9(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1611_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq));
v___x_1612_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_case___closed__8, &l_Lean_Parser_Tactic_Grind_case___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_case___closed__8);
v___x_1613_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1614_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v___x_1612_);
lean_ctor_set(v___x_1614_, 2, v___x_1611_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case___closed__10(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1615_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_case___closed__9, &l_Lean_Parser_Tactic_Grind_case___closed__9_once, _init_l_Lean_Parser_Tactic_Grind_case___closed__9);
v___x_1616_ = lean_unsigned_to_nat(1022u);
v___x_1617_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_case___closed__1));
v___x_1618_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v___x_1616_);
lean_ctor_set(v___x_1618_, 2, v___x_1615_);
return v___x_1618_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_case(void){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_case___closed__10, &l_Lean_Parser_Tactic_Grind_case___closed__10_once, _init_l_Lean_Parser_Tactic_Grind_case___closed__10);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1(lean_object* v_x_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1));
lean_inc(v_x_1699_);
v___x_1703_ = l_Lean_Syntax_isOfKind(v_x_1699_, v___x_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v_x_1699_);
v___x_1704_ = lean_box(1);
v___x_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v_a_1701_);
return v___x_1705_;
}
else
{
lean_object* v_ref_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v_tk_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_ref_1706_ = lean_ctor_get(v_a_1700_, 5);
v___x_1707_ = lean_unsigned_to_nat(0u);
v___x_1708_ = l_Lean_Syntax_getArg(v_x_1699_, v___x_1707_);
v___x_1709_ = lean_unsigned_to_nat(1u);
v_tk_1710_ = l_Lean_Syntax_getArg(v_x_1699_, v___x_1709_);
v___x_1711_ = lean_unsigned_to_nat(2u);
v___x_1712_ = l_Lean_Syntax_getArg(v_x_1699_, v___x_1711_);
lean_dec(v_x_1699_);
v___x_1713_ = 0;
v___x_1714_ = l_Lean_SourceInfo_fromRef(v_ref_1706_, v___x_1713_);
v___x_1715_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_focus___closed__0));
v___x_1716_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_focus___closed__1));
lean_inc_n(v___x_1714_, 18);
v___x_1717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1714_);
lean_ctor_set(v___x_1717_, 1, v___x_1715_);
v___x_1718_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1));
v___x_1719_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1));
v___x_1720_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_1721_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindStep___closed__1));
v___x_1722_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
v___x_1723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1714_);
lean_ctor_set(v___x_1723_, 1, v___x_1720_);
lean_ctor_set(v___x_1723_, 2, v___x_1722_);
lean_inc_ref_n(v___x_1723_, 5);
v___x_1724_ = l_Lean_Syntax_node2(v___x_1714_, v___x_1721_, v___x_1708_, v___x_1723_);
v___x_1725_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1));
v___x_1726_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__0));
v___x_1727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1714_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__0));
v___x_1729_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__1));
v___x_1730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1714_);
lean_ctor_set(v___x_1730_, 1, v___x_1728_);
v___x_1731_ = l_Lean_Syntax_node1(v___x_1714_, v___x_1729_, v___x_1730_);
v___x_1732_ = l_Lean_Syntax_node3(v___x_1714_, v___x_1725_, v___x_1727_, v_tk_1710_, v___x_1731_);
v___x_1733_ = l_Lean_Syntax_node2(v___x_1714_, v___x_1721_, v___x_1732_, v___x_1723_);
v___x_1734_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_allGoals___closed__1));
v___x_1735_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__1));
v___x_1736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1714_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = l_Lean_Syntax_node2(v___x_1714_, v___x_1721_, v___x_1712_, v___x_1723_);
v___x_1738_ = l_Lean_Syntax_node1(v___x_1714_, v___x_1720_, v___x_1737_);
v___x_1739_ = l_Lean_Syntax_node1(v___x_1714_, v___x_1719_, v___x_1738_);
v___x_1740_ = l_Lean_Syntax_node1(v___x_1714_, v___x_1718_, v___x_1739_);
v___x_1741_ = l_Lean_Syntax_node2(v___x_1714_, v___x_1734_, v___x_1736_, v___x_1740_);
v___x_1742_ = l_Lean_Syntax_node2(v___x_1714_, v___x_1721_, v___x_1741_, v___x_1723_);
v___x_1743_ = l_Lean_Syntax_node5(v___x_1714_, v___x_1720_, v___x_1724_, v___x_1723_, v___x_1733_, v___x_1723_, v___x_1742_);
v___x_1744_ = l_Lean_Syntax_node1(v___x_1714_, v___x_1719_, v___x_1743_);
v___x_1745_ = l_Lean_Syntax_node1(v___x_1714_, v___x_1718_, v___x_1744_);
v___x_1746_ = l_Lean_Syntax_node2(v___x_1714_, v___x_1716_, v___x_1717_, v___x_1745_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v_a_1701_);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___boxed(lean_object* v_x_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1(v_x_1748_, v_a_1749_, v_a_1750_);
lean_dec_ref(v_a_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1(lean_object* v_x_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1));
lean_inc(v_x_1844_);
v___x_1848_ = l_Lean_Syntax_isOfKind(v_x_1844_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
lean_dec(v_x_1844_);
v___x_1849_ = lean_box(1);
v___x_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v_a_1846_);
return v___x_1850_;
}
else
{
lean_object* v_ref_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_ref_1851_ = lean_ctor_get(v_a_1845_, 5);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = l_Lean_Syntax_getArg(v_x_1844_, v___x_1852_);
lean_dec(v_x_1844_);
v___x_1854_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1));
v___x_1855_ = 0;
v___x_1856_ = l_Lean_SourceInfo_fromRef(v_ref_1851_, v___x_1855_);
v___x_1857_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__0));
v___x_1858_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__1));
lean_inc_n(v___x_1856_, 13);
v___x_1859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1856_);
lean_ctor_set(v___x_1859_, 1, v___x_1857_);
v___x_1860_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_1861_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__9));
v___x_1862_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
v___x_1863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1856_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
v___x_1865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1856_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
lean_inc_ref(v___x_1865_);
lean_inc_ref(v___x_1863_);
v___x_1866_ = l_Lean_Syntax_node3(v___x_1856_, v___x_1861_, v___x_1863_, v___x_1853_, v___x_1865_);
v___x_1867_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1));
v___x_1868_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindStep___closed__1));
v___x_1869_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__0));
v___x_1870_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__1));
v___x_1871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1856_);
lean_ctor_set(v___x_1871_, 1, v___x_1869_);
v___x_1872_ = l_Lean_Syntax_node1(v___x_1856_, v___x_1870_, v___x_1871_);
v___x_1873_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
v___x_1874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1856_);
lean_ctor_set(v___x_1874_, 1, v___x_1860_);
lean_ctor_set(v___x_1874_, 2, v___x_1873_);
v___x_1875_ = l_Lean_Syntax_node2(v___x_1856_, v___x_1868_, v___x_1872_, v___x_1874_);
v___x_1876_ = l_Lean_Syntax_node1(v___x_1856_, v___x_1860_, v___x_1875_);
v___x_1877_ = l_Lean_Syntax_node1(v___x_1856_, v___x_1867_, v___x_1876_);
v___x_1878_ = l_Lean_Syntax_node1(v___x_1856_, v___x_1854_, v___x_1877_);
v___x_1879_ = l_Lean_Syntax_node3(v___x_1856_, v___x_1861_, v___x_1863_, v___x_1878_, v___x_1865_);
v___x_1880_ = l_Lean_Syntax_node2(v___x_1856_, v___x_1860_, v___x_1866_, v___x_1879_);
v___x_1881_ = l_Lean_Syntax_node2(v___x_1856_, v___x_1858_, v___x_1859_, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v_a_1846_);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1___boxed(lean_object* v_x_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1(v_x_1883_, v_a_1884_, v_a_1885_);
lean_dec_ref(v_a_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1(lean_object* v_x_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1926_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1));
v___x_1927_ = l_Lean_Syntax_isOfKind(v_x_1923_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_box(1);
v___x_1929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v_a_1925_);
return v___x_1929_;
}
else
{
lean_object* v_ref_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_ref_1930_ = lean_ctor_get(v_a_1924_, 5);
v___x_1931_ = 0;
v___x_1932_ = l_Lean_SourceInfo_fromRef(v_ref_1930_, v___x_1931_);
v___x_1933_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_sorry___closed__0));
v___x_1934_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_sorry___closed__1));
lean_inc(v___x_1932_);
v___x_1935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1932_);
lean_ctor_set(v___x_1935_, 1, v___x_1933_);
v___x_1936_ = l_Lean_Syntax_node1(v___x_1932_, v___x_1934_, v___x_1935_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v_a_1925_);
return v___x_1937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1___boxed(lean_object* v_x_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1(v_x_1938_, v_a_1939_, v_a_1940_);
lean_dec_ref(v_a_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1(lean_object* v_x_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1));
lean_inc(v_x_1995_);
v___x_1999_ = l_Lean_Syntax_isOfKind(v_x_1995_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec(v_x_1995_);
v___x_2000_ = lean_box(1);
v___x_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v_a_1997_);
return v___x_2001_;
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2002_ = lean_unsigned_to_nat(1u);
v___x_2003_ = l_Lean_Syntax_getArg(v_x_1995_, v___x_2002_);
lean_dec(v_x_1995_);
v___x_2004_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1));
lean_inc(v___x_2003_);
v___x_2005_ = l_Lean_Syntax_isOfKind(v___x_2003_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(1);
v___x_2007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v_a_1997_);
return v___x_2007_;
}
else
{
lean_object* v_ref_2008_; uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_ref_2008_ = lean_ctor_get(v_a_1996_, 5);
v___x_2009_ = 0;
v___x_2010_ = l_Lean_SourceInfo_fromRef(v_ref_2008_, v___x_2009_);
v___x_2011_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__0));
v___x_2012_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__1));
lean_inc_n(v___x_2010_, 22);
v___x_2013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2010_);
lean_ctor_set(v___x_2013_, 1, v___x_2011_);
v___x_2014_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_2015_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__9));
v___x_2016_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
v___x_2017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2010_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1));
v___x_2019_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindStep___closed__1));
v___x_2020_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_paren___closed__1));
v___x_2021_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
v___x_2022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2010_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
lean_inc_ref_n(v___x_2022_, 2);
lean_inc(v___x_2003_);
lean_inc_ref_n(v___x_2017_, 2);
v___x_2023_ = l_Lean_Syntax_node3(v___x_2010_, v___x_2020_, v___x_2017_, v___x_2003_, v___x_2022_);
v___x_2024_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
v___x_2025_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2010_);
lean_ctor_set(v___x_2025_, 1, v___x_2014_);
lean_ctor_set(v___x_2025_, 2, v___x_2024_);
lean_inc_ref_n(v___x_2025_, 2);
v___x_2026_ = l_Lean_Syntax_node2(v___x_2010_, v___x_2019_, v___x_2023_, v___x_2025_);
v___x_2027_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__0));
v___x_2028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2010_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__1));
v___x_2030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2010_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = l_Lean_Syntax_node2(v___x_2010_, v___x_1998_, v___x_2030_, v___x_2003_);
v___x_2032_ = l_Lean_Syntax_node2(v___x_2010_, v___x_2019_, v___x_2031_, v___x_2025_);
v___x_2033_ = l_Lean_Syntax_node3(v___x_2010_, v___x_2014_, v___x_2026_, v___x_2028_, v___x_2032_);
v___x_2034_ = l_Lean_Syntax_node1(v___x_2010_, v___x_2018_, v___x_2033_);
v___x_2035_ = l_Lean_Syntax_node1(v___x_2010_, v___x_2004_, v___x_2034_);
v___x_2036_ = l_Lean_Syntax_node3(v___x_2010_, v___x_2015_, v___x_2017_, v___x_2035_, v___x_2022_);
v___x_2037_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__0));
v___x_2038_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__1));
v___x_2039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2010_);
lean_ctor_set(v___x_2039_, 1, v___x_2037_);
v___x_2040_ = l_Lean_Syntax_node1(v___x_2010_, v___x_2038_, v___x_2039_);
v___x_2041_ = l_Lean_Syntax_node2(v___x_2010_, v___x_2019_, v___x_2040_, v___x_2025_);
v___x_2042_ = l_Lean_Syntax_node1(v___x_2010_, v___x_2014_, v___x_2041_);
v___x_2043_ = l_Lean_Syntax_node1(v___x_2010_, v___x_2018_, v___x_2042_);
v___x_2044_ = l_Lean_Syntax_node1(v___x_2010_, v___x_2004_, v___x_2043_);
v___x_2045_ = l_Lean_Syntax_node3(v___x_2010_, v___x_2015_, v___x_2017_, v___x_2044_, v___x_2022_);
v___x_2046_ = l_Lean_Syntax_node2(v___x_2010_, v___x_2014_, v___x_2036_, v___x_2045_);
v___x_2047_ = l_Lean_Syntax_node2(v___x_2010_, v___x_2012_, v___x_2013_, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
lean_ctor_set(v___x_2048_, 1, v_a_1997_);
return v___x_2048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___boxed(lean_object* v_x_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1(v_x_2049_, v_a_2050_, v_a_2051_);
lean_dec_ref(v_a_2050_);
return v_res_2052_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = l_Lean_binderIdent;
v___x_2069_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_renameI___closed__4));
v___x_2070_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2071_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___x_2069_);
lean_ctor_set(v___x_2071_, 2, v___x_2068_);
return v___x_2071_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__6(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__5, &l_Lean_Parser_Tactic_Grind_renameI___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5);
v___x_2073_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__7));
v___x_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_ctor_set(v___x_2074_, 1, v___x_2072_);
return v___x_2074_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__7(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2075_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__6, &l_Lean_Parser_Tactic_Grind_renameI___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__6);
v___x_2076_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_renameI___closed__3));
v___x_2077_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2078_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___x_2076_);
lean_ctor_set(v___x_2078_, 2, v___x_2075_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__8(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2079_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__7, &l_Lean_Parser_Tactic_Grind_renameI___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__7);
v___x_2080_ = lean_unsigned_to_nat(1022u);
v___x_2081_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_renameI___closed__1));
v___x_2082_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v___x_2080_);
lean_ctor_set(v___x_2082_, 2, v___x_2079_);
return v___x_2082_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI(void){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__8, &l_Lean_Parser_Tactic_Grind_renameI___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__8);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__4(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = l_Lean_Parser_Tactic_configItem;
v___x_2178_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__7));
v___x_2179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v___x_2177_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__5(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__4, &l_Lean_Parser_Tactic_Grind_setConfig___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__4);
v___x_2181_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_setConfig___closed__3));
v___x_2182_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2183_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v___x_2181_);
lean_ctor_set(v___x_2183_, 2, v___x_2180_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__6(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2184_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_setOption___closed__18));
v___x_2185_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__5, &l_Lean_Parser_Tactic_Grind_setConfig___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__5);
v___x_2186_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2187_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v___x_2185_);
lean_ctor_set(v___x_2187_, 2, v___x_2184_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__7(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2188_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq));
v___x_2189_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__6, &l_Lean_Parser_Tactic_Grind_setConfig___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__6);
v___x_2190_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2191_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v___x_2189_);
lean_ctor_set(v___x_2191_, 2, v___x_2188_);
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__8(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2192_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__7, &l_Lean_Parser_Tactic_Grind_setConfig___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__7);
v___x_2193_ = lean_unsigned_to_nat(1022u);
v___x_2194_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_setConfig___closed__1));
v___x_2195_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v___x_2193_);
lean_ctor_set(v___x_2195_, 2, v___x_2192_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig(void){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__8, &l_Lean_Parser_Tactic_Grind_setConfig___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__8);
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__5, &l_Lean_Parser_Tactic_Grind_renameI___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5);
v___x_2323_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__4));
v___x_2324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
lean_ctor_set(v___x_2324_, 1, v___x_2322_);
return v___x_2324_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__26(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2325_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__25, &l_Lean_Parser_Tactic_Grind_symIntro___closed__25_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25);
v___x_2326_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__24));
v___x_2327_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2328_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
lean_ctor_set(v___x_2328_, 1, v___x_2326_);
lean_ctor_set(v___x_2328_, 2, v___x_2325_);
return v___x_2328_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__27(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2329_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__26, &l_Lean_Parser_Tactic_Grind_symIntro___closed__26_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__26);
v___x_2330_ = lean_unsigned_to_nat(1022u);
v___x_2331_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__1));
v___x_2332_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___x_2330_);
lean_ctor_set(v___x_2332_, 2, v___x_2329_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro(void){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__27, &l_Lean_Parser_Tactic_Grind_symIntro___closed__27_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__27);
return v___x_2333_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2352_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__25, &l_Lean_Parser_Tactic_Grind_symIntro___closed__25_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25);
v___x_2353_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__5));
v___x_2354_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2355_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
lean_ctor_set(v___x_2355_, 1, v___x_2353_);
lean_ctor_set(v___x_2355_, 2, v___x_2352_);
return v___x_2355_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2356_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6, &l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6);
v___x_2357_ = lean_unsigned_to_nat(1022u);
v___x_2358_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1));
v___x_2359_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v___x_2357_);
lean_ctor_set(v___x_2359_, 2, v___x_2356_);
return v___x_2359_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntroLight(void){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7, &l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1(lean_object* v_x_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1));
lean_inc(v_x_2362_);
v___x_2366_ = l_Lean_Syntax_isOfKind(v_x_2362_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_dec(v_x_2362_);
v___x_2367_ = lean_box(1);
v___x_2368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set(v___x_2368_, 1, v_a_2364_);
return v___x_2368_;
}
else
{
lean_object* v_ref_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v_ids_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_ref_2369_ = lean_ctor_get(v_a_2363_, 5);
v___x_2370_ = lean_unsigned_to_nat(2u);
v___x_2371_ = l_Lean_Syntax_getArg(v_x_2362_, v___x_2370_);
lean_dec(v_x_2362_);
v_ids_2372_ = l_Lean_Syntax_getArgs(v___x_2371_);
lean_dec(v___x_2371_);
v___x_2373_ = 0;
v___x_2374_ = l_Lean_SourceInfo_fromRef(v_ref_2369_, v___x_2373_);
v___x_2375_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__1));
v___x_2376_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__2));
lean_inc_n(v___x_2374_, 9);
v___x_2377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2374_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_2379_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
v___x_2380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2374_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__5));
v___x_2382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2374_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0));
v___x_2384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2374_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__16));
v___x_2386_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__17));
v___x_2387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2374_);
lean_ctor_set(v___x_2387_, 1, v___x_2385_);
v___x_2388_ = l_Lean_Syntax_node1(v___x_2374_, v___x_2386_, v___x_2387_);
v___x_2389_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
v___x_2390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2374_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = l_Lean_Syntax_node5(v___x_2374_, v___x_2378_, v___x_2380_, v___x_2382_, v___x_2384_, v___x_2388_, v___x_2390_);
v___x_2392_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
v___x_2393_ = l_Array_appendCore___redArg(v___x_2392_, v_ids_2372_);
lean_dec_ref(v_ids_2372_);
v___x_2394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2374_);
lean_ctor_set(v___x_2394_, 1, v___x_2378_);
lean_ctor_set(v___x_2394_, 2, v___x_2393_);
v___x_2395_ = l_Lean_Syntax_node3(v___x_2374_, v___x_2375_, v___x_2377_, v___x_2391_, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v_a_2364_);
return v___x_2396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___boxed(lean_object* v_x_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1(v_x_2397_, v_a_2398_, v_a_2399_);
lean_dec_ref(v_a_2398_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1(lean_object* v_x_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1));
v___x_2445_ = l_Lean_Syntax_isOfKind(v_x_2441_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_box(1);
v___x_2447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
lean_ctor_set(v___x_2447_, 1, v_a_2443_);
return v___x_2447_;
}
else
{
lean_object* v_ref_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v_ref_2448_ = lean_ctor_get(v_a_2442_, 5);
v___x_2449_ = 0;
v___x_2450_ = l_Lean_SourceInfo_fromRef(v_ref_2448_, v___x_2449_);
v___x_2451_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntros___closed__1));
v___x_2452_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntros___closed__2));
lean_inc_n(v___x_2450_, 8);
v___x_2453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2450_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_2455_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
v___x_2456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2450_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__5));
v___x_2458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2450_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0));
v___x_2460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2450_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__16));
v___x_2462_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__17));
v___x_2463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2450_);
lean_ctor_set(v___x_2463_, 1, v___x_2461_);
v___x_2464_ = l_Lean_Syntax_node1(v___x_2450_, v___x_2462_, v___x_2463_);
v___x_2465_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
v___x_2466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2450_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = l_Lean_Syntax_node5(v___x_2450_, v___x_2454_, v___x_2456_, v___x_2458_, v___x_2460_, v___x_2464_, v___x_2466_);
v___x_2468_ = l_Lean_Syntax_node2(v___x_2450_, v___x_2451_, v___x_2453_, v___x_2467_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
lean_ctor_set(v___x_2469_, 1, v_a_2443_);
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1___boxed(lean_object* v_x_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1(v_x_2470_, v_a_2471_, v_a_2472_);
lean_dec_ref(v_a_2471_);
return v_res_2473_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symRw___closed__4(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2661_ = l_Lean_Parser_Tactic_rwRuleSeq;
v___x_2662_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symRw___closed__3));
v___x_2663_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2664_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
lean_ctor_set(v___x_2664_, 1, v___x_2662_);
lean_ctor_set(v___x_2664_, 2, v___x_2661_);
return v___x_2664_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symRw___closed__5(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2665_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symRw___closed__4, &l_Lean_Parser_Tactic_Grind_symRw___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_symRw___closed__4);
v___x_2666_ = lean_unsigned_to_nat(1022u);
v___x_2667_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symRw___closed__1));
v___x_2668_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
lean_ctor_set(v___x_2668_, 1, v___x_2666_);
lean_ctor_set(v___x_2668_, 2, v___x_2665_);
return v___x_2668_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symRw(void){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symRw___closed__5, &l_Lean_Parser_Tactic_Grind_symRw___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_symRw___closed__5);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1(lean_object* v_x_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2710_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1));
lean_inc(v_x_2707_);
v___x_2711_ = l_Lean_Syntax_isOfKind(v_x_2707_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_dec(v_x_2707_);
v___x_2712_ = lean_box(1);
v___x_2713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v_a_2709_);
return v___x_2713_;
}
else
{
lean_object* v_ref_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_ref_2714_ = lean_ctor_get(v_a_2708_, 5);
v___x_2715_ = lean_unsigned_to_nat(1u);
v___x_2716_ = l_Lean_Syntax_getArg(v_x_2707_, v___x_2715_);
lean_dec(v_x_2707_);
v___x_2717_ = 0;
v___x_2718_ = l_Lean_SourceInfo_fromRef(v_ref_2714_, v___x_2717_);
v___x_2719_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1));
v___x_2720_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2));
lean_inc_n(v___x_2718_, 7);
v___x_2721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2718_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0));
v___x_2723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2718_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0));
v___x_2725_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2));
v___x_2726_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_2727_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3));
v___x_2728_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4));
v___x_2729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2718_);
lean_ctor_set(v___x_2729_, 1, v___x_2727_);
v___x_2730_ = l_Lean_Syntax_node2(v___x_2718_, v___x_2728_, v___x_2729_, v___x_2716_);
v___x_2731_ = l_Lean_Syntax_node1(v___x_2718_, v___x_2726_, v___x_2730_);
v___x_2732_ = l_Lean_Syntax_node1(v___x_2718_, v___x_2725_, v___x_2731_);
v___x_2733_ = l_Lean_Syntax_node1(v___x_2718_, v___x_2724_, v___x_2732_);
v___x_2734_ = l_Lean_Syntax_node3(v___x_2718_, v___x_2719_, v___x_2721_, v___x_2723_, v___x_2733_);
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
lean_ctor_set(v___x_2735_, 1, v_a_2709_);
return v___x_2735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___boxed(lean_object* v_x_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1(v_x_2736_, v_a_2737_, v_a_2738_);
lean_dec_ref(v_a_2737_);
return v_res_2739_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvNormalize___closed__4(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2799_ = l_Lean_Parser_Tactic_optConfig;
v___x_2800_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_bvNormalize___closed__3));
v___x_2801_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2802_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
lean_ctor_set(v___x_2802_, 1, v___x_2800_);
lean_ctor_set(v___x_2802_, 2, v___x_2799_);
return v___x_2802_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = l_Lean_Parser_Tactic_bvTypes;
v___x_2804_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__5));
v___x_2805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v___x_2803_);
return v___x_2805_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvNormalize___closed__6(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2806_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5, &l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5);
v___x_2807_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__4, &l_Lean_Parser_Tactic_Grind_bvNormalize___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_bvNormalize___closed__4);
v___x_2808_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2809_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
lean_ctor_set(v___x_2809_, 1, v___x_2807_);
lean_ctor_set(v___x_2809_, 2, v___x_2806_);
return v___x_2809_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvNormalize___closed__7(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2810_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__6, &l_Lean_Parser_Tactic_Grind_bvNormalize___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_bvNormalize___closed__6);
v___x_2811_ = lean_unsigned_to_nat(1022u);
v___x_2812_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_bvNormalize___closed__1));
v___x_2813_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
lean_ctor_set(v___x_2813_, 1, v___x_2811_);
lean_ctor_set(v___x_2813_, 2, v___x_2810_);
return v___x_2813_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvNormalize(void){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__7, &l_Lean_Parser_Tactic_Grind_bvNormalize___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_bvNormalize___closed__7);
return v___x_2814_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvDecide___closed__4(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2826_ = l_Lean_Parser_Tactic_optConfig;
v___x_2827_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_bvDecide___closed__3));
v___x_2828_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2829_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___x_2827_);
lean_ctor_set(v___x_2829_, 2, v___x_2826_);
return v___x_2829_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvDecide___closed__5(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2830_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5, &l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5);
v___x_2831_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvDecide___closed__4, &l_Lean_Parser_Tactic_Grind_bvDecide___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_bvDecide___closed__4);
v___x_2832_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2833_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
lean_ctor_set(v___x_2833_, 1, v___x_2831_);
lean_ctor_set(v___x_2833_, 2, v___x_2830_);
return v___x_2833_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvDecide___closed__6(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2834_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvDecide___closed__5, &l_Lean_Parser_Tactic_Grind_bvDecide___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_bvDecide___closed__5);
v___x_2835_ = lean_unsigned_to_nat(1022u);
v___x_2836_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_bvDecide___closed__1));
v___x_2837_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
lean_ctor_set(v___x_2837_, 1, v___x_2835_);
lean_ctor_set(v___x_2837_, 2, v___x_2834_);
return v___x_2837_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvDecide(void){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvDecide___closed__6, &l_Lean_Parser_Tactic_Grind_bvDecide___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_bvDecide___closed__6);
return v___x_2838_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvTrace___closed__4(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2850_ = l_Lean_Parser_Tactic_optConfig;
v___x_2851_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_bvTrace___closed__3));
v___x_2852_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2853_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v___x_2851_);
lean_ctor_set(v___x_2853_, 2, v___x_2850_);
return v___x_2853_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvTrace___closed__5(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2854_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5, &l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5);
v___x_2855_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvTrace___closed__4, &l_Lean_Parser_Tactic_Grind_bvTrace___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_bvTrace___closed__4);
v___x_2856_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2857_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
lean_ctor_set(v___x_2857_, 1, v___x_2855_);
lean_ctor_set(v___x_2857_, 2, v___x_2854_);
return v___x_2857_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvTrace___closed__6(void){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2858_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvTrace___closed__5, &l_Lean_Parser_Tactic_Grind_bvTrace___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_bvTrace___closed__5);
v___x_2859_ = lean_unsigned_to_nat(1022u);
v___x_2860_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_bvTrace___closed__1));
v___x_2861_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
lean_ctor_set(v___x_2861_, 1, v___x_2859_);
lean_ctor_set(v___x_2861_, 2, v___x_2858_);
return v___x_2861_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvTrace(void){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvTrace___closed__6, &l_Lean_Parser_Tactic_Grind_bvTrace___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_bvTrace___closed__6);
return v___x_2862_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvCheck___closed__4(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2874_ = l_Lean_Parser_Tactic_optConfig;
v___x_2875_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_bvCheck___closed__3));
v___x_2876_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2877_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v___x_2875_);
lean_ctor_set(v___x_2877_, 2, v___x_2874_);
return v___x_2877_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvCheck___closed__5(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2878_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5, &l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_bvNormalize___closed__5);
v___x_2879_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvCheck___closed__4, &l_Lean_Parser_Tactic_Grind_bvCheck___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_bvCheck___closed__4);
v___x_2880_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2881_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
lean_ctor_set(v___x_2881_, 1, v___x_2879_);
lean_ctor_set(v___x_2881_, 2, v___x_2878_);
return v___x_2881_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvCheck___closed__6(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2882_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__8));
v___x_2883_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvCheck___closed__5, &l_Lean_Parser_Tactic_Grind_bvCheck___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_bvCheck___closed__5);
v___x_2884_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2885_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
lean_ctor_set(v___x_2885_, 1, v___x_2883_);
lean_ctor_set(v___x_2885_, 2, v___x_2882_);
return v___x_2885_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvCheck___closed__7(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2886_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_fail___closed__5));
v___x_2887_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvCheck___closed__6, &l_Lean_Parser_Tactic_Grind_bvCheck___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_bvCheck___closed__6);
v___x_2888_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2889_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
lean_ctor_set(v___x_2889_, 1, v___x_2887_);
lean_ctor_set(v___x_2889_, 2, v___x_2886_);
return v___x_2889_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvCheck___closed__8(void){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2890_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvCheck___closed__7, &l_Lean_Parser_Tactic_Grind_bvCheck___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_bvCheck___closed__7);
v___x_2891_ = lean_unsigned_to_nat(1022u);
v___x_2892_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_bvCheck___closed__1));
v___x_2893_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
lean_ctor_set(v___x_2893_, 1, v___x_2891_);
lean_ctor_set(v___x_2893_, 2, v___x_2890_);
return v___x_2893_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvCheck(void){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvCheck___closed__8, &l_Lean_Parser_Tactic_Grind_bvCheck___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_bvCheck___closed__8);
return v___x_2894_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__4(void){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2906_ = l_Lean_Parser_Tactic_optConfig;
v___x_2907_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__3));
v___x_2908_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2909_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v___x_2907_);
lean_ctor_set(v___x_2909_, 2, v___x_2906_);
return v___x_2909_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__5(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2910_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__4, &l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__4);
v___x_2911_ = lean_unsigned_to_nat(1022u);
v___x_2912_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__1));
v___x_2913_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
lean_ctor_set(v___x_2913_, 1, v___x_2911_);
lean_ctor_set(v___x_2913_, 2, v___x_2910_);
return v___x_2913_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_bvDecidePush(void){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__5, &l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_bvDecidePush___closed__5);
return v___x_2914_;
}
}
lean_object* runtime_initialize_Init_Grind_Attr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Interactive(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
l_Lean_Parser_Tactic_Grind_bvNormalize = _init_l_Lean_Parser_Tactic_Grind_bvNormalize();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_bvNormalize);
l_Lean_Parser_Tactic_Grind_bvDecide = _init_l_Lean_Parser_Tactic_Grind_bvDecide();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_bvDecide);
l_Lean_Parser_Tactic_Grind_bvTrace = _init_l_Lean_Parser_Tactic_Grind_bvTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_bvTrace);
l_Lean_Parser_Tactic_Grind_bvCheck = _init_l_Lean_Parser_Tactic_Grind_bvCheck();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_bvCheck);
l_Lean_Parser_Tactic_Grind_bvDecidePush = _init_l_Lean_Parser_Tactic_Grind_bvDecidePush();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_bvDecidePush);
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
