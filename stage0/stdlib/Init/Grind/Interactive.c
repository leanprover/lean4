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
lean_inc(v___x_925_);
v___x_932_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_925_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
lean_inc(v___x_925_);
v___x_933_ = l_Lean_Syntax_node1(v___x_925_, v___x_930_, v___x_932_);
v___x_934_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
lean_inc(v___x_925_);
v___x_935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_935_, 0, v___x_925_);
lean_ctor_set(v___x_935_, 1, v___x_930_);
lean_ctor_set(v___x_935_, 2, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__4));
lean_inc(v___x_925_);
v___x_937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_925_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Array_appendCore___redArg(v___x_934_, v___x_923_);
lean_dec_ref(v___x_923_);
lean_inc(v___x_925_);
v___x_939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_939_, 0, v___x_925_);
lean_ctor_set(v___x_939_, 1, v___x_930_);
lean_ctor_set(v___x_939_, 2, v___x_938_);
v___x_940_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__19));
lean_inc(v___x_925_);
v___x_941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_925_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
lean_inc(v___x_925_);
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
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1283_ = l_Lean_Parser_Tactic_configItem;
v___x_1284_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__8));
v___x_1285_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1286_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v___x_1284_);
lean_ctor_set(v___x_1286_, 2, v___x_1283_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__6(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__5, &l_Lean_Parser_Tactic_Grind_finish___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__5);
v___x_1288_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__4));
v___x_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v___x_1287_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__7(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__6, &l_Lean_Parser_Tactic_Grind_finish___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__6);
v___x_1291_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__2));
v___x_1292_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1293_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v___x_1291_);
lean_ctor_set(v___x_1293_, 2, v___x_1290_);
return v___x_1293_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__11(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__10));
v___x_1305_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__7, &l_Lean_Parser_Tactic_Grind_finish___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__7);
v___x_1306_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1307_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1305_);
lean_ctor_set(v___x_1307_, 2, v___x_1304_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__12(void){
_start:
{
uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1308_ = 0;
v___x_1309_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__15));
v___x_1310_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__13));
v___x_1311_ = l_Lean_Parser_Tactic_grindParam;
v___x_1312_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1310_);
lean_ctor_set(v___x_1312_, 2, v___x_1309_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*3, v___x_1308_);
return v___x_1312_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__13(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__12, &l_Lean_Parser_Tactic_Grind_finish___closed__12_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__12);
v___x_1314_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5));
v___x_1315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___x_1313_);
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__14(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1316_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__13, &l_Lean_Parser_Tactic_Grind_finish___closed__13_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__13);
v___x_1317_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__12));
v___x_1318_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1319_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v___x_1317_);
lean_ctor_set(v___x_1319_, 2, v___x_1316_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__15(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1320_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_instantiate___closed__20));
v___x_1321_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__14, &l_Lean_Parser_Tactic_Grind_finish___closed__14_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__14);
v___x_1322_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1323_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
lean_ctor_set(v___x_1323_, 1, v___x_1321_);
lean_ctor_set(v___x_1323_, 2, v___x_1320_);
return v___x_1323_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__16(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__15, &l_Lean_Parser_Tactic_Grind_finish___closed__15_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__15);
v___x_1325_ = ((lean_object*)(l_Lean_Parser_Tactic_grindLemma___closed__5));
v___x_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v___x_1324_);
return v___x_1326_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__17(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1327_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__16, &l_Lean_Parser_Tactic_Grind_finish___closed__16_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__16);
v___x_1328_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__11, &l_Lean_Parser_Tactic_Grind_finish___closed__11_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__11);
v___x_1329_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1330_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v___x_1328_);
lean_ctor_set(v___x_1330_, 2, v___x_1327_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish___closed__18(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1331_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__17, &l_Lean_Parser_Tactic_Grind_finish___closed__17_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__17);
v___x_1332_ = lean_unsigned_to_nat(1022u);
v___x_1333_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__1));
v___x_1334_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1332_);
lean_ctor_set(v___x_1334_, 2, v___x_1331_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finish(void){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__18, &l_Lean_Parser_Tactic_Grind_finish___closed__18_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__18);
return v___x_1335_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__4(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1347_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__6, &l_Lean_Parser_Tactic_Grind_finish___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__6);
v___x_1348_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finishTrace___closed__3));
v___x_1349_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1350_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___x_1348_);
lean_ctor_set(v___x_1350_, 2, v___x_1347_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__5(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1351_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__10));
v___x_1352_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__4, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__4);
v___x_1353_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1354_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v___x_1352_);
lean_ctor_set(v___x_1354_, 2, v___x_1351_);
return v___x_1354_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__6(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1355_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finish___closed__16, &l_Lean_Parser_Tactic_Grind_finish___closed__16_once, _init_l_Lean_Parser_Tactic_Grind_finish___closed__16);
v___x_1356_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__5, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__5);
v___x_1357_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1358_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___x_1356_);
lean_ctor_set(v___x_1358_, 2, v___x_1355_);
return v___x_1358_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__7(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1359_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__6, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__6);
v___x_1360_ = lean_unsigned_to_nat(1022u);
v___x_1361_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finishTrace___closed__1));
v___x_1362_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v___x_1360_);
lean_ctor_set(v___x_1362_, 2, v___x_1359_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_finishTrace(void){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_finishTrace___closed__7, &l_Lean_Parser_Tactic_Grind_finishTrace___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__7);
return v___x_1363_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__4(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = l_Lean_binderIdent;
v___x_1472_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__4));
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___x_1471_);
return v___x_1473_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__5(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1474_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__4, &l_Lean_Parser_Tactic_Grind_next___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__4);
v___x_1475_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__3));
v___x_1476_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1477_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_ctor_set(v___x_1477_, 1, v___x_1475_);
lean_ctor_set(v___x_1477_, 2, v___x_1474_);
return v___x_1477_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__6(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1478_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5));
v___x_1479_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__5, &l_Lean_Parser_Tactic_Grind_next___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__5);
v___x_1480_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1481_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___x_1479_);
lean_ctor_set(v___x_1481_, 2, v___x_1478_);
return v___x_1481_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__7(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1482_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq));
v___x_1483_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__6, &l_Lean_Parser_Tactic_Grind_next___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__6);
v___x_1484_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1485_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v___x_1483_);
lean_ctor_set(v___x_1485_, 2, v___x_1482_);
return v___x_1485_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next___closed__8(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__7, &l_Lean_Parser_Tactic_Grind_next___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__7);
v___x_1487_ = lean_unsigned_to_nat(1022u);
v___x_1488_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__1));
v___x_1489_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v___x_1487_);
lean_ctor_set(v___x_1489_, 2, v___x_1486_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_next(void){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_next___closed__8, &l_Lean_Parser_Tactic_Grind_next___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_next___closed__8);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1(lean_object* v_x_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1));
lean_inc(v_x_1514_);
v___x_1518_ = l_Lean_Syntax_isOfKind(v_x_1514_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec(v_x_1514_);
v___x_1519_ = lean_box(1);
v___x_1520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v_a_1516_);
return v___x_1520_;
}
else
{
lean_object* v_ref_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_ref_1521_ = lean_ctor_get(v_a_1515_, 5);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = l_Lean_Syntax_getArg(v_x_1514_, v___x_1522_);
v___x_1524_ = lean_unsigned_to_nat(1u);
v___x_1525_ = l_Lean_Syntax_getArg(v_x_1514_, v___x_1524_);
lean_dec(v_x_1514_);
v___x_1526_ = 0;
v___x_1527_ = l_Lean_SourceInfo_fromRef(v_ref_1521_, v___x_1526_);
v___x_1528_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__0));
v___x_1529_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_next___closed__1));
v___x_1530_ = l_Lean_SourceInfo_fromRef(v___x_1523_, v___x_1518_);
lean_dec(v___x_1523_);
lean_inc(v___x_1530_);
v___x_1531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v___x_1528_);
v___x_1532_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_1533_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
lean_inc(v___x_1527_);
v___x_1534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1527_);
lean_ctor_set(v___x_1534_, 1, v___x_1532_);
lean_ctor_set(v___x_1534_, 2, v___x_1533_);
v___x_1535_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0));
v___x_1536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1530_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = l_Lean_Syntax_node4(v___x_1527_, v___x_1529_, v___x_1531_, v___x_1534_, v___x_1536_, v___x_1525_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v_a_1516_);
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___boxed(lean_object* v_x_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1(v_x_1539_, v_a_1540_, v_a_1541_);
lean_dec_ref(v_a_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1(lean_object* v_x_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1));
lean_inc(v_x_1622_);
v___x_1626_ = l_Lean_Syntax_isOfKind(v_x_1622_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_dec(v_x_1622_);
v___x_1627_ = lean_box(1);
v___x_1628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
lean_ctor_set(v___x_1628_, 1, v_a_1624_);
return v___x_1628_;
}
else
{
lean_object* v_ref_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_tk_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_ref_1629_ = lean_ctor_get(v_a_1623_, 5);
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = l_Lean_Syntax_getArg(v_x_1622_, v___x_1630_);
v___x_1632_ = lean_unsigned_to_nat(1u);
v_tk_1633_ = l_Lean_Syntax_getArg(v_x_1622_, v___x_1632_);
v___x_1634_ = lean_unsigned_to_nat(2u);
v___x_1635_ = l_Lean_Syntax_getArg(v_x_1622_, v___x_1634_);
lean_dec(v_x_1622_);
v___x_1636_ = 0;
v___x_1637_ = l_Lean_SourceInfo_fromRef(v_ref_1629_, v___x_1636_);
v___x_1638_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_focus___closed__0));
v___x_1639_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_focus___closed__1));
lean_inc(v___x_1637_);
v___x_1640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1637_);
lean_ctor_set(v___x_1640_, 1, v___x_1638_);
v___x_1641_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1));
v___x_1642_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1));
v___x_1643_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_1644_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindStep___closed__1));
v___x_1645_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
lean_inc(v___x_1637_);
v___x_1646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1637_);
lean_ctor_set(v___x_1646_, 1, v___x_1643_);
lean_ctor_set(v___x_1646_, 2, v___x_1645_);
lean_inc_ref(v___x_1646_);
lean_inc(v___x_1637_);
v___x_1647_ = l_Lean_Syntax_node2(v___x_1637_, v___x_1644_, v___x_1631_, v___x_1646_);
v___x_1648_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1));
v___x_1649_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__0));
lean_inc(v___x_1637_);
v___x_1650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1637_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__0));
v___x_1652_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__1));
lean_inc(v___x_1637_);
v___x_1653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1637_);
lean_ctor_set(v___x_1653_, 1, v___x_1651_);
lean_inc(v___x_1637_);
v___x_1654_ = l_Lean_Syntax_node1(v___x_1637_, v___x_1652_, v___x_1653_);
lean_inc(v___x_1637_);
v___x_1655_ = l_Lean_Syntax_node3(v___x_1637_, v___x_1648_, v___x_1650_, v_tk_1633_, v___x_1654_);
lean_inc_ref(v___x_1646_);
lean_inc(v___x_1637_);
v___x_1656_ = l_Lean_Syntax_node2(v___x_1637_, v___x_1644_, v___x_1655_, v___x_1646_);
v___x_1657_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_allGoals___closed__1));
v___x_1658_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__1));
lean_inc(v___x_1637_);
v___x_1659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1637_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
lean_inc_ref(v___x_1646_);
lean_inc(v___x_1637_);
v___x_1660_ = l_Lean_Syntax_node2(v___x_1637_, v___x_1644_, v___x_1635_, v___x_1646_);
lean_inc(v___x_1637_);
v___x_1661_ = l_Lean_Syntax_node1(v___x_1637_, v___x_1643_, v___x_1660_);
lean_inc(v___x_1637_);
v___x_1662_ = l_Lean_Syntax_node1(v___x_1637_, v___x_1642_, v___x_1661_);
lean_inc(v___x_1637_);
v___x_1663_ = l_Lean_Syntax_node1(v___x_1637_, v___x_1641_, v___x_1662_);
lean_inc(v___x_1637_);
v___x_1664_ = l_Lean_Syntax_node2(v___x_1637_, v___x_1657_, v___x_1659_, v___x_1663_);
lean_inc_ref(v___x_1646_);
lean_inc(v___x_1637_);
v___x_1665_ = l_Lean_Syntax_node2(v___x_1637_, v___x_1644_, v___x_1664_, v___x_1646_);
lean_inc_ref(v___x_1646_);
lean_inc(v___x_1637_);
v___x_1666_ = l_Lean_Syntax_node5(v___x_1637_, v___x_1643_, v___x_1647_, v___x_1646_, v___x_1656_, v___x_1646_, v___x_1665_);
lean_inc(v___x_1637_);
v___x_1667_ = l_Lean_Syntax_node1(v___x_1637_, v___x_1642_, v___x_1666_);
lean_inc(v___x_1637_);
v___x_1668_ = l_Lean_Syntax_node1(v___x_1637_, v___x_1641_, v___x_1667_);
v___x_1669_ = l_Lean_Syntax_node2(v___x_1637_, v___x_1639_, v___x_1640_, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v_a_1624_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___boxed(lean_object* v_x_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1(v_x_1671_, v_a_1672_, v_a_1673_);
lean_dec_ref(v_a_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1(lean_object* v_x_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1));
lean_inc(v_x_1767_);
v___x_1771_ = l_Lean_Syntax_isOfKind(v_x_1767_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_dec(v_x_1767_);
v___x_1772_ = lean_box(1);
v___x_1773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v_a_1769_);
return v___x_1773_;
}
else
{
lean_object* v_ref_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_ref_1774_ = lean_ctor_get(v_a_1768_, 5);
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = l_Lean_Syntax_getArg(v_x_1767_, v___x_1775_);
lean_dec(v_x_1767_);
v___x_1777_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1));
v___x_1778_ = 0;
v___x_1779_ = l_Lean_SourceInfo_fromRef(v_ref_1774_, v___x_1778_);
v___x_1780_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__0));
v___x_1781_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__1));
lean_inc(v___x_1779_);
v___x_1782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1779_);
lean_ctor_set(v___x_1782_, 1, v___x_1780_);
v___x_1783_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_1784_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__9));
v___x_1785_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
lean_inc(v___x_1779_);
v___x_1786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1779_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
lean_inc(v___x_1779_);
v___x_1788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1779_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
lean_inc_ref(v___x_1788_);
lean_inc_ref(v___x_1786_);
lean_inc(v___x_1779_);
v___x_1789_ = l_Lean_Syntax_node3(v___x_1779_, v___x_1784_, v___x_1786_, v___x_1776_, v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1));
v___x_1791_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindStep___closed__1));
v___x_1792_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__0));
v___x_1793_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__1));
lean_inc(v___x_1779_);
v___x_1794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1779_);
lean_ctor_set(v___x_1794_, 1, v___x_1792_);
lean_inc(v___x_1779_);
v___x_1795_ = l_Lean_Syntax_node1(v___x_1779_, v___x_1793_, v___x_1794_);
v___x_1796_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
lean_inc(v___x_1779_);
v___x_1797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1779_);
lean_ctor_set(v___x_1797_, 1, v___x_1783_);
lean_ctor_set(v___x_1797_, 2, v___x_1796_);
lean_inc(v___x_1779_);
v___x_1798_ = l_Lean_Syntax_node2(v___x_1779_, v___x_1791_, v___x_1795_, v___x_1797_);
lean_inc(v___x_1779_);
v___x_1799_ = l_Lean_Syntax_node1(v___x_1779_, v___x_1783_, v___x_1798_);
lean_inc(v___x_1779_);
v___x_1800_ = l_Lean_Syntax_node1(v___x_1779_, v___x_1790_, v___x_1799_);
lean_inc(v___x_1779_);
v___x_1801_ = l_Lean_Syntax_node1(v___x_1779_, v___x_1777_, v___x_1800_);
lean_inc(v___x_1779_);
v___x_1802_ = l_Lean_Syntax_node3(v___x_1779_, v___x_1784_, v___x_1786_, v___x_1801_, v___x_1788_);
lean_inc(v___x_1779_);
v___x_1803_ = l_Lean_Syntax_node2(v___x_1779_, v___x_1783_, v___x_1789_, v___x_1802_);
v___x_1804_ = l_Lean_Syntax_node2(v___x_1779_, v___x_1781_, v___x_1782_, v___x_1803_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v_a_1769_);
return v___x_1805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1___boxed(lean_object* v_x_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1(v_x_1806_, v_a_1807_, v_a_1808_);
lean_dec_ref(v_a_1807_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1(lean_object* v_x_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1));
v___x_1850_ = l_Lean_Syntax_isOfKind(v_x_1846_, v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_box(1);
v___x_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v_a_1848_);
return v___x_1852_;
}
else
{
lean_object* v_ref_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v_ref_1853_ = lean_ctor_get(v_a_1847_, 5);
v___x_1854_ = 0;
v___x_1855_ = l_Lean_SourceInfo_fromRef(v_ref_1853_, v___x_1854_);
v___x_1856_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_sorry___closed__0));
v___x_1857_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_sorry___closed__1));
lean_inc(v___x_1855_);
v___x_1858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1855_);
lean_ctor_set(v___x_1858_, 1, v___x_1856_);
v___x_1859_ = l_Lean_Syntax_node1(v___x_1855_, v___x_1857_, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v_a_1848_);
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1___boxed(lean_object* v_x_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1(v_x_1861_, v_a_1862_, v_a_1863_);
lean_dec_ref(v_a_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1(lean_object* v_x_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1));
lean_inc(v_x_1918_);
v___x_1922_ = l_Lean_Syntax_isOfKind(v_x_1918_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
lean_dec(v_x_1918_);
v___x_1923_ = lean_box(1);
v___x_1924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v_a_1920_);
return v___x_1924_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1925_ = lean_unsigned_to_nat(1u);
v___x_1926_ = l_Lean_Syntax_getArg(v_x_1918_, v___x_1925_);
lean_dec(v_x_1918_);
v___x_1927_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1));
lean_inc(v___x_1926_);
v___x_1928_ = l_Lean_Syntax_isOfKind(v___x_1926_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_dec(v___x_1926_);
v___x_1929_ = lean_box(1);
v___x_1930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
lean_ctor_set(v___x_1930_, 1, v_a_1920_);
return v___x_1930_;
}
else
{
lean_object* v_ref_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v_ref_1931_ = lean_ctor_get(v_a_1919_, 5);
v___x_1932_ = 0;
v___x_1933_ = l_Lean_SourceInfo_fromRef(v_ref_1931_, v___x_1932_);
v___x_1934_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__0));
v___x_1935_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__1));
lean_inc(v___x_1933_);
v___x_1936_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1933_);
lean_ctor_set(v___x_1936_, 1, v___x_1934_);
v___x_1937_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_1938_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__9));
v___x_1939_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
lean_inc(v___x_1933_);
v___x_1940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1933_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1));
v___x_1942_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindStep___closed__1));
v___x_1943_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_paren___closed__1));
v___x_1944_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
lean_inc(v___x_1933_);
v___x_1945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1933_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
lean_inc_ref(v___x_1945_);
lean_inc(v___x_1926_);
lean_inc_ref(v___x_1940_);
lean_inc(v___x_1933_);
v___x_1946_ = l_Lean_Syntax_node3(v___x_1933_, v___x_1943_, v___x_1940_, v___x_1926_, v___x_1945_);
v___x_1947_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
lean_inc(v___x_1933_);
v___x_1948_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1933_);
lean_ctor_set(v___x_1948_, 1, v___x_1937_);
lean_ctor_set(v___x_1948_, 2, v___x_1947_);
lean_inc_ref(v___x_1948_);
lean_inc(v___x_1933_);
v___x_1949_ = l_Lean_Syntax_node2(v___x_1933_, v___x_1942_, v___x_1946_, v___x_1948_);
v___x_1950_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__0));
lean_inc(v___x_1933_);
v___x_1951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1933_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__1));
lean_inc(v___x_1933_);
v___x_1953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1933_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
lean_inc(v___x_1933_);
v___x_1954_ = l_Lean_Syntax_node2(v___x_1933_, v___x_1921_, v___x_1953_, v___x_1926_);
lean_inc_ref(v___x_1948_);
lean_inc(v___x_1933_);
v___x_1955_ = l_Lean_Syntax_node2(v___x_1933_, v___x_1942_, v___x_1954_, v___x_1948_);
lean_inc(v___x_1933_);
v___x_1956_ = l_Lean_Syntax_node3(v___x_1933_, v___x_1937_, v___x_1949_, v___x_1951_, v___x_1955_);
lean_inc(v___x_1933_);
v___x_1957_ = l_Lean_Syntax_node1(v___x_1933_, v___x_1941_, v___x_1956_);
lean_inc(v___x_1933_);
v___x_1958_ = l_Lean_Syntax_node1(v___x_1933_, v___x_1927_, v___x_1957_);
lean_inc_ref(v___x_1945_);
lean_inc_ref(v___x_1940_);
lean_inc(v___x_1933_);
v___x_1959_ = l_Lean_Syntax_node3(v___x_1933_, v___x_1938_, v___x_1940_, v___x_1958_, v___x_1945_);
v___x_1960_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__0));
v___x_1961_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_skip___closed__1));
lean_inc(v___x_1933_);
v___x_1962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1933_);
lean_ctor_set(v___x_1962_, 1, v___x_1960_);
lean_inc(v___x_1933_);
v___x_1963_ = l_Lean_Syntax_node1(v___x_1933_, v___x_1961_, v___x_1962_);
lean_inc(v___x_1933_);
v___x_1964_ = l_Lean_Syntax_node2(v___x_1933_, v___x_1942_, v___x_1963_, v___x_1948_);
lean_inc(v___x_1933_);
v___x_1965_ = l_Lean_Syntax_node1(v___x_1933_, v___x_1937_, v___x_1964_);
lean_inc(v___x_1933_);
v___x_1966_ = l_Lean_Syntax_node1(v___x_1933_, v___x_1941_, v___x_1965_);
lean_inc(v___x_1933_);
v___x_1967_ = l_Lean_Syntax_node1(v___x_1933_, v___x_1927_, v___x_1966_);
lean_inc(v___x_1933_);
v___x_1968_ = l_Lean_Syntax_node3(v___x_1933_, v___x_1938_, v___x_1940_, v___x_1967_, v___x_1945_);
lean_inc(v___x_1933_);
v___x_1969_ = l_Lean_Syntax_node2(v___x_1933_, v___x_1937_, v___x_1959_, v___x_1968_);
v___x_1970_ = l_Lean_Syntax_node2(v___x_1933_, v___x_1935_, v___x_1936_, v___x_1969_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v_a_1920_);
return v___x_1971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___boxed(lean_object* v_x_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1(v_x_1972_, v_a_1973_, v_a_1974_);
lean_dec_ref(v_a_1973_);
return v_res_1975_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1991_ = l_Lean_binderIdent;
v___x_1992_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_renameI___closed__4));
v___x_1993_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_1994_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_ctor_set(v___x_1994_, 1, v___x_1992_);
lean_ctor_set(v___x_1994_, 2, v___x_1991_);
return v___x_1994_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__6(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__5, &l_Lean_Parser_Tactic_Grind_renameI___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5);
v___x_1996_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__7));
v___x_1997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v___x_1995_);
return v___x_1997_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__7(void){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1998_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__6, &l_Lean_Parser_Tactic_Grind_renameI___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__6);
v___x_1999_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_renameI___closed__3));
v___x_2000_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2001_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v___x_1999_);
lean_ctor_set(v___x_2001_, 2, v___x_1998_);
return v___x_2001_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI___closed__8(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2002_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__7, &l_Lean_Parser_Tactic_Grind_renameI___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__7);
v___x_2003_ = lean_unsigned_to_nat(1022u);
v___x_2004_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_renameI___closed__1));
v___x_2005_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
lean_ctor_set(v___x_2005_, 1, v___x_2003_);
lean_ctor_set(v___x_2005_, 2, v___x_2002_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_renameI(void){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__8, &l_Lean_Parser_Tactic_Grind_renameI___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__8);
return v___x_2006_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__4(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = l_Lean_Parser_Tactic_configItem;
v___x_2101_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_first___closed__7));
v___x_2102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v___x_2100_);
return v___x_2102_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__5(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2103_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__4, &l_Lean_Parser_Tactic_Grind_setConfig___closed__4_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__4);
v___x_2104_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_setConfig___closed__3));
v___x_2105_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2106_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v___x_2104_);
lean_ctor_set(v___x_2106_, 2, v___x_2103_);
return v___x_2106_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__6(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2107_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_setOption___closed__18));
v___x_2108_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__5, &l_Lean_Parser_Tactic_Grind_setConfig___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__5);
v___x_2109_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2110_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v___x_2108_);
lean_ctor_set(v___x_2110_, 2, v___x_2107_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__7(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2111_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindSeq));
v___x_2112_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__6, &l_Lean_Parser_Tactic_Grind_setConfig___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__6);
v___x_2113_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2114_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v___x_2112_);
lean_ctor_set(v___x_2114_, 2, v___x_2111_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__8(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2115_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__7, &l_Lean_Parser_Tactic_Grind_setConfig___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__7);
v___x_2116_ = lean_unsigned_to_nat(1022u);
v___x_2117_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_setConfig___closed__1));
v___x_2118_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_2116_);
lean_ctor_set(v___x_2118_, 2, v___x_2115_);
return v___x_2118_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_setConfig(void){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_setConfig___closed__8, &l_Lean_Parser_Tactic_Grind_setConfig___closed__8_once, _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__8);
return v___x_2119_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_renameI___closed__5, &l_Lean_Parser_Tactic_Grind_renameI___closed__5_once, _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5);
v___x_2246_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_finish___closed__4));
v___x_2247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v___x_2245_);
return v___x_2247_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__26(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2248_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__25, &l_Lean_Parser_Tactic_Grind_symIntro___closed__25_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25);
v___x_2249_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__24));
v___x_2250_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2251_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set(v___x_2251_, 1, v___x_2249_);
lean_ctor_set(v___x_2251_, 2, v___x_2248_);
return v___x_2251_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__27(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2252_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__26, &l_Lean_Parser_Tactic_Grind_symIntro___closed__26_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__26);
v___x_2253_ = lean_unsigned_to_nat(1022u);
v___x_2254_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__1));
v___x_2255_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v___x_2253_);
lean_ctor_set(v___x_2255_, 2, v___x_2252_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntro(void){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__27, &l_Lean_Parser_Tactic_Grind_symIntro___closed__27_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__27);
return v___x_2256_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2275_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntro___closed__25, &l_Lean_Parser_Tactic_Grind_symIntro___closed__25_once, _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25);
v___x_2276_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__5));
v___x_2277_ = ((lean_object*)(l_Lean_Parser_Tactic_anchor___closed__6));
v___x_2278_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___x_2276_);
lean_ctor_set(v___x_2278_, 2, v___x_2275_);
return v___x_2278_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2279_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6, &l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6_once, _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6);
v___x_2280_ = lean_unsigned_to_nat(1022u);
v___x_2281_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1));
v___x_2282_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v___x_2280_);
lean_ctor_set(v___x_2282_, 2, v___x_2279_);
return v___x_2282_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_symIntroLight(void){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7, &l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7_once, _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1(lean_object* v_x_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2288_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1));
lean_inc(v_x_2285_);
v___x_2289_ = l_Lean_Syntax_isOfKind(v_x_2285_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
lean_dec(v_x_2285_);
v___x_2290_ = lean_box(1);
v___x_2291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v_a_2287_);
return v___x_2291_;
}
else
{
lean_object* v_ref_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v_ids_2295_; uint8_t v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_ref_2292_ = lean_ctor_get(v_a_2286_, 5);
v___x_2293_ = lean_unsigned_to_nat(2u);
v___x_2294_ = l_Lean_Syntax_getArg(v_x_2285_, v___x_2293_);
lean_dec(v_x_2285_);
v_ids_2295_ = l_Lean_Syntax_getArgs(v___x_2294_);
lean_dec(v___x_2294_);
v___x_2296_ = 0;
v___x_2297_ = l_Lean_SourceInfo_fromRef(v_ref_2292_, v___x_2296_);
v___x_2298_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__1));
v___x_2299_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__2));
lean_inc(v___x_2297_);
v___x_2300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2297_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_2302_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
lean_inc(v___x_2297_);
v___x_2303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2297_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__5));
lean_inc(v___x_2297_);
v___x_2305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2297_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0));
lean_inc(v___x_2297_);
v___x_2307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2297_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__16));
v___x_2309_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__17));
lean_inc(v___x_2297_);
v___x_2310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2297_);
lean_ctor_set(v___x_2310_, 1, v___x_2308_);
lean_inc(v___x_2297_);
v___x_2311_ = l_Lean_Syntax_node1(v___x_2297_, v___x_2309_, v___x_2310_);
v___x_2312_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
lean_inc(v___x_2297_);
v___x_2313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2297_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
lean_inc(v___x_2297_);
v___x_2314_ = l_Lean_Syntax_node5(v___x_2297_, v___x_2301_, v___x_2303_, v___x_2305_, v___x_2307_, v___x_2311_, v___x_2313_);
v___x_2315_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3, &l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once, _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
v___x_2316_ = l_Array_appendCore___redArg(v___x_2315_, v_ids_2295_);
lean_dec_ref(v_ids_2295_);
lean_inc(v___x_2297_);
v___x_2317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2297_);
lean_ctor_set(v___x_2317_, 1, v___x_2301_);
lean_ctor_set(v___x_2317_, 2, v___x_2316_);
v___x_2318_ = l_Lean_Syntax_node3(v___x_2297_, v___x_2298_, v___x_2300_, v___x_2314_, v___x_2317_);
v___x_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v_a_2287_);
return v___x_2319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___boxed(lean_object* v_x_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1(v_x_2320_, v_a_2321_, v_a_2322_);
lean_dec_ref(v_a_2321_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1(lean_object* v_x_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1));
v___x_2368_ = l_Lean_Syntax_isOfKind(v_x_2364_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_box(1);
v___x_2370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v_a_2366_);
return v___x_2370_;
}
else
{
lean_object* v_ref_2371_; uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v_ref_2371_ = lean_ctor_get(v_a_2365_, 5);
v___x_2372_ = 0;
v___x_2373_ = l_Lean_SourceInfo_fromRef(v_ref_2371_, v___x_2372_);
v___x_2374_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntros___closed__1));
v___x_2375_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntros___closed__2));
lean_inc(v___x_2373_);
v___x_2376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2373_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_2378_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2));
lean_inc(v___x_2373_);
v___x_2379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2373_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__5));
lean_inc(v___x_2373_);
v___x_2381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2373_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0));
lean_inc(v___x_2373_);
v___x_2383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2373_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__16));
v___x_2385_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_symIntro___closed__17));
lean_inc(v___x_2373_);
v___x_2386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2373_);
lean_ctor_set(v___x_2386_, 1, v___x_2384_);
lean_inc(v___x_2373_);
v___x_2387_ = l_Lean_Syntax_node1(v___x_2373_, v___x_2385_, v___x_2386_);
v___x_2388_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9));
lean_inc(v___x_2373_);
v___x_2389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2373_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
lean_inc(v___x_2373_);
v___x_2390_ = l_Lean_Syntax_node5(v___x_2373_, v___x_2377_, v___x_2379_, v___x_2381_, v___x_2383_, v___x_2387_, v___x_2389_);
v___x_2391_ = l_Lean_Syntax_node2(v___x_2373_, v___x_2374_, v___x_2376_, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
lean_ctor_set(v___x_2392_, 1, v_a_2366_);
return v___x_2392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1___boxed(lean_object* v_x_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1(v_x_2393_, v_a_2394_, v_a_2395_);
lean_dec_ref(v_a_2394_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1(lean_object* v_x_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2559_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1));
lean_inc(v_x_2556_);
v___x_2560_ = l_Lean_Syntax_isOfKind(v_x_2556_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec(v_x_2556_);
v___x_2561_ = lean_box(1);
v___x_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
lean_ctor_set(v___x_2562_, 1, v_a_2558_);
return v___x_2562_;
}
else
{
lean_object* v_ref_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_ref_2563_ = lean_ctor_get(v_a_2557_, 5);
v___x_2564_ = lean_unsigned_to_nat(1u);
v___x_2565_ = l_Lean_Syntax_getArg(v_x_2556_, v___x_2564_);
lean_dec(v_x_2556_);
v___x_2566_ = 0;
v___x_2567_ = l_Lean_SourceInfo_fromRef(v_ref_2563_, v___x_2566_);
v___x_2568_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1));
v___x_2569_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2));
lean_inc(v___x_2567_);
v___x_2570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2567_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0));
lean_inc(v___x_2567_);
v___x_2572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2567_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0));
v___x_2574_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2));
v___x_2575_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1));
v___x_2576_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3));
v___x_2577_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4));
lean_inc(v___x_2567_);
v___x_2578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2567_);
lean_ctor_set(v___x_2578_, 1, v___x_2576_);
lean_inc(v___x_2567_);
v___x_2579_ = l_Lean_Syntax_node2(v___x_2567_, v___x_2577_, v___x_2578_, v___x_2565_);
lean_inc(v___x_2567_);
v___x_2580_ = l_Lean_Syntax_node1(v___x_2567_, v___x_2575_, v___x_2579_);
lean_inc(v___x_2567_);
v___x_2581_ = l_Lean_Syntax_node1(v___x_2567_, v___x_2574_, v___x_2580_);
lean_inc(v___x_2567_);
v___x_2582_ = l_Lean_Syntax_node1(v___x_2567_, v___x_2573_, v___x_2581_);
v___x_2583_ = l_Lean_Syntax_node3(v___x_2567_, v___x_2568_, v___x_2570_, v___x_2572_, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v_a_2558_);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___boxed(lean_object* v_x_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1(v_x_2585_, v_a_2586_, v_a_2587_);
lean_dec_ref(v_a_2586_);
return v_res_2588_;
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
l_Lean_Parser_Tactic_Grind_renameI = _init_l_Lean_Parser_Tactic_Grind_renameI();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_renameI);
l_Lean_Parser_Tactic_Grind_setConfig = _init_l_Lean_Parser_Tactic_Grind_setConfig();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_setConfig);
l_Lean_Parser_Tactic_Grind_symIntro = _init_l_Lean_Parser_Tactic_Grind_symIntro();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_symIntro);
l_Lean_Parser_Tactic_Grind_symIntroLight = _init_l_Lean_Parser_Tactic_Grind_symIntroLight();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_symIntroLight);
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
