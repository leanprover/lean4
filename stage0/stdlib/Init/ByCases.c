// Lean compiler output
// Module: Init.ByCases
// Imports: public meta import Init.Grind.Tactics public import Init.Grind.Tactics import Init.SimpLemmas
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_tacticBy__cases___x3a___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticBy_cases_:_"};
static const lean_object* l_tacticBy__cases___x3a___00__closed__0 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__0_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticBy__cases___x3a___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 65, 31, 128, 134, 243, 21, 139)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__1 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__1_value;
static const lean_string_object l_tacticBy__cases___x3a___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_tacticBy__cases___x3a___00__closed__2 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__2_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticBy__cases___x3a___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__3 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__3_value;
static const lean_string_object l_tacticBy__cases___x3a___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "by_cases "};
static const lean_object* l_tacticBy__cases___x3a___00__closed__4 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__4_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_tacticBy__cases___x3a___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__5 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__5_value;
static const lean_string_object l_tacticBy__cases___x3a___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_tacticBy__cases___x3a___00__closed__6 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__6_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticBy__cases___x3a___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__7 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__7_value;
static const lean_string_object l_tacticBy__cases___x3a___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l_tacticBy__cases___x3a___00__closed__8 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__8_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticBy__cases___x3a___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__9 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__9_value;
static const lean_string_object l_tacticBy__cases___x3a___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_tacticBy__cases___x3a___00__closed__10 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__10_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticBy__cases___x3a___00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__11 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__11_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_tacticBy__cases___x3a___00__closed__11_value)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__12 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__12_value;
static const lean_string_object l_tacticBy__cases___x3a___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_tacticBy__cases___x3a___00__closed__13 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__13_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_tacticBy__cases___x3a___00__closed__13_value)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__14 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__14_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_tacticBy__cases___x3a___00__closed__3_value),((lean_object*)&l_tacticBy__cases___x3a___00__closed__12_value),((lean_object*)&l_tacticBy__cases___x3a___00__closed__14_value)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__15 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__15_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_tacticBy__cases___x3a___00__closed__9_value),((lean_object*)&l_tacticBy__cases___x3a___00__closed__15_value)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__16 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__16_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_tacticBy__cases___x3a___00__closed__7_value),((lean_object*)&l_tacticBy__cases___x3a___00__closed__16_value)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__17 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__17_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_tacticBy__cases___x3a___00__closed__3_value),((lean_object*)&l_tacticBy__cases___x3a___00__closed__5_value),((lean_object*)&l_tacticBy__cases___x3a___00__closed__17_value)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__18 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__18_value;
static const lean_string_object l_tacticBy__cases___x3a___00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_tacticBy__cases___x3a___00__closed__19 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__19_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticBy__cases___x3a___00__closed__19_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__20 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__20_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_tacticBy__cases___x3a___00__closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__21 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__21_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_tacticBy__cases___x3a___00__closed__3_value),((lean_object*)&l_tacticBy__cases___x3a___00__closed__18_value),((lean_object*)&l_tacticBy__cases___x3a___00__closed__21_value)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__22 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__22_value;
static const lean_ctor_object l_tacticBy__cases___x3a___00__closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_tacticBy__cases___x3a___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_tacticBy__cases___x3a___00__closed__22_value)}};
static const lean_object* l_tacticBy__cases___x3a___00__closed__23 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__23_value;
LEAN_EXPORT const lean_object* l_tacticBy__cases___x3a__ = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__23_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "by_cases"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__0 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__0_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__1 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__1_value;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3_value;
static lean_once_cell_t l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "open"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3_value;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_0),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_1),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_2),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(68, 209, 138, 110, 159, 245, 114, 22)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__5 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__5_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openSimple"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__6 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__6_value;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_0),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_1),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_2),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(171, 238, 134, 92, 162, 110, 43, 67)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__8 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__8_value;
static lean_once_cell_t l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__10 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__10_value;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__10_value)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__11 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__11_value;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__12 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__12_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__13 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__13_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__14 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__14_value;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_0),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_1),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_2),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__14_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__16 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__16_value;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_0),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_1),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_2),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__16_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "refine"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__18 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__18_value;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_0),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_1),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_2),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__18_value),LEAN_SCALAR_PTR_LITERAL(49, 130, 130, 160, 131, 48, 178, 245)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDepIfThenElse"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__20 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__20_value;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__20_value),LEAN_SCALAR_PTR_LITERAL(191, 94, 17, 11, 145, 108, 236, 173)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__21 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__21_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__22 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__22_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__23 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__23_value;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24_value_aux_0),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__23_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__25 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__25_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__26 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__26_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__27 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__27_value;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_0),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_1),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_2),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__27_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__29 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__29_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pos"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30_value;
static lean_once_cell_t l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30_value),LEAN_SCALAR_PTR_LITERAL(175, 67, 188, 228, 198, 126, 180, 88)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34_value;
static lean_once_cell_t l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34_value),LEAN_SCALAR_PTR_LITERAL(224, 129, 35, 203, 24, 252, 22, 100)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36_value;
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3));
v___x_60_ = l_String_toRawSubstring_x27(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1(lean_object* v_x_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = ((lean_object*)(l_tacticBy__cases___x3a___00__closed__1));
lean_inc(v_x_64_);
v___x_68_ = l_Lean_Syntax_isOfKind(v_x_64_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_x_64_);
v___x_69_ = lean_box(1);
v___x_70_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v_a_66_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = l_Lean_Syntax_getArg(v_x_64_, v___x_72_);
v___x_74_ = l_Lean_Syntax_matchesNull(v___x_73_, v___x_71_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_x_64_);
v___x_75_ = lean_box(1);
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v_a_66_);
return v___x_76_;
}
else
{
lean_object* v_quotContext_77_; lean_object* v_currMacroScope_78_; lean_object* v_ref_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_quotContext_77_ = lean_ctor_get(v_a_65_, 1);
v_currMacroScope_78_ = lean_ctor_get(v_a_65_, 2);
v_ref_79_ = lean_ctor_get(v_a_65_, 5);
v___x_80_ = lean_unsigned_to_nat(2u);
v___x_81_ = l_Lean_Syntax_getArg(v_x_64_, v___x_80_);
lean_dec(v_x_64_);
v___x_82_ = 0;
v___x_83_ = l_Lean_SourceInfo_fromRef(v_ref_79_, v___x_82_);
v___x_84_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__0));
lean_inc_n(v___x_83_, 4);
v___x_85_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2));
v___x_87_ = lean_obj_once(&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4, &l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4_once, _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4);
v___x_88_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5));
lean_inc(v_currMacroScope_78_);
lean_inc(v_quotContext_77_);
v___x_89_ = l_Lean_addMacroScope(v_quotContext_77_, v___x_88_, v_currMacroScope_78_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_91_, 0, v___x_83_);
lean_ctor_set(v___x_91_, 1, v___x_87_);
lean_ctor_set(v___x_91_, 2, v___x_89_);
lean_ctor_set(v___x_91_, 3, v___x_90_);
v___x_92_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6));
v___x_93_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_83_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = l_Lean_Syntax_node2(v___x_83_, v___x_86_, v___x_91_, v___x_93_);
v___x_95_ = l_Lean_Syntax_node3(v___x_83_, v___x_67_, v___x_85_, v___x_94_, v___x_81_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v_a_66_);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___boxed(lean_object* v_x_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1(v_x_97_, v_a_98_, v_a_99_);
lean_dec_ref(v_a_98_);
return v_res_100_;
}
}
static lean_object* _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__8));
v___x_119_ = l_String_toRawSubstring_x27(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30));
v___x_165_ = l_String_toRawSubstring_x27(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34));
v___x_171_ = l_String_toRawSubstring_x27(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2(lean_object* v_x_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_tacticBy__cases___x3a___00__closed__1));
lean_inc(v_x_174_);
v___x_178_ = l_Lean_Syntax_isOfKind(v_x_174_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_x_174_);
v___x_179_ = lean_box(1);
v___x_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v_a_176_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = l_Lean_Syntax_getArg(v_x_174_, v___x_181_);
v___x_183_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_182_);
v___x_184_ = l_Lean_Syntax_matchesNull(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v___x_182_);
lean_dec(v_x_174_);
v___x_185_ = lean_box(1);
v___x_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_a_176_);
return v___x_186_;
}
else
{
lean_object* v_quotContext_187_; lean_object* v_currMacroScope_188_; lean_object* v_ref_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_quotContext_187_ = lean_ctor_get(v_a_175_, 1);
v_currMacroScope_188_ = lean_ctor_get(v_a_175_, 2);
v_ref_189_ = lean_ctor_get(v_a_175_, 5);
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = l_Lean_Syntax_getArg(v___x_182_, v___x_190_);
lean_dec(v___x_182_);
v___x_192_ = l_Lean_Syntax_getArg(v_x_174_, v___x_183_);
lean_dec(v_x_174_);
v___x_193_ = 0;
v___x_194_ = l_Lean_SourceInfo_fromRef(v_ref_189_, v___x_193_);
v___x_195_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3));
v___x_196_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4));
lean_inc_n(v___x_194_, 21);
v___x_197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_194_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
v___x_198_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7));
v___x_199_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2));
v___x_200_ = lean_obj_once(&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9, &l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9_once, _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9);
v___x_201_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__10));
lean_inc_n(v_currMacroScope_188_, 3);
lean_inc_n(v_quotContext_187_, 3);
v___x_202_ = l_Lean_addMacroScope(v_quotContext_187_, v___x_201_, v_currMacroScope_188_);
v___x_203_ = lean_box(0);
v___x_204_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__12));
v___x_205_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_205_, 0, v___x_194_);
lean_ctor_set(v___x_205_, 1, v___x_200_);
lean_ctor_set(v___x_205_, 2, v___x_202_);
lean_ctor_set(v___x_205_, 3, v___x_204_);
v___x_206_ = l_Lean_Syntax_node1(v___x_194_, v___x_199_, v___x_205_);
v___x_207_ = l_Lean_Syntax_node1(v___x_194_, v___x_198_, v___x_206_);
v___x_208_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__13));
v___x_209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_194_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15));
v___x_211_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17));
v___x_212_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__18));
v___x_213_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19));
v___x_214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_194_);
lean_ctor_set(v___x_214_, 1, v___x_212_);
v___x_215_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__21));
v___x_216_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__22));
v___x_217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_194_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24));
v___x_219_ = l_Lean_Syntax_node1(v___x_194_, v___x_218_, v___x_191_);
v___x_220_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6));
v___x_221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_194_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__25));
v___x_223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_194_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28));
v___x_225_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__29));
v___x_226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_194_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_obj_once(&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31, &l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31_once, _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31);
v___x_228_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32));
v___x_229_ = l_Lean_addMacroScope(v_quotContext_187_, v___x_228_, v_currMacroScope_188_);
v___x_230_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_230_, 0, v___x_194_);
lean_ctor_set(v___x_230_, 1, v___x_227_);
lean_ctor_set(v___x_230_, 2, v___x_229_);
lean_ctor_set(v___x_230_, 3, v___x_203_);
lean_inc_ref(v___x_226_);
v___x_231_ = l_Lean_Syntax_node2(v___x_194_, v___x_224_, v___x_226_, v___x_230_);
v___x_232_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33));
v___x_233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_194_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_obj_once(&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35, &l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35_once, _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35);
v___x_235_ = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36));
v___x_236_ = l_Lean_addMacroScope(v_quotContext_187_, v___x_235_, v_currMacroScope_188_);
v___x_237_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_237_, 0, v___x_194_);
lean_ctor_set(v___x_237_, 1, v___x_234_);
lean_ctor_set(v___x_237_, 2, v___x_236_);
lean_ctor_set(v___x_237_, 3, v___x_203_);
v___x_238_ = l_Lean_Syntax_node2(v___x_194_, v___x_224_, v___x_226_, v___x_237_);
v___x_239_ = l_Lean_Syntax_node8(v___x_194_, v___x_215_, v___x_217_, v___x_219_, v___x_221_, v___x_192_, v___x_223_, v___x_231_, v___x_233_, v___x_238_);
v___x_240_ = l_Lean_Syntax_node2(v___x_194_, v___x_213_, v___x_214_, v___x_239_);
v___x_241_ = l_Lean_Syntax_node1(v___x_194_, v___x_199_, v___x_240_);
v___x_242_ = l_Lean_Syntax_node1(v___x_194_, v___x_211_, v___x_241_);
v___x_243_ = l_Lean_Syntax_node1(v___x_194_, v___x_210_, v___x_242_);
v___x_244_ = l_Lean_Syntax_node4(v___x_194_, v___x_196_, v___x_197_, v___x_207_, v___x_209_, v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v_a_176_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___boxed(lean_object* v_x_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2(v_x_246_, v_a_247_, v_a_248_);
lean_dec_ref(v_a_247_);
return v_res_249_;
}
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_SimpLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_ByCases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_ByCases(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_SimpLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_ByCases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_ByCases(builtin);
}
#ifdef __cplusplus
}
#endif
