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
static const lean_string_object l_tacticBy__cases___x3a___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticBy_cases_:_"};
static const lean_object* l_tacticBy__cases___x3a___00__closed__0 = (const lean_object*)&l_tacticBy__cases___x3a___00__closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "open"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
static lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30_value),LEAN_SCALAR_PTR_LITERAL(175, 67, 188, 228, 198, 126, 180, 88)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33_value;
static const lean_string_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34_value;
static lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35;
static const lean_ctor_object l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34_value),LEAN_SCALAR_PTR_LITERAL(224, 129, 35, 203, 24, 252, 22, 100)}};
static const lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36 = (const lean_object*)&l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36_value;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticBy__cases___x3a___00__closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_matchesNull(x_10, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
lean_dec_ref(x_2);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_16, x_19);
lean_dec(x_16);
x_21 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__0));
lean_inc(x_20);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2));
x_24 = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4;
x_25 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5));
x_26 = l_Lean_addMacroScope(x_14, x_25, x_15);
x_27 = lean_box(0);
lean_inc(x_20);
x_28 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_27);
x_29 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6));
lean_inc(x_20);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_20);
x_31 = l_Lean_Syntax_node2(x_20, x_23, x_28, x_30);
x_32 = l_Lean_Syntax_node3(x_20, x_4, x_22, x_31, x_18);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
}
}
}
static lean_object* _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__8));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_tacticBy__cases___x3a___00__closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
lean_inc(x_9);
x_11 = l_Lean_Syntax_matchesNull(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
lean_dec_ref(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_9, x_17);
lean_dec(x_9);
x_19 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_20 = 0;
x_21 = l_Lean_SourceInfo_fromRef(x_16, x_20);
lean_dec(x_16);
x_22 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3));
x_23 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4));
lean_inc(x_21);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
x_25 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7));
x_26 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2));
x_27 = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9;
x_28 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__10));
lean_inc(x_15);
lean_inc(x_14);
x_29 = l_Lean_addMacroScope(x_14, x_28, x_15);
x_30 = lean_box(0);
x_31 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__12));
lean_inc(x_21);
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_31);
lean_inc(x_21);
x_33 = l_Lean_Syntax_node1(x_21, x_26, x_32);
lean_inc(x_21);
x_34 = l_Lean_Syntax_node1(x_21, x_25, x_33);
x_35 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__13));
lean_inc(x_21);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_35);
x_37 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15));
x_38 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17));
x_39 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__18));
x_40 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19));
lean_inc(x_21);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_39);
x_42 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__21));
x_43 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__22));
lean_inc(x_21);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_43);
x_45 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24));
lean_inc(x_21);
x_46 = l_Lean_Syntax_node1(x_21, x_45, x_18);
x_47 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6));
lean_inc(x_21);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_47);
x_49 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__25));
lean_inc(x_21);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_21);
lean_ctor_set(x_50, 1, x_49);
x_51 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28));
x_52 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__29));
lean_inc(x_21);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_21);
lean_ctor_set(x_53, 1, x_52);
x_54 = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31;
x_55 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32));
lean_inc(x_15);
lean_inc(x_14);
x_56 = l_Lean_addMacroScope(x_14, x_55, x_15);
lean_inc(x_21);
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_30);
lean_inc_ref(x_53);
lean_inc(x_21);
x_58 = l_Lean_Syntax_node2(x_21, x_51, x_53, x_57);
x_59 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33));
lean_inc(x_21);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_21);
lean_ctor_set(x_60, 1, x_59);
x_61 = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35;
x_62 = ((lean_object*)(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36));
x_63 = l_Lean_addMacroScope(x_14, x_62, x_15);
lean_inc(x_21);
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_21);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_30);
lean_inc(x_21);
x_65 = l_Lean_Syntax_node2(x_21, x_51, x_53, x_64);
lean_inc(x_21);
x_66 = l_Lean_Syntax_node8(x_21, x_42, x_44, x_46, x_48, x_19, x_50, x_58, x_60, x_65);
lean_inc(x_21);
x_67 = l_Lean_Syntax_node2(x_21, x_40, x_41, x_66);
lean_inc(x_21);
x_68 = l_Lean_Syntax_node1(x_21, x_26, x_67);
lean_inc(x_21);
x_69 = l_Lean_Syntax_node1(x_21, x_38, x_68);
lean_inc(x_21);
x_70 = l_Lean_Syntax_node1(x_21, x_37, x_69);
x_71 = l_Lean_Syntax_node4(x_21, x_23, x_24, x_34, x_36, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_3);
return x_72;
}
}
}
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
l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4 = _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4();
lean_mark_persistent(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4);
l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9 = _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9();
lean_mark_persistent(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9);
l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31 = _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31();
lean_mark_persistent(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31);
l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35 = _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35();
lean_mark_persistent(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
