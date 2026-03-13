// Lean compiler output
// Module: Init.MacroTrace
// Imports: public meta import Init.Meta public import Init.Notation import Init.Data.ToString.Macro
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value;
static const lean_string_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "termMacro.trace[_]_"};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__1 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__1_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2_value_aux_0),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(43, 106, 148, 90, 66, 246, 255, 117)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2_value;
static const lean_string_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__3 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__3_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4_value;
static const lean_string_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Macro.trace["};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__5 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__5_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__5_value)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__6 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__6_value;
static const lean_string_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__7 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__7_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__8 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__8_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__8_value)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__9 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__9_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4_value),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__6_value),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__9_value)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__10 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__10_value;
static const lean_string_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__11 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__11_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__11_value)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__12 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__12_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4_value),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__10_value),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__12_value)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__13 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__13_value;
static const lean_string_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__14 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__14_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__14_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__15 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__15_value;
static const lean_string_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__16 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__16_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__16_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__17 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__17_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__18 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__18_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__15_value),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__18_value)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__19 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__19_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4_value),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__13_value),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__19_value)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__20 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__20_value;
static const lean_ctor_object l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__20_value)}};
static const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__21 = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__21_value;
LEAN_EXPORT const lean_object* l_Lean_termMacro_x2etrace_x5b___x5d__ = (const lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__21_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__2 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_0),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_1),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_2),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Macro.trace"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__4 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__4_value;
static lean_once_cell_t l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__6 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__6_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__7 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__7_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(153, 13, 84, 30, 172, 208, 133, 203)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8_value_aux_0),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(158, 132, 167, 209, 110, 243, 212, 132)}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value_aux_0),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value_aux_1),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(227, 20, 194, 181, 135, 86, 144, 29)}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__10 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__10_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__11 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__11_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__12 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__12_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__13 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__13_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__14 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__14_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_0),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_1),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_2),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__16 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__16_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_0),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_1),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_2),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__18 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__18_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__19 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__19_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__20 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__20_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__21 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__21_value;
static lean_once_cell_t l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__23 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__23_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__23_value)}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__24 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__24_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__25 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__25_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termS!_"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__26 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__26_value;
static const lean_ctor_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(30, 130, 93, 49, 63, 146, 201, 153)}};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__27 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__27_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "s!"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__28 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__28_value;
static const lean_string_object l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__29 = (const lean_object*)&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__29_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__4));
v___x_59_ = l_String_toRawSubstring_x27(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__21));
v___x_96_ = l_String_toRawSubstring_x27(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1(lean_object* v_x_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = ((lean_object*)(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2));
lean_inc(v_x_109_);
v___x_113_ = l_Lean_Syntax_isOfKind(v_x_109_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec_ref(v_a_110_);
lean_dec(v_x_109_);
v___x_114_ = lean_box(1);
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_a_111_);
return v___x_115_;
}
else
{
lean_object* v_quotContext_116_; lean_object* v_currMacroScope_117_; lean_object* v_ref_118_; lean_object* v___x_119_; lean_object* v_id_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_quotContext_116_ = lean_ctor_get(v_a_110_, 1);
lean_inc(v_quotContext_116_);
v_currMacroScope_117_ = lean_ctor_get(v_a_110_, 2);
lean_inc(v_currMacroScope_117_);
v_ref_118_ = lean_ctor_get(v_a_110_, 5);
lean_inc(v_ref_118_);
lean_dec_ref(v_a_110_);
v___x_119_ = lean_unsigned_to_nat(1u);
v_id_120_ = l_Lean_Syntax_getArg(v_x_109_, v___x_119_);
v___x_121_ = lean_unsigned_to_nat(3u);
v___x_122_ = l_Lean_Syntax_getArg(v_x_109_, v___x_121_);
lean_dec(v_x_109_);
v___x_123_ = 0;
v___x_124_ = l_Lean_SourceInfo_fromRef(v_ref_118_, v___x_123_);
lean_dec(v_ref_118_);
v___x_125_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3));
v___x_126_ = lean_obj_once(&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5, &l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5_once, _init_l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5);
v___x_127_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8));
lean_inc(v_currMacroScope_117_);
lean_inc(v_quotContext_116_);
v___x_128_ = l_Lean_addMacroScope(v_quotContext_116_, v___x_127_, v_currMacroScope_117_);
v___x_129_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__11));
lean_inc(v___x_124_);
v___x_130_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_130_, 0, v___x_124_);
lean_ctor_set(v___x_130_, 1, v___x_126_);
lean_ctor_set(v___x_130_, 2, v___x_128_);
lean_ctor_set(v___x_130_, 3, v___x_129_);
v___x_131_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__13));
v___x_132_ = l_Lean_TSyntax_getId(v_id_120_);
lean_dec(v_id_120_);
v___x_133_ = lean_erase_macro_scopes(v___x_132_);
v___x_134_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_133_);
v___x_135_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15));
v___x_136_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17));
v___x_137_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__18));
lean_inc(v___x_124_);
v___x_138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_124_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__20));
v___x_140_ = lean_obj_once(&l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22, &l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22_once, _init_l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22);
v___x_141_ = lean_box(0);
v___x_142_ = l_Lean_addMacroScope(v_quotContext_116_, v___x_141_, v_currMacroScope_117_);
v___x_143_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__25));
lean_inc(v___x_124_);
v___x_144_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_144_, 0, v___x_124_);
lean_ctor_set(v___x_144_, 1, v___x_140_);
lean_ctor_set(v___x_144_, 2, v___x_142_);
lean_ctor_set(v___x_144_, 3, v___x_143_);
lean_inc(v___x_124_);
v___x_145_ = l_Lean_Syntax_node1(v___x_124_, v___x_139_, v___x_144_);
lean_inc(v___x_124_);
v___x_146_ = l_Lean_Syntax_node2(v___x_124_, v___x_136_, v___x_138_, v___x_145_);
v___x_147_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__27));
v___x_148_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__28));
lean_inc(v___x_124_);
v___x_149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_124_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
lean_inc(v___x_124_);
v___x_150_ = l_Lean_Syntax_node2(v___x_124_, v___x_147_, v___x_149_, v___x_122_);
v___x_151_ = ((lean_object*)(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__29));
lean_inc(v___x_124_);
v___x_152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_124_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
lean_inc(v___x_124_);
v___x_153_ = l_Lean_Syntax_node3(v___x_124_, v___x_135_, v___x_146_, v___x_150_, v___x_152_);
lean_inc(v___x_124_);
v___x_154_ = l_Lean_Syntax_node2(v___x_124_, v___x_131_, v___x_134_, v___x_153_);
v___x_155_ = l_Lean_Syntax_node2(v___x_124_, v___x_125_, v___x_130_, v___x_154_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_a_111_);
return v___x_156_;
}
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_MacroTrace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_MacroTrace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Meta(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_MacroTrace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_MacroTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_MacroTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_MacroTrace(builtin);
}
#ifdef __cplusplus
}
#endif
