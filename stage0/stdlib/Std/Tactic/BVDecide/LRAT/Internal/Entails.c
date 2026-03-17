// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Entails
// Imports: public import Init.PropLemmas
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
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LRAT"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊨_"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__5_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_1),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_2),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_3),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 130, 112, 117, 243, 29, 235, 233)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_4),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(190, 231, 56, 71, 46, 94, 101, 126)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊨ "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10_value),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8__ = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_1),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_2),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Entails.eval"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Entails"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(203, 198, 196, 172, 3, 180, 146, 93)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(28, 139, 224, 246, 205, 136, 122, 12)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_1),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_2),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_3),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 130, 112, 117, 243, 29, 235, 233)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_4),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(228, 30, 234, 204, 37, 39, 206, 127)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_5),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(63, 10, 186, 100, 241, 140, 240, 104)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊭_"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_1),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_2),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_3),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 130, 112, 117, 243, 29, 235, 233)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_4),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 207, 17, 12, 22, 244, 166, 51)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊭ "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3_value),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad__ = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 6, .m_data = "term¬_"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 122, 71, 36, 131, 84, 176, 236)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "¬"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_1),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_2),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_1),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_2),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_0),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_1),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_2),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_3),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 130, 112, 117, 243, 29, 235, 233)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5));
v___x_47_ = l_String_toRawSubstring_x27(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1(lean_object* v_x_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6));
lean_inc(v_x_70_);
v___x_74_ = l_Lean_Syntax_isOfKind(v_x_70_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec_ref(v_a_71_);
lean_dec(v_x_70_);
v___x_75_ = lean_box(1);
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v_a_72_);
return v___x_76_;
}
else
{
lean_object* v_quotContext_77_; lean_object* v_currMacroScope_78_; lean_object* v_ref_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_quotContext_77_ = lean_ctor_get(v_a_71_, 1);
lean_inc(v_quotContext_77_);
v_currMacroScope_78_ = lean_ctor_get(v_a_71_, 2);
lean_inc(v_currMacroScope_78_);
v_ref_79_ = lean_ctor_get(v_a_71_, 5);
lean_inc(v_ref_79_);
lean_dec_ref(v_a_71_);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_Lean_Syntax_getArg(v_x_70_, v___x_80_);
v___x_82_ = lean_unsigned_to_nat(2u);
v___x_83_ = l_Lean_Syntax_getArg(v_x_70_, v___x_82_);
lean_dec(v_x_70_);
v___x_84_ = 0;
v___x_85_ = l_Lean_SourceInfo_fromRef(v_ref_79_, v___x_84_);
lean_dec(v_ref_79_);
v___x_86_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4));
v___x_87_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6, &l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6);
v___x_88_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9));
v___x_89_ = l_Lean_addMacroScope(v_quotContext_77_, v___x_88_, v_currMacroScope_78_);
v___x_90_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12));
lean_inc(v___x_85_);
v___x_91_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_91_, 0, v___x_85_);
lean_ctor_set(v___x_91_, 1, v___x_87_);
lean_ctor_set(v___x_91_, 2, v___x_89_);
lean_ctor_set(v___x_91_, 3, v___x_90_);
v___x_92_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14));
lean_inc(v___x_85_);
v___x_93_ = l_Lean_Syntax_node2(v___x_85_, v___x_92_, v___x_81_, v___x_83_);
v___x_94_ = l_Lean_Syntax_node2(v___x_85_, v___x_86_, v___x_91_, v___x_93_);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v_a_72_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1(lean_object* v_x_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4));
lean_inc(v_x_99_);
v___x_103_ = l_Lean_Syntax_isOfKind(v_x_99_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_x_99_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v_a_101_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = l_Lean_Syntax_getArg(v_x_99_, v___x_106_);
v___x_108_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1));
lean_inc(v___x_107_);
v___x_109_ = l_Lean_Syntax_isOfKind(v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec(v___x_107_);
lean_dec(v_x_99_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_a_101_);
return v___x_111_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = l_Lean_Syntax_getArg(v_x_99_, v___x_112_);
lean_dec(v_x_99_);
v___x_114_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_113_);
v___x_115_ = l_Lean_Syntax_matchesNull(v___x_113_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v___x_113_);
lean_dec(v___x_107_);
v___x_116_ = lean_box(0);
v___x_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_a_101_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_ref_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_118_ = l_Lean_Syntax_getArg(v___x_113_, v___x_106_);
v___x_119_ = l_Lean_Syntax_getArg(v___x_113_, v___x_112_);
lean_dec(v___x_113_);
v_ref_120_ = l_Lean_replaceRef(v___x_107_, v_a_100_);
lean_dec(v___x_107_);
v___x_121_ = 0;
v___x_122_ = l_Lean_SourceInfo_fromRef(v_ref_120_, v___x_121_);
lean_dec(v_ref_120_);
v___x_123_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6));
v___x_124_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9));
lean_inc(v___x_122_);
v___x_125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_122_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = l_Lean_Syntax_node3(v___x_122_, v___x_123_, v___x_118_, v___x_125_, v___x_119_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v_a_101_);
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___boxed(lean_object* v_x_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1(v_x_128_, v_a_129_, v_a_130_);
lean_dec(v_a_129_);
return v_res_131_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10));
v___x_177_ = l_String_toRawSubstring_x27(v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1(lean_object* v_x_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1));
lean_inc(v_x_196_);
v___x_200_ = l_Lean_Syntax_isOfKind(v_x_196_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec_ref(v_a_197_);
lean_dec(v_x_196_);
v___x_201_ = lean_box(1);
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_a_198_);
return v___x_202_;
}
else
{
lean_object* v_quotContext_203_; lean_object* v_currMacroScope_204_; lean_object* v_ref_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_quotContext_203_ = lean_ctor_get(v_a_197_, 1);
lean_inc(v_quotContext_203_);
v_currMacroScope_204_ = lean_ctor_get(v_a_197_, 2);
lean_inc(v_currMacroScope_204_);
v_ref_205_ = lean_ctor_get(v_a_197_, 5);
lean_inc(v_ref_205_);
lean_dec_ref(v_a_197_);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = l_Lean_Syntax_getArg(v_x_196_, v___x_206_);
v___x_208_ = lean_unsigned_to_nat(2u);
v___x_209_ = l_Lean_Syntax_getArg(v_x_196_, v___x_208_);
lean_dec(v_x_196_);
v___x_210_ = 0;
v___x_211_ = l_Lean_SourceInfo_fromRef(v_ref_205_, v___x_210_);
lean_dec(v_ref_205_);
v___x_212_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1));
v___x_213_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2));
lean_inc(v___x_211_);
v___x_214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_211_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4));
v___x_216_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6));
v___x_217_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7));
lean_inc(v___x_211_);
v___x_218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_211_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9));
v___x_220_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11, &l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11);
v___x_221_ = lean_box(0);
lean_inc(v_currMacroScope_204_);
lean_inc(v_quotContext_203_);
v___x_222_ = l_Lean_addMacroScope(v_quotContext_203_, v___x_221_, v_currMacroScope_204_);
v___x_223_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14));
lean_inc(v___x_211_);
v___x_224_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_224_, 0, v___x_211_);
lean_ctor_set(v___x_224_, 1, v___x_220_);
lean_ctor_set(v___x_224_, 2, v___x_222_);
lean_ctor_set(v___x_224_, 3, v___x_223_);
lean_inc(v___x_211_);
v___x_225_ = l_Lean_Syntax_node1(v___x_211_, v___x_219_, v___x_224_);
lean_inc(v___x_211_);
v___x_226_ = l_Lean_Syntax_node2(v___x_211_, v___x_216_, v___x_218_, v___x_225_);
v___x_227_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4));
v___x_228_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6, &l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6);
v___x_229_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9));
v___x_230_ = l_Lean_addMacroScope(v_quotContext_203_, v___x_229_, v_currMacroScope_204_);
v___x_231_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16));
lean_inc(v___x_211_);
v___x_232_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_232_, 0, v___x_211_);
lean_ctor_set(v___x_232_, 1, v___x_228_);
lean_ctor_set(v___x_232_, 2, v___x_230_);
lean_ctor_set(v___x_232_, 3, v___x_231_);
v___x_233_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14));
lean_inc(v___x_211_);
v___x_234_ = l_Lean_Syntax_node2(v___x_211_, v___x_233_, v___x_207_, v___x_209_);
lean_inc(v___x_211_);
v___x_235_ = l_Lean_Syntax_node2(v___x_211_, v___x_227_, v___x_232_, v___x_234_);
v___x_236_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17));
lean_inc(v___x_211_);
v___x_237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_211_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
lean_inc(v___x_211_);
v___x_238_ = l_Lean_Syntax_node3(v___x_211_, v___x_215_, v___x_226_, v___x_235_, v___x_237_);
v___x_239_ = l_Lean_Syntax_node2(v___x_211_, v___x_212_, v___x_214_, v___x_238_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v_a_198_);
return v___x_240_;
}
}
}
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
}
#ifdef __cplusplus
}
#endif
