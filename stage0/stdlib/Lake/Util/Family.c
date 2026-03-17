// Lean compiler output
// Module: Lake.Util.Family
// Imports: public meta import Init.Data.ToString.Name import Init.Data.ToString public import Init.Notation
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static const lean_string_object l_Lake_familyDef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_familyDef___closed__0 = (const lean_object*)&l_Lake_familyDef___closed__0_value;
static const lean_string_object l_Lake_familyDef___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "familyDef"};
static const lean_object* l_Lake_familyDef___closed__1 = (const lean_object*)&l_Lake_familyDef___closed__1_value;
static const lean_ctor_object l_Lake_familyDef___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_familyDef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_familyDef___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__2_value_aux_0),((lean_object*)&l_Lake_familyDef___closed__1_value),LEAN_SCALAR_PTR_LITERAL(59, 240, 138, 11, 51, 35, 78, 153)}};
static const lean_object* l_Lake_familyDef___closed__2 = (const lean_object*)&l_Lake_familyDef___closed__2_value;
static const lean_string_object l_Lake_familyDef___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lake_familyDef___closed__3 = (const lean_object*)&l_Lake_familyDef___closed__3_value;
static const lean_ctor_object l_Lake_familyDef___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_familyDef___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lake_familyDef___closed__4 = (const lean_object*)&l_Lake_familyDef___closed__4_value;
static const lean_string_object l_Lake_familyDef___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lake_familyDef___closed__5 = (const lean_object*)&l_Lake_familyDef___closed__5_value;
static const lean_ctor_object l_Lake_familyDef___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_familyDef___closed__5_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lake_familyDef___closed__6 = (const lean_object*)&l_Lake_familyDef___closed__6_value;
static const lean_string_object l_Lake_familyDef___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lake_familyDef___closed__7 = (const lean_object*)&l_Lake_familyDef___closed__7_value;
static const lean_ctor_object l_Lake_familyDef___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_familyDef___closed__7_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lake_familyDef___closed__8 = (const lean_object*)&l_Lake_familyDef___closed__8_value;
static const lean_ctor_object l_Lake_familyDef___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__8_value)}};
static const lean_object* l_Lake_familyDef___closed__9 = (const lean_object*)&l_Lake_familyDef___closed__9_value;
static const lean_ctor_object l_Lake_familyDef___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__6_value),((lean_object*)&l_Lake_familyDef___closed__9_value)}};
static const lean_object* l_Lake_familyDef___closed__10 = (const lean_object*)&l_Lake_familyDef___closed__10_value;
static const lean_string_object l_Lake_familyDef___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "family_def "};
static const lean_object* l_Lake_familyDef___closed__11 = (const lean_object*)&l_Lake_familyDef___closed__11_value;
static const lean_ctor_object l_Lake_familyDef___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__11_value)}};
static const lean_object* l_Lake_familyDef___closed__12 = (const lean_object*)&l_Lake_familyDef___closed__12_value;
static const lean_ctor_object l_Lake_familyDef___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__4_value),((lean_object*)&l_Lake_familyDef___closed__10_value),((lean_object*)&l_Lake_familyDef___closed__12_value)}};
static const lean_object* l_Lake_familyDef___closed__13 = (const lean_object*)&l_Lake_familyDef___closed__13_value;
static const lean_string_object l_Lake_familyDef___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_familyDef___closed__14 = (const lean_object*)&l_Lake_familyDef___closed__14_value;
static const lean_ctor_object l_Lake_familyDef___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_familyDef___closed__14_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_familyDef___closed__15 = (const lean_object*)&l_Lake_familyDef___closed__15_value;
static const lean_ctor_object l_Lake_familyDef___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__15_value)}};
static const lean_object* l_Lake_familyDef___closed__16 = (const lean_object*)&l_Lake_familyDef___closed__16_value;
static const lean_ctor_object l_Lake_familyDef___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__4_value),((lean_object*)&l_Lake_familyDef___closed__13_value),((lean_object*)&l_Lake_familyDef___closed__16_value)}};
static const lean_object* l_Lake_familyDef___closed__17 = (const lean_object*)&l_Lake_familyDef___closed__17_value;
static const lean_string_object l_Lake_familyDef___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lake_familyDef___closed__18 = (const lean_object*)&l_Lake_familyDef___closed__18_value;
static const lean_ctor_object l_Lake_familyDef___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__18_value)}};
static const lean_object* l_Lake_familyDef___closed__19 = (const lean_object*)&l_Lake_familyDef___closed__19_value;
static const lean_ctor_object l_Lake_familyDef___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__4_value),((lean_object*)&l_Lake_familyDef___closed__17_value),((lean_object*)&l_Lake_familyDef___closed__19_value)}};
static const lean_object* l_Lake_familyDef___closed__20 = (const lean_object*)&l_Lake_familyDef___closed__20_value;
static const lean_ctor_object l_Lake_familyDef___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__4_value),((lean_object*)&l_Lake_familyDef___closed__20_value),((lean_object*)&l_Lake_familyDef___closed__16_value)}};
static const lean_object* l_Lake_familyDef___closed__21 = (const lean_object*)&l_Lake_familyDef___closed__21_value;
static const lean_string_object l_Lake_familyDef___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lake_familyDef___closed__22 = (const lean_object*)&l_Lake_familyDef___closed__22_value;
static const lean_ctor_object l_Lake_familyDef___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_familyDef___closed__22_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lake_familyDef___closed__23 = (const lean_object*)&l_Lake_familyDef___closed__23_value;
static const lean_ctor_object l_Lake_familyDef___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_familyDef___closed__24 = (const lean_object*)&l_Lake_familyDef___closed__24_value;
static const lean_ctor_object l_Lake_familyDef___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__4_value),((lean_object*)&l_Lake_familyDef___closed__21_value),((lean_object*)&l_Lake_familyDef___closed__24_value)}};
static const lean_object* l_Lake_familyDef___closed__25 = (const lean_object*)&l_Lake_familyDef___closed__25_value;
static const lean_string_object l_Lake_familyDef___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_familyDef___closed__26 = (const lean_object*)&l_Lake_familyDef___closed__26_value;
static const lean_ctor_object l_Lake_familyDef___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__26_value)}};
static const lean_object* l_Lake_familyDef___closed__27 = (const lean_object*)&l_Lake_familyDef___closed__27_value;
static const lean_ctor_object l_Lake_familyDef___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__4_value),((lean_object*)&l_Lake_familyDef___closed__25_value),((lean_object*)&l_Lake_familyDef___closed__27_value)}};
static const lean_object* l_Lake_familyDef___closed__28 = (const lean_object*)&l_Lake_familyDef___closed__28_value;
static const lean_ctor_object l_Lake_familyDef___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__4_value),((lean_object*)&l_Lake_familyDef___closed__28_value),((lean_object*)&l_Lake_familyDef___closed__24_value)}};
static const lean_object* l_Lake_familyDef___closed__29 = (const lean_object*)&l_Lake_familyDef___closed__29_value;
static const lean_ctor_object l_Lake_familyDef___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_familyDef___closed__2_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_familyDef___closed__29_value)}};
static const lean_object* l_Lake_familyDef___closed__30 = (const lean_object*)&l_Lake_familyDef___closed__30_value;
LEAN_EXPORT const lean_object* l_Lake_familyDef = (const lean_object*)&l_Lake_familyDef___closed__30_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__0_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__1 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__1_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__2 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__2_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__3 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__3_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__4 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__4_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__5 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__5_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__6 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__6_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__7 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__7_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__8 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__8_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "axiom"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__9 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__9_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__10 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__10_value;
static const lean_array_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__11 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__11_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__12 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__12_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__13 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__13_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__14 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__14_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_=_"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__15 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__15_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(167, 251, 107, 62, 223, 239, 203, 78)}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__16 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__16_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__17 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__17_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__18 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__18_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__19 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__19_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "FamilyDef"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21;
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(149, 240, 255, 22, 138, 196, 41, 195)}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__22 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__22_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_familyDef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(249, 224, 215, 22, 102, 9, 211, 189)}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__24 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__24_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__23_value)}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__25 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__25_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__26 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__26_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__24_value),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__26_value)}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__27 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__27_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__28 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__28_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__29 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__29_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__30 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__30_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__31 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__31_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__32 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__32_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__33 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__33_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__34 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__34_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__35 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__35_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(184, 175, 53, 50, 212, 152, 178, 8)}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__36 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__36_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__37 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__37_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__38 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__38_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__42 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__42_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__44 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__44_value;
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45_value;
static lean_once_cell_t l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46;
static const lean_array_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__47 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__47_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unknown family `"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__48 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__48_value;
static const lean_string_object l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__49 = (const lean_object*)&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__49_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__20));
v___x_97_ = l_String_toRawSubstring_x27(v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46(void){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Array_mkArray0(lean_box(0));
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1(lean_object* v_x_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = ((lean_object*)(l_Lake_familyDef___closed__2));
lean_inc(v_x_147_);
v___x_151_ = l_Lean_Syntax_isOfKind(v_x_147_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec_ref(v_a_148_);
lean_dec(v_x_147_);
v___x_152_ = lean_box(1);
v___x_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v_a_149_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_id_157_; lean_object* v___x_158_; lean_object* v_fam_159_; lean_object* v___x_160_; lean_object* v_idx_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_272_; lean_object* v___x_339_; 
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = l_Lean_Syntax_getArg(v_x_147_, v___x_154_);
v___x_156_ = lean_unsigned_to_nat(2u);
v_id_157_ = l_Lean_Syntax_getArg(v_x_147_, v___x_156_);
v___x_158_ = lean_unsigned_to_nat(4u);
v_fam_159_ = l_Lean_Syntax_getArg(v_x_147_, v___x_158_);
v___x_160_ = lean_unsigned_to_nat(5u);
v_idx_161_ = l_Lean_Syntax_getArg(v_x_147_, v___x_160_);
v___x_162_ = lean_unsigned_to_nat(7u);
v___x_163_ = l_Lean_Syntax_getArg(v_x_147_, v___x_162_);
lean_dec(v_x_147_);
v___x_339_ = l_Lean_Syntax_getOptional_x3f(v___x_155_);
lean_dec(v___x_155_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v___x_340_; 
v___x_340_ = lean_box(0);
v___y_272_ = v___x_340_;
goto v___jp_271_;
}
else
{
lean_object* v_val_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_val_341_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_339_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_val_341_);
lean_dec(v___x_339_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_val_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
v___y_272_ = v___x_346_;
goto v___jp_271_;
}
}
}
v___jp_164_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_inc_ref(v___y_165_);
v___x_179_ = l_Array_append___redArg(v___y_165_, v___y_178_);
lean_dec_ref(v___y_178_);
lean_inc(v___y_171_);
lean_inc(v___y_166_);
v___x_180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_180_, 0, v___y_166_);
lean_ctor_set(v___x_180_, 1, v___y_171_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
v___x_181_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__0));
v___x_182_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__1));
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_183_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___x_181_, v___x_182_);
v___x_184_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__2));
lean_inc(v___y_166_);
v___x_185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_185_, 0, v___y_166_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__3));
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_187_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___x_181_, v___x_186_);
v___x_188_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__4));
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_189_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___x_181_, v___x_188_);
lean_inc(v___y_171_);
lean_inc(v___y_166_);
v___x_190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_190_, 0, v___y_166_);
lean_ctor_set(v___x_190_, 1, v___y_171_);
lean_ctor_set(v___x_190_, 2, v___y_165_);
lean_inc_ref(v___x_190_);
lean_inc(v___y_166_);
v___x_191_ = l_Lean_Syntax_node1(v___y_166_, v___x_189_, v___x_190_);
v___x_192_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__5));
v___x_193_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__6));
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_194_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___x_192_, v___x_193_);
lean_inc(v___y_166_);
v___x_195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_195_, 0, v___y_166_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_inc_ref_n(v___x_190_, 3);
lean_inc(v___y_166_);
v___x_196_ = l_Lean_Syntax_node4(v___y_166_, v___x_194_, v___x_195_, v___x_190_, v___x_190_, v___x_190_);
lean_inc(v___x_191_);
lean_inc(v___y_166_);
v___x_197_ = l_Lean_Syntax_node2(v___y_166_, v___x_187_, v___x_191_, v___x_196_);
lean_inc(v___y_171_);
lean_inc(v___y_166_);
v___x_198_ = l_Lean_Syntax_node1(v___y_166_, v___y_171_, v___x_197_);
v___x_199_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__7));
lean_inc(v___y_166_);
v___x_200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_200_, 0, v___y_166_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
lean_inc(v___y_166_);
v___x_201_ = l_Lean_Syntax_node3(v___y_166_, v___x_183_, v___x_185_, v___x_198_, v___x_200_);
lean_inc(v___y_171_);
lean_inc(v___y_166_);
v___x_202_ = l_Lean_Syntax_node1(v___y_166_, v___y_171_, v___x_201_);
v___x_203_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__8));
lean_inc_ref(v___y_177_);
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_204_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___y_177_, v___x_203_);
lean_inc(v___y_166_);
v___x_205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_205_, 0, v___y_166_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
lean_inc(v___y_166_);
v___x_206_ = l_Lean_Syntax_node1(v___y_166_, v___x_204_, v___x_205_);
lean_inc(v___y_171_);
lean_inc(v___y_166_);
v___x_207_ = l_Lean_Syntax_node1(v___y_166_, v___y_171_, v___x_206_);
lean_inc_ref_n(v___x_190_, 4);
lean_inc(v___x_207_);
lean_inc(v___y_174_);
lean_inc(v___y_166_);
v___x_208_ = l_Lean_Syntax_node7(v___y_166_, v___y_174_, v___x_180_, v___x_202_, v___x_207_, v___x_190_, v___x_190_, v___x_190_, v___x_190_);
v___x_209_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__9));
lean_inc_ref(v___y_177_);
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_210_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___y_177_, v___x_209_);
lean_inc(v___y_166_);
v___x_211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_211_, 0, v___y_166_);
lean_ctor_set(v___x_211_, 1, v___x_209_);
v___x_212_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__10));
lean_inc_ref(v___y_177_);
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_213_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___y_177_, v___x_212_);
v___x_214_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__11));
v___x_215_ = lean_box(2);
lean_inc(v___y_171_);
v___x_216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___y_171_);
lean_ctor_set(v___x_216_, 2, v___x_214_);
v___x_217_ = lean_mk_empty_array_with_capacity(v___x_156_);
lean_inc(v___y_169_);
v___x_218_ = lean_array_push(v___x_217_, v___y_169_);
v___x_219_ = lean_array_push(v___x_218_, v___x_216_);
v___x_220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_220_, 0, v___x_215_);
lean_ctor_set(v___x_220_, 1, v___x_213_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
v___x_221_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__12));
lean_inc_ref(v___y_177_);
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_222_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___y_177_, v___x_221_);
v___x_223_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__13));
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_224_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___x_181_, v___x_223_);
v___x_225_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__14));
lean_inc(v___y_166_);
v___x_226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_226_, 0, v___y_166_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__16));
v___x_228_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__17));
lean_inc(v___y_166_);
v___x_229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_229_, 0, v___y_166_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
lean_inc(v___x_163_);
lean_inc(v___y_166_);
v___x_230_ = l_Lean_Syntax_node3(v___y_166_, v___x_227_, v___y_170_, v___x_229_, v___x_163_);
lean_inc_ref(v___x_226_);
lean_inc(v___x_224_);
lean_inc(v___y_166_);
v___x_231_ = l_Lean_Syntax_node2(v___y_166_, v___x_224_, v___x_226_, v___x_230_);
lean_inc_ref(v___x_190_);
lean_inc(v___x_222_);
lean_inc(v___y_166_);
v___x_232_ = l_Lean_Syntax_node2(v___y_166_, v___x_222_, v___x_190_, v___x_231_);
lean_inc(v___y_166_);
v___x_233_ = l_Lean_Syntax_node3(v___y_166_, v___x_210_, v___x_211_, v___x_220_, v___x_232_);
lean_inc(v___y_176_);
lean_inc(v___y_166_);
v___x_234_ = l_Lean_Syntax_node2(v___y_166_, v___y_176_, v___x_208_, v___x_233_);
lean_inc_ref_n(v___x_190_, 6);
lean_inc(v___y_166_);
v___x_235_ = l_Lean_Syntax_node7(v___y_166_, v___y_174_, v___x_190_, v___x_190_, v___x_207_, v___x_190_, v___x_190_, v___x_190_, v___x_190_);
v___x_236_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__18));
lean_inc_ref(v___y_177_);
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_237_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___y_177_, v___x_236_);
lean_inc(v___y_166_);
v___x_238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_238_, 0, v___y_166_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
v___x_239_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__19));
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_240_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___x_181_, v___x_239_);
v___x_241_ = lean_obj_once(&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21, &l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21_once, _init_l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__21);
v___x_242_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__22));
v___x_243_ = l_Lean_addMacroScope(v___y_172_, v___x_242_, v___y_175_);
v___x_244_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__27));
lean_inc(v___y_166_);
v___x_245_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_245_, 0, v___y_166_);
lean_ctor_set(v___x_245_, 1, v___x_241_);
lean_ctor_set(v___x_245_, 2, v___x_243_);
lean_ctor_set(v___x_245_, 3, v___x_244_);
lean_inc(v___y_171_);
lean_inc(v___y_166_);
v___x_246_ = l_Lean_Syntax_node3(v___y_166_, v___y_171_, v_fam_159_, v_idx_161_, v___x_163_);
lean_inc(v___y_166_);
v___x_247_ = l_Lean_Syntax_node2(v___y_166_, v___x_240_, v___x_245_, v___x_246_);
lean_inc(v___y_166_);
v___x_248_ = l_Lean_Syntax_node2(v___y_166_, v___x_224_, v___x_226_, v___x_247_);
lean_inc_ref(v___x_190_);
lean_inc(v___y_166_);
v___x_249_ = l_Lean_Syntax_node2(v___y_166_, v___x_222_, v___x_190_, v___x_248_);
v___x_250_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__28));
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_251_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___y_177_, v___x_250_);
v___x_252_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__29));
lean_inc(v___y_166_);
v___x_253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_253_, 0, v___y_166_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__30));
lean_inc_ref(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_255_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___x_181_, v___x_254_);
v___x_256_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__31));
lean_inc(v___y_166_);
v___x_257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_257_, 0, v___y_166_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
lean_inc(v___y_171_);
lean_inc(v___y_166_);
v___x_258_ = l_Lean_Syntax_node1(v___y_166_, v___y_171_, v___y_169_);
v___x_259_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__32));
lean_inc(v___y_166_);
v___x_260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_260_, 0, v___y_166_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_inc(v___y_166_);
v___x_261_ = l_Lean_Syntax_node3(v___y_166_, v___x_255_, v___x_257_, v___x_258_, v___x_260_);
v___x_262_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__33));
v___x_263_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__34));
v___x_264_ = l_Lean_Name_mkStr4(v___y_167_, v___y_168_, v___x_262_, v___x_263_);
lean_inc_ref_n(v___x_190_, 2);
lean_inc(v___y_166_);
v___x_265_ = l_Lean_Syntax_node2(v___y_166_, v___x_264_, v___x_190_, v___x_190_);
lean_inc_ref(v___x_190_);
lean_inc(v___y_166_);
v___x_266_ = l_Lean_Syntax_node4(v___y_166_, v___x_251_, v___x_253_, v___x_261_, v___x_265_, v___x_190_);
lean_inc_ref(v___x_190_);
lean_inc(v___y_166_);
v___x_267_ = l_Lean_Syntax_node6(v___y_166_, v___x_237_, v___x_191_, v___x_238_, v___x_190_, v___x_190_, v___x_249_, v___x_266_);
lean_inc(v___y_166_);
v___x_268_ = l_Lean_Syntax_node2(v___y_166_, v___y_176_, v___x_235_, v___x_267_);
v___x_269_ = l_Lean_Syntax_node2(v___y_166_, v___y_171_, v___x_234_, v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___y_173_);
return v___x_270_;
}
v___jp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_name_275_; lean_object* v___x_276_; 
v___x_273_ = l_Lean_TSyntax_getId(v_fam_159_);
v___x_274_ = l_Lean_extractMacroScopes(v___x_273_);
v_name_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_name_275_);
lean_dec_ref(v___x_274_);
lean_inc_ref(v_a_148_);
lean_inc(v_name_275_);
v___x_276_ = l_Lean_Macro_resolveGlobalName(v_name_275_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
if (lean_obj_tag(v_a_277_) == 1)
{
lean_object* v_head_278_; lean_object* v_a_279_; lean_object* v_fst_280_; lean_object* v_quotContext_281_; lean_object* v_currMacroScope_282_; lean_object* v_ref_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_name_275_);
v_head_278_ = lean_ctor_get(v_a_277_, 0);
lean_inc(v_head_278_);
lean_dec_ref(v_a_277_);
v_a_279_ = lean_ctor_get(v___x_276_, 1);
lean_inc(v_a_279_);
lean_dec_ref(v___x_276_);
v_fst_280_ = lean_ctor_get(v_head_278_, 0);
lean_inc(v_fst_280_);
lean_dec(v_head_278_);
v_quotContext_281_ = lean_ctor_get(v_a_148_, 1);
lean_inc(v_quotContext_281_);
v_currMacroScope_282_ = lean_ctor_get(v_a_148_, 2);
lean_inc(v_currMacroScope_282_);
v_ref_283_ = lean_ctor_get(v_a_148_, 5);
lean_inc(v_ref_283_);
lean_dec_ref(v_a_148_);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_mk_empty_array_with_capacity(v___x_284_);
lean_inc(v_idx_161_);
v___x_286_ = lean_array_push(v___x_285_, v_idx_161_);
lean_inc(v_fam_159_);
v___x_287_ = l_Lean_Syntax_mkApp(v_fam_159_, v___x_286_);
v___x_288_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__36));
v___x_289_ = l_Lean_Name_append(v___x_288_, v_fst_280_);
v___x_290_ = l_Lean_TSyntax_getId(v_id_157_);
v___x_291_ = l_Lean_Name_append(v___x_289_, v___x_290_);
v___x_292_ = l_Lean_mkIdentFrom(v_id_157_, v___x_291_, v___x_151_);
lean_dec(v_id_157_);
v___x_293_ = 0;
v___x_294_ = l_Lean_SourceInfo_fromRef(v_ref_283_, v___x_293_);
lean_dec(v_ref_283_);
v___x_295_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__38));
v___x_296_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__39));
v___x_297_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__40));
v___x_298_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__41));
v___x_299_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__43));
v___x_300_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__45));
v___x_301_ = lean_obj_once(&l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46, &l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46_once, _init_l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__46);
if (lean_obj_tag(v___y_272_) == 1)
{
lean_object* v_val_302_; lean_object* v___x_303_; 
v_val_302_ = lean_ctor_get(v___y_272_, 0);
lean_inc(v_val_302_);
lean_dec_ref(v___y_272_);
v___x_303_ = l_Array_mkArray1___redArg(v_val_302_);
v___y_165_ = v___x_301_;
v___y_166_ = v___x_294_;
v___y_167_ = v___x_296_;
v___y_168_ = v___x_297_;
v___y_169_ = v___x_292_;
v___y_170_ = v___x_287_;
v___y_171_ = v___x_295_;
v___y_172_ = v_quotContext_281_;
v___y_173_ = v_a_279_;
v___y_174_ = v___x_300_;
v___y_175_ = v_currMacroScope_282_;
v___y_176_ = v___x_299_;
v___y_177_ = v___x_298_;
v___y_178_ = v___x_303_;
goto v___jp_164_;
}
else
{
lean_object* v___x_304_; 
lean_dec(v___y_272_);
v___x_304_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__47));
v___y_165_ = v___x_301_;
v___y_166_ = v___x_294_;
v___y_167_ = v___x_296_;
v___y_168_ = v___x_297_;
v___y_169_ = v___x_292_;
v___y_170_ = v___x_287_;
v___y_171_ = v___x_295_;
v___y_172_ = v_quotContext_281_;
v___y_173_ = v_a_279_;
v___y_174_ = v___x_300_;
v___y_175_ = v_currMacroScope_282_;
v___y_176_ = v___x_299_;
v___y_177_ = v___x_298_;
v___y_178_ = v___x_304_;
goto v___jp_164_;
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_a_277_);
lean_dec(v___y_272_);
lean_dec(v___x_163_);
lean_dec(v_idx_161_);
lean_dec(v_id_157_);
v_a_305_ = lean_ctor_get(v___x_276_, 1);
lean_inc(v_a_305_);
lean_dec_ref(v___x_276_);
v___x_306_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__48));
v___x_307_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_275_, v___x_151_);
v___x_308_ = lean_string_append(v___x_306_, v___x_307_);
lean_dec_ref(v___x_307_);
v___x_309_ = ((lean_object*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___closed__49));
v___x_310_ = lean_string_append(v___x_308_, v___x_309_);
v___x_311_ = l_Lean_Macro_throwErrorAt___redArg(v_fam_159_, v___x_310_, v_a_148_, v_a_305_);
lean_dec(v_fam_159_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_a_313_ = lean_ctor_get(v___x_311_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_311_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_312_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v_a_321_; lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_a_321_ = lean_ctor_get(v___x_311_, 0);
v_a_322_ = lean_ctor_get(v___x_311_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_311_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_inc(v_a_321_);
lean_dec(v___x_311_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_321_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
else
{
lean_object* v_a_330_; lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_name_275_);
lean_dec(v___y_272_);
lean_dec(v___x_163_);
lean_dec(v_idx_161_);
lean_dec(v_fam_159_);
lean_dec(v_id_157_);
lean_dec_ref(v_a_148_);
v_a_330_ = lean_ctor_get(v___x_276_, 0);
v_a_331_ = lean_ctor_get(v___x_276_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_276_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_inc(v_a_330_);
lean_dec(v___x_276_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_330_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Family(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Family(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Family(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Family(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Family(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Family(builtin);
}
#ifdef __cplusplus
}
#endif
