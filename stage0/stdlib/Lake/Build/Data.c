// Lean compiler output
// Module: Lake.Build.Data
// Imports: public import Lake.Build.Key public import Lake.Util.Family public import Lake.Config.Dynlib public import Lake.Config.Kinds public meta import Lake.Config.Kinds public meta import Lake.Util.Name import all Lake.Config.Kinds import Lake.Util.Name
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Macro_resolveNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
extern lean_object* l_Lake_Module_keyword;
extern lean_object* l_Lake_Package_keyword;
LEAN_EXPORT lean_object* l_Lake_OptDataKind_anonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instInhabited(lean_object*);
LEAN_EXPORT uint8_t l_Lake_OptDataKind_isAnonymous___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OptDataKind_isAnonymous___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_OptDataKind_isAnonymous(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OptDataKind_isAnonymous___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instOfDataKind___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instOfDataKind___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instOfDataKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instOfDataKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instCoeOutName___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instCoeOutName___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_OptDataKind_instCoeOutName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_OptDataKind_instCoeOutName___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OptDataKind_instCoeOutName___closed__0 = (const lean_object*)&l_Lake_OptDataKind_instCoeOutName___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instCoeOutName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instToString___lam__0(lean_object*);
static const lean_closure_object l_Lake_OptDataKind_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_OptDataKind_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OptDataKind_instToString___closed__0 = (const lean_object*)&l_Lake_OptDataKind_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instToString(lean_object*);
static const lean_string_object l_Lake_dataTypeDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_dataTypeDecl___closed__0 = (const lean_object*)&l_Lake_dataTypeDecl___closed__0_value;
static const lean_string_object l_Lake_dataTypeDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dataTypeDecl"};
static const lean_object* l_Lake_dataTypeDecl___closed__1 = (const lean_object*)&l_Lake_dataTypeDecl___closed__1_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_dataTypeDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__2_value_aux_0),((lean_object*)&l_Lake_dataTypeDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 208, 230, 96, 184, 13, 30, 26)}};
static const lean_object* l_Lake_dataTypeDecl___closed__2 = (const lean_object*)&l_Lake_dataTypeDecl___closed__2_value;
static const lean_string_object l_Lake_dataTypeDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lake_dataTypeDecl___closed__3 = (const lean_object*)&l_Lake_dataTypeDecl___closed__3_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lake_dataTypeDecl___closed__4 = (const lean_object*)&l_Lake_dataTypeDecl___closed__4_value;
static const lean_string_object l_Lake_dataTypeDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lake_dataTypeDecl___closed__5 = (const lean_object*)&l_Lake_dataTypeDecl___closed__5_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lake_dataTypeDecl___closed__6 = (const lean_object*)&l_Lake_dataTypeDecl___closed__6_value;
static const lean_string_object l_Lake_dataTypeDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lake_dataTypeDecl___closed__7 = (const lean_object*)&l_Lake_dataTypeDecl___closed__7_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__7_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lake_dataTypeDecl___closed__8 = (const lean_object*)&l_Lake_dataTypeDecl___closed__8_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__8_value)}};
static const lean_object* l_Lake_dataTypeDecl___closed__9 = (const lean_object*)&l_Lake_dataTypeDecl___closed__9_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__6_value),((lean_object*)&l_Lake_dataTypeDecl___closed__9_value)}};
static const lean_object* l_Lake_dataTypeDecl___closed__10 = (const lean_object*)&l_Lake_dataTypeDecl___closed__10_value;
static const lean_string_object l_Lake_dataTypeDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "data_type "};
static const lean_object* l_Lake_dataTypeDecl___closed__11 = (const lean_object*)&l_Lake_dataTypeDecl___closed__11_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__11_value)}};
static const lean_object* l_Lake_dataTypeDecl___closed__12 = (const lean_object*)&l_Lake_dataTypeDecl___closed__12_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__10_value),((lean_object*)&l_Lake_dataTypeDecl___closed__12_value)}};
static const lean_object* l_Lake_dataTypeDecl___closed__13 = (const lean_object*)&l_Lake_dataTypeDecl___closed__13_value;
static const lean_string_object l_Lake_dataTypeDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_dataTypeDecl___closed__14 = (const lean_object*)&l_Lake_dataTypeDecl___closed__14_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__14_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_dataTypeDecl___closed__15 = (const lean_object*)&l_Lake_dataTypeDecl___closed__15_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__15_value)}};
static const lean_object* l_Lake_dataTypeDecl___closed__16 = (const lean_object*)&l_Lake_dataTypeDecl___closed__16_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__13_value),((lean_object*)&l_Lake_dataTypeDecl___closed__16_value)}};
static const lean_object* l_Lake_dataTypeDecl___closed__17 = (const lean_object*)&l_Lake_dataTypeDecl___closed__17_value;
static const lean_string_object l_Lake_dataTypeDecl___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lake_dataTypeDecl___closed__18 = (const lean_object*)&l_Lake_dataTypeDecl___closed__18_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__18_value)}};
static const lean_object* l_Lake_dataTypeDecl___closed__19 = (const lean_object*)&l_Lake_dataTypeDecl___closed__19_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__17_value),((lean_object*)&l_Lake_dataTypeDecl___closed__19_value)}};
static const lean_object* l_Lake_dataTypeDecl___closed__20 = (const lean_object*)&l_Lake_dataTypeDecl___closed__20_value;
static const lean_string_object l_Lake_dataTypeDecl___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lake_dataTypeDecl___closed__21 = (const lean_object*)&l_Lake_dataTypeDecl___closed__21_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__21_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lake_dataTypeDecl___closed__22 = (const lean_object*)&l_Lake_dataTypeDecl___closed__22_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_dataTypeDecl___closed__23 = (const lean_object*)&l_Lake_dataTypeDecl___closed__23_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__20_value),((lean_object*)&l_Lake_dataTypeDecl___closed__23_value)}};
static const lean_object* l_Lake_dataTypeDecl___closed__24 = (const lean_object*)&l_Lake_dataTypeDecl___closed__24_value;
static const lean_ctor_object l_Lake_dataTypeDecl___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__2_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__24_value)}};
static const lean_object* l_Lake_dataTypeDecl___closed__25 = (const lean_object*)&l_Lake_dataTypeDecl___closed__25_value;
LEAN_EXPORT const lean_object* l_Lake_dataTypeDecl = (const lean_object*)&l_Lake_dataTypeDecl___closed__25_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "family_def"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DataKind"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value;
static lean_once_cell_t l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(85, 248, 95, 223, 234, 189, 212, 227)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(57, 137, 77, 253, 49, 4, 64, 32)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27_value),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29_value)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Name.isAnonymous_iff_eq_anonymous"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52_value;
static lean_once_cell_t l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "isAnonymous_iff_eq_anonymous"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(154, 178, 141, 167, 199, 52, 205, 105)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value),LEAN_SCALAR_PTR_LITERAL(10, 45, 172, 138, 28, 252, 34, 255)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(94, 175, 90, 84, 80, 182, 246, 68)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value),LEAN_SCALAR_PTR_LITERAL(158, 41, 113, 154, 180, 181, 171, 218)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DataType"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(33, 68, 121, 193, 122, 109, 136, 152)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "familyDef"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(59, 240, 138, 11, 51, 35, 78, 153)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value;
static lean_once_cell_t l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71;
static const lean_array_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instDataKindUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lake_instDataKindUnit___closed__0 = (const lean_object*)&l_Lake_instDataKindUnit___closed__0_value;
static const lean_ctor_object l_Lake_instDataKindUnit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindUnit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 16, 7, 142, 223, 189, 92, 152)}};
static const lean_object* l_Lake_instDataKindUnit___closed__1 = (const lean_object*)&l_Lake_instDataKindUnit___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instDataKindUnit = (const lean_object*)&l_Lake_instDataKindUnit___closed__1_value;
static const lean_string_object l_Lake_instDataKindBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bool"};
static const lean_object* l_Lake_instDataKindBool___closed__0 = (const lean_object*)&l_Lake_instDataKindBool___closed__0_value;
static const lean_ctor_object l_Lake_instDataKindBool___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindBool___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 123, 29, 106, 21, 111, 175, 162)}};
static const lean_object* l_Lake_instDataKindBool___closed__1 = (const lean_object*)&l_Lake_instDataKindBool___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instDataKindBool = (const lean_object*)&l_Lake_instDataKindBool___closed__1_value;
static const lean_string_object l_Lake_instDataKindFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "filepath"};
static const lean_object* l_Lake_instDataKindFilePath___closed__0 = (const lean_object*)&l_Lake_instDataKindFilePath___closed__0_value;
static const lean_ctor_object l_Lake_instDataKindFilePath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindFilePath___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 79, 67, 231, 21, 24, 25, 253)}};
static const lean_object* l_Lake_instDataKindFilePath___closed__1 = (const lean_object*)&l_Lake_instDataKindFilePath___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instDataKindFilePath = (const lean_object*)&l_Lake_instDataKindFilePath___closed__1_value;
static const lean_string_object l_Lake_instDataKindDynlib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "dynlib"};
static const lean_object* l_Lake_instDataKindDynlib___closed__0 = (const lean_object*)&l_Lake_instDataKindDynlib___closed__0_value;
static const lean_ctor_object l_Lake_instDataKindDynlib___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instDataKindDynlib___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 146, 131, 63, 203, 243, 150, 200)}};
static const lean_object* l_Lake_instDataKindDynlib___closed__1 = (const lean_object*)&l_Lake_instDataKindDynlib___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instDataKindDynlib = (const lean_object*)&l_Lake_instDataKindDynlib___closed__1_value;
static const lean_string_object l_Lake_builtinFacetCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "builtinFacetCommand"};
static const lean_object* l_Lake_builtinFacetCommand___closed__0 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__0_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_builtinFacetCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_builtinFacetCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 118, 124, 184, 192, 242, 254, 60)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__1 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__1_value;
static const lean_string_object l_Lake_builtinFacetCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "builtin_facet "};
static const lean_object* l_Lake_builtinFacetCommand___closed__2 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__2_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_builtinFacetCommand___closed__2_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__3 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__3_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__10_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__3_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__4 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__4_value;
static const lean_string_object l_Lake_builtinFacetCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l_Lake_builtinFacetCommand___closed__5 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__5_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_builtinFacetCommand___closed__5_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__6 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__6_value;
static const lean_string_object l_Lake_builtinFacetCommand___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lake_builtinFacetCommand___closed__7 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__7_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_builtinFacetCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__8 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__8_value;
static const lean_string_object l_Lake_builtinFacetCommand___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " @ "};
static const lean_object* l_Lake_builtinFacetCommand___closed__9 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__9_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_builtinFacetCommand___closed__9_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__10 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__10_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__16_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__10_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__11 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__11_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_builtinFacetCommand___closed__8_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__11_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__12 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__12_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_builtinFacetCommand___closed__6_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__12_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__13 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__13_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__6_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__13_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__14 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__14_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__4_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__14_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__15 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__15_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__15_value),((lean_object*)&l_Lake_dataTypeDecl___closed__16_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__16 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__16_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__16_value),((lean_object*)&l_Lake_dataTypeDecl___closed__19_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__17 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__17_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__17_value),((lean_object*)&l_Lake_dataTypeDecl___closed__16_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__18 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__18_value;
static const lean_string_object l_Lake_builtinFacetCommand___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lake_builtinFacetCommand___closed__19 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__19_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_builtinFacetCommand___closed__19_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__20 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__20_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__18_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__20_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__21 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__21_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_builtinFacetCommand___closed__21_value),((lean_object*)&l_Lake_dataTypeDecl___closed__23_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__22 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__22_value;
static const lean_ctor_object l_Lake_builtinFacetCommand___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_builtinFacetCommand___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_builtinFacetCommand___closed__22_value)}};
static const lean_object* l_Lake_builtinFacetCommand___closed__23 = (const lean_object*)&l_Lake_builtinFacetCommand___closed__23_value;
LEAN_EXPORT const lean_object* l_Lake_builtinFacetCommand = (const lean_object*)&l_Lake_builtinFacetCommand___closed__23_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5_value;
static lean_once_cell_t l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(29, 67, 225, 118, 155, 2, 197, 97)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "expose"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8_value;
static lean_once_cell_t l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(170, 113, 233, 77, 243, 78, 243, 129)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "FamilyDef"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value;
static lean_once_cell_t l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(149, 240, 255, 22, 138, 196, 41, 195)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23_value;
static lean_once_cell_t l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_++_"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(90, 69, 86, 178, 149, 48, 216, 23)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "++"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inferInstanceAs"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29_value;
static lean_once_cell_t l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(120, 135, 37, 233, 184, 173, 222, 47)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__32 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__32_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__33 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__33_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "cannot generate facet declaration name from facet name"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__34 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__34_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Facet"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__35 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__35_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___boxed(lean_object**);
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "FacetOut"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 147, 236, 126, 195, 124, 217, 255)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unknown target namespace `"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "unknown or ambiguous target namespace `"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_facetDataDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "facetDataDecl"};
static const lean_object* l_Lake_facetDataDecl___closed__0 = (const lean_object*)&l_Lake_facetDataDecl___closed__0_value;
static const lean_ctor_object l_Lake_facetDataDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_facetDataDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_facetDataDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_facetDataDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 4, 106, 30, 217, 73, 248, 83)}};
static const lean_object* l_Lake_facetDataDecl___closed__1 = (const lean_object*)&l_Lake_facetDataDecl___closed__1_value;
static const lean_string_object l_Lake_facetDataDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "facet_data "};
static const lean_object* l_Lake_facetDataDecl___closed__2 = (const lean_object*)&l_Lake_facetDataDecl___closed__2_value;
static const lean_ctor_object l_Lake_facetDataDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_facetDataDecl___closed__2_value)}};
static const lean_object* l_Lake_facetDataDecl___closed__3 = (const lean_object*)&l_Lake_facetDataDecl___closed__3_value;
static const lean_ctor_object l_Lake_facetDataDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__10_value),((lean_object*)&l_Lake_facetDataDecl___closed__3_value)}};
static const lean_object* l_Lake_facetDataDecl___closed__4 = (const lean_object*)&l_Lake_facetDataDecl___closed__4_value;
static const lean_ctor_object l_Lake_facetDataDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_facetDataDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__16_value)}};
static const lean_object* l_Lake_facetDataDecl___closed__5 = (const lean_object*)&l_Lake_facetDataDecl___closed__5_value;
static const lean_ctor_object l_Lake_facetDataDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_facetDataDecl___closed__5_value),((lean_object*)&l_Lake_dataTypeDecl___closed__16_value)}};
static const lean_object* l_Lake_facetDataDecl___closed__6 = (const lean_object*)&l_Lake_facetDataDecl___closed__6_value;
static const lean_ctor_object l_Lake_facetDataDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_facetDataDecl___closed__6_value),((lean_object*)&l_Lake_dataTypeDecl___closed__19_value)}};
static const lean_object* l_Lake_facetDataDecl___closed__7 = (const lean_object*)&l_Lake_facetDataDecl___closed__7_value;
static const lean_ctor_object l_Lake_facetDataDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_facetDataDecl___closed__7_value),((lean_object*)&l_Lake_dataTypeDecl___closed__23_value)}};
static const lean_object* l_Lake_facetDataDecl___closed__8 = (const lean_object*)&l_Lake_facetDataDecl___closed__8_value;
static const lean_ctor_object l_Lake_facetDataDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_facetDataDecl___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_facetDataDecl___closed__8_value)}};
static const lean_object* l_Lake_facetDataDecl___closed__9 = (const lean_object*)&l_Lake_facetDataDecl___closed__9_value;
LEAN_EXPORT const lean_object* l_Lake_facetDataDecl = (const lean_object*)&l_Lake_facetDataDecl___closed__9_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(249, 224, 215, 22, 102, 9, 211, 189)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1_value),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3_value)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7_value)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9_value)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11_value)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__14 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__14_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_packageDataDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "packageDataDecl"};
static const lean_object* l_Lake_packageDataDecl___closed__0 = (const lean_object*)&l_Lake_packageDataDecl___closed__0_value;
static const lean_ctor_object l_Lake_packageDataDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_packageDataDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_packageDataDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_packageDataDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 160, 98, 6, 154, 122, 231, 28)}};
static const lean_object* l_Lake_packageDataDecl___closed__1 = (const lean_object*)&l_Lake_packageDataDecl___closed__1_value;
static const lean_string_object l_Lake_packageDataDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "package_data "};
static const lean_object* l_Lake_packageDataDecl___closed__2 = (const lean_object*)&l_Lake_packageDataDecl___closed__2_value;
static const lean_ctor_object l_Lake_packageDataDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_packageDataDecl___closed__2_value)}};
static const lean_object* l_Lake_packageDataDecl___closed__3 = (const lean_object*)&l_Lake_packageDataDecl___closed__3_value;
static const lean_ctor_object l_Lake_packageDataDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__10_value),((lean_object*)&l_Lake_packageDataDecl___closed__3_value)}};
static const lean_object* l_Lake_packageDataDecl___closed__4 = (const lean_object*)&l_Lake_packageDataDecl___closed__4_value;
static const lean_ctor_object l_Lake_packageDataDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_packageDataDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__16_value)}};
static const lean_object* l_Lake_packageDataDecl___closed__5 = (const lean_object*)&l_Lake_packageDataDecl___closed__5_value;
static const lean_ctor_object l_Lake_packageDataDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_packageDataDecl___closed__5_value),((lean_object*)&l_Lake_dataTypeDecl___closed__19_value)}};
static const lean_object* l_Lake_packageDataDecl___closed__6 = (const lean_object*)&l_Lake_packageDataDecl___closed__6_value;
static const lean_ctor_object l_Lake_packageDataDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_packageDataDecl___closed__6_value),((lean_object*)&l_Lake_dataTypeDecl___closed__23_value)}};
static const lean_object* l_Lake_packageDataDecl___closed__7 = (const lean_object*)&l_Lake_packageDataDecl___closed__7_value;
static const lean_ctor_object l_Lake_packageDataDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_packageDataDecl___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_packageDataDecl___closed__7_value)}};
static const lean_object* l_Lake_packageDataDecl___closed__8 = (const lean_object*)&l_Lake_packageDataDecl___closed__8_value;
LEAN_EXPORT const lean_object* l_Lake_packageDataDecl = (const lean_object*)&l_Lake_packageDataDecl___closed__8_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "facet_data"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_moduleDataDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "moduleDataDecl"};
static const lean_object* l_Lake_moduleDataDecl___closed__0 = (const lean_object*)&l_Lake_moduleDataDecl___closed__0_value;
static const lean_ctor_object l_Lake_moduleDataDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_moduleDataDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_moduleDataDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_moduleDataDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 236, 99, 131, 4, 228, 74, 185)}};
static const lean_object* l_Lake_moduleDataDecl___closed__1 = (const lean_object*)&l_Lake_moduleDataDecl___closed__1_value;
static const lean_string_object l_Lake_moduleDataDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "module_data "};
static const lean_object* l_Lake_moduleDataDecl___closed__2 = (const lean_object*)&l_Lake_moduleDataDecl___closed__2_value;
static const lean_ctor_object l_Lake_moduleDataDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_moduleDataDecl___closed__2_value)}};
static const lean_object* l_Lake_moduleDataDecl___closed__3 = (const lean_object*)&l_Lake_moduleDataDecl___closed__3_value;
static const lean_ctor_object l_Lake_moduleDataDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__10_value),((lean_object*)&l_Lake_moduleDataDecl___closed__3_value)}};
static const lean_object* l_Lake_moduleDataDecl___closed__4 = (const lean_object*)&l_Lake_moduleDataDecl___closed__4_value;
static const lean_ctor_object l_Lake_moduleDataDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_moduleDataDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__16_value)}};
static const lean_object* l_Lake_moduleDataDecl___closed__5 = (const lean_object*)&l_Lake_moduleDataDecl___closed__5_value;
static const lean_ctor_object l_Lake_moduleDataDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_moduleDataDecl___closed__5_value),((lean_object*)&l_Lake_dataTypeDecl___closed__19_value)}};
static const lean_object* l_Lake_moduleDataDecl___closed__6 = (const lean_object*)&l_Lake_moduleDataDecl___closed__6_value;
static const lean_ctor_object l_Lake_moduleDataDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_moduleDataDecl___closed__6_value),((lean_object*)&l_Lake_dataTypeDecl___closed__23_value)}};
static const lean_object* l_Lake_moduleDataDecl___closed__7 = (const lean_object*)&l_Lake_moduleDataDecl___closed__7_value;
static const lean_ctor_object l_Lake_moduleDataDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_moduleDataDecl___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_moduleDataDecl___closed__7_value)}};
static const lean_object* l_Lake_moduleDataDecl___closed__8 = (const lean_object*)&l_Lake_moduleDataDecl___closed__8_value;
LEAN_EXPORT const lean_object* l_Lake_moduleDataDecl = (const lean_object*)&l_Lake_moduleDataDecl___closed__8_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_libraryDataDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "libraryDataDecl"};
static const lean_object* l_Lake_libraryDataDecl___closed__0 = (const lean_object*)&l_Lake_libraryDataDecl___closed__0_value;
static const lean_ctor_object l_Lake_libraryDataDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_libraryDataDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_libraryDataDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_libraryDataDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 126, 44, 46, 121, 159, 210, 189)}};
static const lean_object* l_Lake_libraryDataDecl___closed__1 = (const lean_object*)&l_Lake_libraryDataDecl___closed__1_value;
static const lean_string_object l_Lake_libraryDataDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "library_data "};
static const lean_object* l_Lake_libraryDataDecl___closed__2 = (const lean_object*)&l_Lake_libraryDataDecl___closed__2_value;
static const lean_ctor_object l_Lake_libraryDataDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_libraryDataDecl___closed__2_value)}};
static const lean_object* l_Lake_libraryDataDecl___closed__3 = (const lean_object*)&l_Lake_libraryDataDecl___closed__3_value;
static const lean_ctor_object l_Lake_libraryDataDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__10_value),((lean_object*)&l_Lake_libraryDataDecl___closed__3_value)}};
static const lean_object* l_Lake_libraryDataDecl___closed__4 = (const lean_object*)&l_Lake_libraryDataDecl___closed__4_value;
static const lean_ctor_object l_Lake_libraryDataDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_libraryDataDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__16_value)}};
static const lean_object* l_Lake_libraryDataDecl___closed__5 = (const lean_object*)&l_Lake_libraryDataDecl___closed__5_value;
static const lean_ctor_object l_Lake_libraryDataDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_libraryDataDecl___closed__5_value),((lean_object*)&l_Lake_dataTypeDecl___closed__19_value)}};
static const lean_object* l_Lake_libraryDataDecl___closed__6 = (const lean_object*)&l_Lake_libraryDataDecl___closed__6_value;
static const lean_ctor_object l_Lake_libraryDataDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_libraryDataDecl___closed__6_value),((lean_object*)&l_Lake_dataTypeDecl___closed__23_value)}};
static const lean_object* l_Lake_libraryDataDecl___closed__7 = (const lean_object*)&l_Lake_libraryDataDecl___closed__7_value;
static const lean_ctor_object l_Lake_libraryDataDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_libraryDataDecl___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_libraryDataDecl___closed__7_value)}};
static const lean_object* l_Lake_libraryDataDecl___closed__8 = (const lean_object*)&l_Lake_libraryDataDecl___closed__8_value;
LEAN_EXPORT const lean_object* l_Lake_libraryDataDecl = (const lean_object*)&l_Lake_libraryDataDecl___closed__8_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_customDataDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "customDataDecl"};
static const lean_object* l_Lake_customDataDecl___closed__0 = (const lean_object*)&l_Lake_customDataDecl___closed__0_value;
static const lean_ctor_object l_Lake_customDataDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_customDataDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_customDataDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_customDataDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 51, 251, 114, 214, 40, 109, 65)}};
static const lean_object* l_Lake_customDataDecl___closed__1 = (const lean_object*)&l_Lake_customDataDecl___closed__1_value;
static const lean_string_object l_Lake_customDataDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "custom_data "};
static const lean_object* l_Lake_customDataDecl___closed__2 = (const lean_object*)&l_Lake_customDataDecl___closed__2_value;
static const lean_ctor_object l_Lake_customDataDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_customDataDecl___closed__2_value)}};
static const lean_object* l_Lake_customDataDecl___closed__3 = (const lean_object*)&l_Lake_customDataDecl___closed__3_value;
static const lean_ctor_object l_Lake_customDataDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__10_value),((lean_object*)&l_Lake_customDataDecl___closed__3_value)}};
static const lean_object* l_Lake_customDataDecl___closed__4 = (const lean_object*)&l_Lake_customDataDecl___closed__4_value;
static const lean_ctor_object l_Lake_customDataDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_customDataDecl___closed__4_value),((lean_object*)&l_Lake_dataTypeDecl___closed__16_value)}};
static const lean_object* l_Lake_customDataDecl___closed__5 = (const lean_object*)&l_Lake_customDataDecl___closed__5_value;
static const lean_ctor_object l_Lake_customDataDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_customDataDecl___closed__5_value),((lean_object*)&l_Lake_dataTypeDecl___closed__16_value)}};
static const lean_object* l_Lake_customDataDecl___closed__6 = (const lean_object*)&l_Lake_customDataDecl___closed__6_value;
static const lean_ctor_object l_Lake_customDataDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_customDataDecl___closed__6_value),((lean_object*)&l_Lake_dataTypeDecl___closed__19_value)}};
static const lean_object* l_Lake_customDataDecl___closed__7 = (const lean_object*)&l_Lake_customDataDecl___closed__7_value;
static const lean_ctor_object l_Lake_customDataDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_dataTypeDecl___closed__4_value),((lean_object*)&l_Lake_customDataDecl___closed__7_value),((lean_object*)&l_Lake_dataTypeDecl___closed__23_value)}};
static const lean_object* l_Lake_customDataDecl___closed__8 = (const lean_object*)&l_Lake_customDataDecl___closed__8_value;
static const lean_ctor_object l_Lake_customDataDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_customDataDecl___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lake_customDataDecl___closed__8_value)}};
static const lean_object* l_Lake_customDataDecl___closed__9 = (const lean_object*)&l_Lake_customDataDecl___closed__9_value;
LEAN_EXPORT const lean_object* l_Lake_customDataDecl = (const lean_object*)&l_Lake_customDataDecl___closed__9_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2_value)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "CustomOut"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4_value;
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_dataTypeDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(104, 189, 225, 248, 232, 79, 182, 148)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OptDataKind_anonymous(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instInhabited(lean_object* v_00_u03b1_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT uint8_t l_Lake_OptDataKind_isAnonymous___redArg(lean_object* v_self_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = l_Lean_Name_isAnonymous(v_self_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_isAnonymous___redArg___boxed(lean_object* v_self_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lake_OptDataKind_isAnonymous___redArg(v_self_7_);
lean_dec(v_self_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_Lake_OptDataKind_isAnonymous(lean_object* v_00_u03b1_10_, lean_object* v_self_11_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = l_Lean_Name_isAnonymous(v_self_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_isAnonymous___boxed(lean_object* v_00_u03b1_13_, lean_object* v_self_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lake_OptDataKind_isAnonymous(v_00_u03b1_13_, v_self_14_);
lean_dec(v_self_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instOfDataKind___redArg(lean_object* v_inst_17_){
_start:
{
lean_inc(v_inst_17_);
return v_inst_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instOfDataKind___redArg___boxed(lean_object* v_inst_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lake_OptDataKind_instOfDataKind___redArg(v_inst_18_);
lean_dec(v_inst_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instOfDataKind(lean_object* v_00_u03b1_20_, lean_object* v_inst_21_){
_start:
{
lean_inc(v_inst_21_);
return v_inst_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instOfDataKind___boxed(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_OptDataKind_instOfDataKind(v_00_u03b1_22_, v_inst_23_);
lean_dec(v_inst_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instCoeOutName___lam__0(lean_object* v_x_25_){
_start:
{
lean_inc(v_x_25_);
return v_x_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instCoeOutName___lam__0___boxed(lean_object* v_x_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lake_OptDataKind_instCoeOutName___lam__0(v_x_26_);
lean_dec(v_x_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instCoeOutName(lean_object* v_00_u03b1_29_){
_start:
{
lean_object* v___f_30_; 
v___f_30_ = ((lean_object*)(l_Lake_OptDataKind_instCoeOutName___closed__0));
return v___f_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instToString___lam__0(lean_object* v_x_31_){
_start:
{
uint8_t v___x_32_; lean_object* v___x_33_; 
v___x_32_ = 1;
v___x_33_ = l_Lean_Name_toString(v_x_31_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_OptDataKind_instToString(lean_object* v_00_u03b1_35_){
_start:
{
lean_object* v___f_36_; 
v___f_36_ = ((lean_object*)(l_Lake_OptDataKind_instToString___closed__0));
return v___f_36_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23));
v___x_151_ = l_String_toRawSubstring_x27(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52));
v___x_223_ = l_String_toRawSubstring_x27(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71(void){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Array_mkArray0(lean_box(0));
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1(lean_object* v_x_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lake_dataTypeDecl___closed__2));
lean_inc(v_x_262_);
v___x_266_ = l_Lean_Syntax_isOfKind(v_x_262_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref(v_a_263_);
lean_dec(v_x_262_);
v___x_267_ = lean_box(1);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v_a_264_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v_kind_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_366_; lean_object* v___x_382_; 
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = l_Lean_Syntax_getArg(v_x_262_, v___x_269_);
v___x_271_ = lean_unsigned_to_nat(2u);
v_kind_272_ = l_Lean_Syntax_getArg(v_x_262_, v___x_271_);
v___x_273_ = lean_unsigned_to_nat(4u);
v___x_274_ = l_Lean_Syntax_getArg(v_x_262_, v___x_273_);
lean_dec(v_x_262_);
v___x_382_ = l_Lean_Syntax_getOptional_x3f(v___x_270_);
lean_dec(v___x_270_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v___x_383_; 
v___x_383_ = lean_box(0);
v___y_366_ = v___x_383_;
goto v___jp_365_;
}
else
{
lean_object* v_val_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v_val_384_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_382_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_val_384_);
lean_dec(v___x_382_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_val_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
v___y_366_ = v___x_389_;
goto v___jp_365_;
}
}
}
v___jp_275_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
lean_inc_ref(v___y_283_);
v___x_285_ = l_Array_append___redArg(v___y_283_, v___y_284_);
lean_dec_ref(v___y_284_);
lean_inc(v___y_278_);
lean_inc(v___y_276_);
v___x_286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_286_, 0, v___y_276_);
lean_ctor_set(v___x_286_, 1, v___y_278_);
lean_ctor_set(v___x_286_, 2, v___x_285_);
v___x_287_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0));
lean_inc(v___y_276_);
v___x_288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_288_, 0, v___y_276_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_276_);
v___x_290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_290_, 0, v___y_276_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2));
lean_inc(v___y_276_);
v___x_292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_292_, 0, v___y_276_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
lean_inc(v___x_274_);
lean_inc_ref(v___x_292_);
lean_inc(v___y_279_);
lean_inc_ref(v___x_290_);
lean_inc(v___y_276_);
v___x_293_ = l_Lean_Syntax_node8(v___y_276_, v___y_277_, v___x_286_, v___x_288_, v_kind_272_, v___x_290_, v___y_282_, v___y_279_, v___x_292_, v___x_274_);
v___x_294_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7));
v___x_295_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9));
lean_inc(v___y_278_);
lean_inc(v___y_276_);
v___x_296_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_296_, 0, v___y_276_);
lean_ctor_set(v___x_296_, 1, v___y_278_);
lean_ctor_set(v___x_296_, 2, v___y_283_);
v___x_297_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10));
v___x_298_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11));
lean_inc(v___y_276_);
v___x_299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_299_, 0, v___y_276_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
lean_inc(v___y_276_);
v___x_300_ = l_Lean_Syntax_node1(v___y_276_, v___x_298_, v___x_299_);
lean_inc(v___y_278_);
lean_inc(v___y_276_);
v___x_301_ = l_Lean_Syntax_node1(v___y_276_, v___y_278_, v___x_300_);
lean_inc_ref_n(v___x_296_, 6);
lean_inc(v___y_276_);
v___x_302_ = l_Lean_Syntax_node7(v___y_276_, v___x_295_, v___x_296_, v___x_296_, v___x_301_, v___x_296_, v___x_296_, v___x_296_, v___x_296_);
v___x_303_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12));
v___x_304_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13));
v___x_305_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16));
lean_inc_ref(v___x_296_);
lean_inc(v___y_276_);
v___x_306_ = l_Lean_Syntax_node1(v___y_276_, v___x_305_, v___x_296_);
lean_inc(v___y_276_);
v___x_307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_307_, 0, v___y_276_);
lean_ctor_set(v___x_307_, 1, v___x_303_);
v___x_308_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18));
v___x_309_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20));
v___x_310_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22));
v___x_311_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24);
v___x_312_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25));
lean_inc(v___y_280_);
lean_inc(v___y_281_);
v___x_313_ = l_Lean_addMacroScope(v___y_281_, v___x_312_, v___y_280_);
v___x_314_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30));
lean_inc(v___y_276_);
v___x_315_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_315_, 0, v___y_276_);
lean_ctor_set(v___x_315_, 1, v___x_311_);
lean_ctor_set(v___x_315_, 2, v___x_313_);
lean_ctor_set(v___x_315_, 3, v___x_314_);
lean_inc(v___y_278_);
lean_inc(v___y_276_);
v___x_316_ = l_Lean_Syntax_node1(v___y_276_, v___y_278_, v___x_274_);
lean_inc(v___y_276_);
v___x_317_ = l_Lean_Syntax_node2(v___y_276_, v___x_310_, v___x_315_, v___x_316_);
lean_inc(v___y_276_);
v___x_318_ = l_Lean_Syntax_node2(v___y_276_, v___x_309_, v___x_290_, v___x_317_);
lean_inc_ref(v___x_296_);
lean_inc(v___y_276_);
v___x_319_ = l_Lean_Syntax_node2(v___y_276_, v___x_308_, v___x_296_, v___x_318_);
v___x_320_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32));
v___x_321_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34));
v___x_322_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35));
lean_inc(v___y_276_);
v___x_323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_323_, 0, v___y_276_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36));
lean_inc(v___y_276_);
v___x_325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_325_, 0, v___y_276_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38));
v___x_327_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39));
lean_inc(v___y_276_);
v___x_328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_328_, 0, v___y_276_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42));
v___x_330_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44));
v___x_331_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45));
v___x_332_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46));
lean_inc(v___y_276_);
v___x_333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_333_, 0, v___y_276_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
v___x_334_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48));
lean_inc_ref(v___x_296_);
lean_inc(v___y_276_);
v___x_335_ = l_Lean_Syntax_node1(v___y_276_, v___x_334_, v___x_296_);
v___x_336_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49));
lean_inc(v___y_276_);
v___x_337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_337_, 0, v___y_276_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51));
v___x_339_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53);
v___x_340_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56));
v___x_341_ = l_Lean_addMacroScope(v___y_281_, v___x_340_, v___y_280_);
v___x_342_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59));
lean_inc(v___y_276_);
v___x_343_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_343_, 0, v___y_276_);
lean_ctor_set(v___x_343_, 1, v___x_339_);
lean_ctor_set(v___x_343_, 2, v___x_341_);
lean_ctor_set(v___x_343_, 3, v___x_342_);
lean_inc_ref_n(v___x_296_, 2);
lean_inc(v___y_276_);
v___x_344_ = l_Lean_Syntax_node3(v___y_276_, v___x_338_, v___x_296_, v___x_296_, v___x_343_);
lean_inc(v___y_278_);
lean_inc(v___y_276_);
v___x_345_ = l_Lean_Syntax_node1(v___y_276_, v___y_278_, v___x_344_);
v___x_346_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60));
lean_inc(v___y_276_);
v___x_347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_347_, 0, v___y_276_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
lean_inc(v___y_278_);
lean_inc(v___y_276_);
v___x_348_ = l_Lean_Syntax_node3(v___y_276_, v___y_278_, v___x_337_, v___x_345_, v___x_347_);
lean_inc_ref_n(v___x_296_, 3);
lean_inc(v___y_276_);
v___x_349_ = l_Lean_Syntax_node6(v___y_276_, v___x_332_, v___x_333_, v___x_335_, v___x_296_, v___x_296_, v___x_348_, v___x_296_);
lean_inc(v___y_278_);
lean_inc(v___y_276_);
v___x_350_ = l_Lean_Syntax_node1(v___y_276_, v___y_278_, v___x_349_);
lean_inc(v___y_276_);
v___x_351_ = l_Lean_Syntax_node1(v___y_276_, v___x_330_, v___x_350_);
lean_inc(v___y_276_);
v___x_352_ = l_Lean_Syntax_node1(v___y_276_, v___x_329_, v___x_351_);
lean_inc(v___y_276_);
v___x_353_ = l_Lean_Syntax_node2(v___y_276_, v___x_326_, v___x_328_, v___x_352_);
lean_inc(v___y_278_);
lean_inc(v___y_276_);
v___x_354_ = l_Lean_Syntax_node3(v___y_276_, v___y_278_, v___y_279_, v___x_325_, v___x_353_);
v___x_355_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61));
lean_inc(v___y_276_);
v___x_356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_356_, 0, v___y_276_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
lean_inc(v___y_276_);
v___x_357_ = l_Lean_Syntax_node3(v___y_276_, v___x_321_, v___x_323_, v___x_354_, v___x_356_);
v___x_358_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64));
lean_inc_ref_n(v___x_296_, 2);
lean_inc(v___y_276_);
v___x_359_ = l_Lean_Syntax_node2(v___y_276_, v___x_358_, v___x_296_, v___x_296_);
lean_inc_ref(v___x_296_);
lean_inc(v___y_276_);
v___x_360_ = l_Lean_Syntax_node4(v___y_276_, v___x_320_, v___x_292_, v___x_357_, v___x_359_, v___x_296_);
lean_inc_ref(v___x_296_);
lean_inc(v___y_276_);
v___x_361_ = l_Lean_Syntax_node6(v___y_276_, v___x_304_, v___x_306_, v___x_307_, v___x_296_, v___x_296_, v___x_319_, v___x_360_);
lean_inc(v___y_276_);
v___x_362_ = l_Lean_Syntax_node2(v___y_276_, v___x_294_, v___x_302_, v___x_361_);
v___x_363_ = l_Lean_Syntax_node2(v___y_276_, v___y_278_, v___x_293_, v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_a_264_);
return v___x_364_;
}
v___jp_365_:
{
lean_object* v_quotContext_367_; lean_object* v_currMacroScope_368_; lean_object* v_ref_369_; lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_quotContext_367_ = lean_ctor_get(v_a_263_, 1);
lean_inc(v_quotContext_367_);
v_currMacroScope_368_ = lean_ctor_get(v_a_263_, 2);
lean_inc(v_currMacroScope_368_);
v_ref_369_ = lean_ctor_get(v_a_263_, 5);
lean_inc(v_ref_369_);
lean_dec_ref(v_a_263_);
v___x_370_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66));
v___x_371_ = 0;
v___x_372_ = l_Lean_mkCIdentFrom(v_ref_369_, v___x_370_, v___x_371_);
v___x_373_ = l_Lean_TSyntax_getId(v_kind_272_);
lean_inc(v_kind_272_);
v___x_374_ = l_Lake_Name_quoteFrom(v_kind_272_, v___x_373_, v___x_371_);
v___x_375_ = l_Lean_SourceInfo_fromRef(v_ref_369_, v___x_371_);
lean_dec(v_ref_369_);
v___x_376_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_377_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70));
v___x_378_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_366_) == 1)
{
lean_object* v_val_379_; lean_object* v___x_380_; 
v_val_379_ = lean_ctor_get(v___y_366_, 0);
lean_inc(v_val_379_);
lean_dec_ref(v___y_366_);
v___x_380_ = l_Array_mkArray1___redArg(v_val_379_);
v___y_276_ = v___x_375_;
v___y_277_ = v___x_377_;
v___y_278_ = v___x_376_;
v___y_279_ = v___x_374_;
v___y_280_ = v_currMacroScope_368_;
v___y_281_ = v_quotContext_367_;
v___y_282_ = v___x_372_;
v___y_283_ = v___x_378_;
v___y_284_ = v___x_380_;
goto v___jp_275_;
}
else
{
lean_object* v___x_381_; 
lean_dec(v___y_366_);
v___x_381_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72));
v___y_276_ = v___x_375_;
v___y_277_ = v___x_377_;
v___y_278_ = v___x_376_;
v___y_279_ = v___x_374_;
v___y_280_ = v_currMacroScope_368_;
v___y_281_ = v_quotContext_367_;
v___y_282_ = v___x_372_;
v___y_283_ = v___x_378_;
v___y_284_ = v___x_381_;
goto v___jp_275_;
}
}
}
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5));
v___x_480_ = l_String_toRawSubstring_x27(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8));
v___x_485_ = l_String_toRawSubstring_x27(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15));
v___x_494_ = l_String_toRawSubstring_x27(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23));
v___x_505_ = l_String_toRawSubstring_x27(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29));
v___x_513_ = l_String_toRawSubstring_x27(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(lean_object* v___x_524_, lean_object* v___x_525_, lean_object* v___x_526_, lean_object* v_fam_527_, lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v___x_530_, uint8_t v___x_531_, lean_object* v___y_532_, lean_object* v_name_533_, lean_object* v_ns_534_, lean_object* v___x_535_, uint8_t v___x_536_, lean_object* v_tk_537_, lean_object* v___y_538_, lean_object* v___x_539_, lean_object* v_____r_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v_id_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___x_739_; uint8_t v___y_741_; 
v___x_739_ = l_Lean_TSyntax_getId(v_name_533_);
if (lean_obj_tag(v___y_538_) == 0)
{
v___y_741_ = v___x_531_;
goto v___jp_740_;
}
else
{
v___y_741_ = v___x_536_;
goto v___jp_740_;
}
v___jp_543_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_inc_ref(v___y_557_);
v___x_561_ = l_Array_append___redArg(v___y_557_, v___y_560_);
lean_dec_ref(v___y_560_);
lean_inc(v___y_550_);
lean_inc(v___y_559_);
v___x_562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_562_, 0, v___y_559_);
lean_ctor_set(v___x_562_, 1, v___y_550_);
lean_ctor_set(v___x_562_, 2, v___x_561_);
v___x_563_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14));
v___x_564_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0));
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_565_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___x_563_, v___x_564_);
v___x_566_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1));
lean_inc(v___y_559_);
v___x_567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_567_, 0, v___y_559_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2));
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_569_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___x_563_, v___x_568_);
v___x_570_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15));
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_571_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___x_563_, v___x_570_);
lean_inc(v___y_550_);
lean_inc(v___y_559_);
v___x_572_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_572_, 0, v___y_559_);
lean_ctor_set(v___x_572_, 1, v___y_550_);
lean_ctor_set(v___x_572_, 2, v___y_557_);
lean_inc_ref(v___x_572_);
lean_inc(v___y_559_);
v___x_573_ = l_Lean_Syntax_node1(v___y_559_, v___x_571_, v___x_572_);
v___x_574_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3));
v___x_575_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4));
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_576_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___x_574_, v___x_575_);
v___x_577_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6);
v___x_578_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7));
lean_inc(v___y_554_);
lean_inc(v___y_553_);
v___x_579_ = l_Lean_addMacroScope(v___y_553_, v___x_578_, v___y_554_);
v___x_580_ = lean_box(0);
lean_inc(v___y_559_);
v___x_581_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_581_, 0, v___y_559_);
lean_ctor_set(v___x_581_, 1, v___x_577_);
lean_ctor_set(v___x_581_, 2, v___x_579_);
lean_ctor_set(v___x_581_, 3, v___x_580_);
lean_inc_ref(v___x_572_);
lean_inc(v___x_576_);
lean_inc(v___y_559_);
v___x_582_ = l_Lean_Syntax_node2(v___y_559_, v___x_576_, v___x_581_, v___x_572_);
lean_inc(v___x_573_);
lean_inc(v___x_569_);
lean_inc(v___y_559_);
v___x_583_ = l_Lean_Syntax_node2(v___y_559_, v___x_569_, v___x_573_, v___x_582_);
v___x_584_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36));
lean_inc(v___y_559_);
v___x_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_585_, 0, v___y_559_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9);
v___x_587_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10));
lean_inc(v___y_554_);
lean_inc(v___y_553_);
v___x_588_ = l_Lean_addMacroScope(v___y_553_, v___x_587_, v___y_554_);
lean_inc(v___y_559_);
v___x_589_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_589_, 0, v___y_559_);
lean_ctor_set(v___x_589_, 1, v___x_586_);
lean_ctor_set(v___x_589_, 2, v___x_588_);
lean_ctor_set(v___x_589_, 3, v___x_580_);
lean_inc_ref(v___x_572_);
lean_inc(v___y_559_);
v___x_590_ = l_Lean_Syntax_node2(v___y_559_, v___x_576_, v___x_589_, v___x_572_);
lean_inc(v___x_573_);
lean_inc(v___y_559_);
v___x_591_ = l_Lean_Syntax_node2(v___y_559_, v___x_569_, v___x_573_, v___x_590_);
lean_inc(v___y_550_);
lean_inc(v___y_559_);
v___x_592_ = l_Lean_Syntax_node3(v___y_559_, v___y_550_, v___x_583_, v___x_585_, v___x_591_);
v___x_593_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60));
lean_inc(v___y_559_);
v___x_594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_594_, 0, v___y_559_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
lean_inc(v___y_559_);
v___x_595_ = l_Lean_Syntax_node3(v___y_559_, v___x_565_, v___x_567_, v___x_592_, v___x_594_);
lean_inc(v___y_550_);
lean_inc(v___y_559_);
v___x_596_ = l_Lean_Syntax_node1(v___y_559_, v___y_550_, v___x_595_);
v___x_597_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10));
lean_inc_ref(v___y_556_);
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_598_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___y_556_, v___x_597_);
lean_inc(v___y_559_);
v___x_599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_599_, 0, v___y_559_);
lean_ctor_set(v___x_599_, 1, v___x_597_);
lean_inc(v___y_559_);
v___x_600_ = l_Lean_Syntax_node1(v___y_559_, v___x_598_, v___x_599_);
lean_inc(v___y_550_);
lean_inc(v___y_559_);
v___x_601_ = l_Lean_Syntax_node1(v___y_559_, v___y_550_, v___x_600_);
lean_inc_ref_n(v___x_572_, 4);
lean_inc(v___x_601_);
lean_inc(v___y_551_);
lean_inc(v___y_559_);
v___x_602_ = l_Lean_Syntax_node7(v___y_559_, v___y_551_, v___x_562_, v___x_596_, v___x_601_, v___x_572_, v___x_572_, v___x_572_, v___x_572_);
v___x_603_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11));
lean_inc_ref(v___y_556_);
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_604_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___y_556_, v___x_603_);
v___x_605_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12));
lean_inc(v___y_559_);
v___x_606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_606_, 0, v___y_559_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13));
lean_inc_ref(v___y_556_);
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_608_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___y_556_, v___x_607_);
v___x_609_ = lean_mk_empty_array_with_capacity(v___x_524_);
v___x_610_ = lean_box(2);
lean_inc(v___y_550_);
v___x_611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___y_550_);
lean_ctor_set(v___x_611_, 2, v___x_609_);
v___x_612_ = lean_mk_empty_array_with_capacity(v___x_525_);
v___x_613_ = lean_array_push(v___x_612_, v___y_549_);
v___x_614_ = lean_array_push(v___x_613_, v___x_611_);
v___x_615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_615_, 0, v___x_610_);
lean_ctor_set(v___x_615_, 1, v___x_608_);
lean_ctor_set(v___x_615_, 2, v___x_614_);
v___x_616_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14));
lean_inc_ref(v___y_556_);
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_617_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___y_556_, v___x_616_);
lean_inc_ref_n(v___x_572_, 2);
lean_inc(v___y_559_);
v___x_618_ = l_Lean_Syntax_node2(v___y_559_, v___x_617_, v___x_572_, v___x_572_);
v___x_619_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31));
lean_inc_ref(v___y_556_);
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_620_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___y_556_, v___x_619_);
v___x_621_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2));
lean_inc(v___y_559_);
v___x_622_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_622_, 0, v___y_559_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62));
v___x_624_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63));
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_625_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___x_623_, v___x_624_);
lean_inc_ref_n(v___x_572_, 2);
lean_inc(v___y_559_);
v___x_626_ = l_Lean_Syntax_node2(v___y_559_, v___x_625_, v___x_572_, v___x_572_);
lean_inc_ref(v___x_572_);
lean_inc(v___x_626_);
lean_inc(v___y_548_);
lean_inc_ref(v___x_622_);
lean_inc(v___x_620_);
lean_inc(v___y_559_);
v___x_627_ = l_Lean_Syntax_node4(v___y_559_, v___x_620_, v___x_622_, v___y_548_, v___x_626_, v___x_572_);
lean_inc_ref(v___x_572_);
lean_inc(v___y_559_);
v___x_628_ = l_Lean_Syntax_node5(v___y_559_, v___x_604_, v___x_606_, v___x_615_, v___x_618_, v___x_627_, v___x_572_);
lean_inc(v___y_552_);
lean_inc(v___y_559_);
v___x_629_ = l_Lean_Syntax_node2(v___y_559_, v___y_552_, v___x_602_, v___x_628_);
v___x_630_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69));
lean_inc_ref(v___x_526_);
v___x_631_ = l_Lean_Name_mkStr2(v___x_526_, v___x_630_);
v___x_632_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0));
lean_inc(v___y_559_);
v___x_633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_633_, 0, v___y_559_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_559_);
v___x_635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_635_, 0, v___y_559_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
lean_inc(v___x_528_);
lean_inc_ref(v___x_622_);
lean_inc(v___y_548_);
lean_inc_ref(v___x_635_);
lean_inc_ref(v___x_572_);
lean_inc(v___y_559_);
v___x_636_ = l_Lean_Syntax_node8(v___y_559_, v___x_631_, v___x_572_, v___x_633_, v___y_555_, v___x_635_, v_fam_527_, v___y_548_, v___x_622_, v___x_528_);
lean_inc_ref_n(v___x_572_, 6);
lean_inc(v___y_559_);
v___x_637_ = l_Lean_Syntax_node7(v___y_559_, v___y_551_, v___x_572_, v___x_572_, v___x_601_, v___x_572_, v___x_572_, v___x_572_, v___x_572_);
v___x_638_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12));
lean_inc_ref(v___y_556_);
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_639_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___y_556_, v___x_638_);
lean_inc(v___y_559_);
v___x_640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_640_, 0, v___y_559_);
lean_ctor_set(v___x_640_, 1, v___x_638_);
v___x_641_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17));
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_642_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___y_556_, v___x_641_);
v___x_643_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19));
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_644_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___x_563_, v___x_643_);
v___x_645_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21));
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_646_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___x_563_, v___x_645_);
v___x_647_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15));
v___x_648_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16);
v___x_649_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17));
lean_inc(v___y_554_);
lean_inc(v___y_553_);
v___x_650_ = l_Lean_addMacroScope(v___y_553_, v___x_649_, v___y_554_);
lean_inc_ref(v___x_526_);
v___x_651_ = l_Lean_Name_mkStr2(v___x_526_, v___x_647_);
lean_inc(v___x_651_);
v___x_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_580_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___x_580_);
v___x_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_652_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
lean_inc(v___y_559_);
v___x_656_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_656_, 0, v___y_559_);
lean_ctor_set(v___x_656_, 1, v___x_648_);
lean_ctor_set(v___x_656_, 2, v___x_650_);
lean_ctor_set(v___x_656_, 3, v___x_655_);
lean_inc_ref(v___x_529_);
v___x_657_ = l_String_toRawSubstring_x27(v___x_529_);
v___x_658_ = l_Lean_Name_mkStr1(v___x_529_);
lean_inc(v___y_554_);
lean_inc(v___y_553_);
v___x_659_ = l_Lean_addMacroScope(v___y_553_, v___x_658_, v___y_554_);
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_530_);
lean_ctor_set(v___x_660_, 1, v___x_580_);
v___x_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_580_);
lean_inc(v___y_559_);
v___x_662_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_662_, 0, v___y_559_);
lean_ctor_set(v___x_662_, 1, v___x_657_);
lean_ctor_set(v___x_662_, 2, v___x_659_);
lean_ctor_set(v___x_662_, 3, v___x_661_);
v___x_663_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18));
lean_inc_ref(v___y_545_);
lean_inc_ref(v___y_544_);
v___x_664_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___x_563_, v___x_663_);
v___x_665_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19));
lean_inc_ref(v___y_544_);
v___x_666_ = l_Lean_Name_mkStr4(v___y_544_, v___y_545_, v___x_563_, v___x_665_);
v___x_667_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20));
lean_inc(v___y_559_);
v___x_668_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_668_, 0, v___y_559_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22));
v___x_670_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
v___x_671_ = lean_box(0);
lean_inc(v___y_554_);
lean_inc(v___y_553_);
v___x_672_ = l_Lean_addMacroScope(v___y_553_, v___x_671_, v___y_554_);
v___x_673_ = l_Lean_Name_mkStr1(v___x_526_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
v___x_675_ = l_Lean_Name_mkStr1(v___y_544_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
v___x_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___x_580_);
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_674_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
lean_inc(v___y_559_);
v___x_679_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_679_, 0, v___y_559_);
lean_ctor_set(v___x_679_, 1, v___x_670_);
lean_ctor_set(v___x_679_, 2, v___x_672_);
lean_ctor_set(v___x_679_, 3, v___x_678_);
lean_inc(v___y_559_);
v___x_680_ = l_Lean_Syntax_node1(v___y_559_, v___x_669_, v___x_679_);
lean_inc(v___y_559_);
v___x_681_ = l_Lean_Syntax_node2(v___y_559_, v___x_666_, v___x_668_, v___x_680_);
v___x_682_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26));
v___x_683_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27));
lean_inc(v___y_559_);
v___x_684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_684_, 0, v___y_559_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
lean_inc(v___y_559_);
v___x_685_ = l_Lean_Syntax_node3(v___y_559_, v___x_682_, v___y_558_, v___x_684_, v___y_547_);
v___x_686_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28));
lean_inc(v___y_559_);
v___x_687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_687_, 0, v___y_559_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
lean_inc_ref(v___x_687_);
lean_inc(v___x_681_);
lean_inc(v___x_664_);
lean_inc(v___y_559_);
v___x_688_ = l_Lean_Syntax_node3(v___y_559_, v___x_664_, v___x_681_, v___x_685_, v___x_687_);
lean_inc(v___x_528_);
lean_inc_ref(v___x_662_);
lean_inc(v___y_550_);
lean_inc(v___y_559_);
v___x_689_ = l_Lean_Syntax_node3(v___y_559_, v___y_550_, v___x_662_, v___x_688_, v___x_528_);
lean_inc_ref(v___x_656_);
lean_inc(v___x_646_);
lean_inc(v___y_559_);
v___x_690_ = l_Lean_Syntax_node2(v___y_559_, v___x_646_, v___x_656_, v___x_689_);
lean_inc(v___y_559_);
v___x_691_ = l_Lean_Syntax_node2(v___y_559_, v___x_644_, v___x_635_, v___x_690_);
lean_inc_ref(v___x_572_);
lean_inc(v___y_559_);
v___x_692_ = l_Lean_Syntax_node2(v___y_559_, v___x_642_, v___x_572_, v___x_691_);
v___x_693_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30);
v___x_694_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31));
v___x_695_ = l_Lean_addMacroScope(v___y_553_, v___x_694_, v___y_554_);
v___x_696_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__33));
lean_inc(v___y_559_);
v___x_697_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_697_, 0, v___y_559_);
lean_ctor_set(v___x_697_, 1, v___x_693_);
lean_ctor_set(v___x_697_, 2, v___x_695_);
lean_ctor_set(v___x_697_, 3, v___x_696_);
lean_inc(v___y_550_);
lean_inc(v___y_559_);
v___x_698_ = l_Lean_Syntax_node3(v___y_559_, v___y_550_, v___x_662_, v___y_548_, v___x_528_);
lean_inc(v___x_646_);
lean_inc(v___y_559_);
v___x_699_ = l_Lean_Syntax_node2(v___y_559_, v___x_646_, v___x_656_, v___x_698_);
lean_inc(v___y_559_);
v___x_700_ = l_Lean_Syntax_node3(v___y_559_, v___x_664_, v___x_681_, v___x_699_, v___x_687_);
lean_inc(v___y_550_);
lean_inc(v___y_559_);
v___x_701_ = l_Lean_Syntax_node1(v___y_559_, v___y_550_, v___x_700_);
lean_inc(v___y_559_);
v___x_702_ = l_Lean_Syntax_node2(v___y_559_, v___x_646_, v___x_697_, v___x_701_);
lean_inc_ref(v___x_572_);
lean_inc(v___y_559_);
v___x_703_ = l_Lean_Syntax_node4(v___y_559_, v___x_620_, v___x_622_, v___x_702_, v___x_626_, v___x_572_);
lean_inc_ref(v___x_572_);
lean_inc(v___y_559_);
v___x_704_ = l_Lean_Syntax_node6(v___y_559_, v___x_639_, v___x_573_, v___x_640_, v___x_572_, v___x_572_, v___x_692_, v___x_703_);
lean_inc(v___y_559_);
v___x_705_ = l_Lean_Syntax_node2(v___y_559_, v___y_552_, v___x_637_, v___x_704_);
v___x_706_ = l_Lean_Syntax_node3(v___y_559_, v___y_550_, v___x_629_, v___x_636_, v___x_705_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___y_546_);
return v___x_707_;
}
v___jp_708_:
{
lean_object* v_quotContext_716_; lean_object* v_currMacroScope_717_; lean_object* v_ref_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_quotContext_716_ = lean_ctor_get(v___y_714_, 1);
lean_inc(v_quotContext_716_);
v_currMacroScope_717_ = lean_ctor_get(v___y_714_, 2);
lean_inc(v_currMacroScope_717_);
v_ref_718_ = lean_ctor_get(v___y_714_, 5);
lean_inc(v_ref_718_);
lean_dec_ref(v___y_714_);
v___x_719_ = l_Lean_SourceInfo_fromRef(v_ref_718_, v___x_531_);
lean_dec(v_ref_718_);
v___x_720_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_721_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3));
v___x_722_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4));
v___x_723_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5));
v___x_724_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7));
v___x_725_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9));
v___x_726_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_532_) == 1)
{
lean_object* v_val_727_; lean_object* v___x_728_; 
v_val_727_ = lean_ctor_get(v___y_532_, 0);
lean_inc(v_val_727_);
lean_dec_ref(v___y_532_);
v___x_728_ = l_Array_mkArray1___redArg(v_val_727_);
v___y_544_ = v___x_721_;
v___y_545_ = v___x_722_;
v___y_546_ = v___y_715_;
v___y_547_ = v___y_710_;
v___y_548_ = v___y_709_;
v___y_549_ = v_id_713_;
v___y_550_ = v___x_720_;
v___y_551_ = v___x_725_;
v___y_552_ = v___x_724_;
v___y_553_ = v_quotContext_716_;
v___y_554_ = v_currMacroScope_717_;
v___y_555_ = v___y_711_;
v___y_556_ = v___x_723_;
v___y_557_ = v___x_726_;
v___y_558_ = v___y_712_;
v___y_559_ = v___x_719_;
v___y_560_ = v___x_728_;
goto v___jp_543_;
}
else
{
lean_object* v___x_729_; 
lean_dec(v___y_532_);
v___x_729_ = lean_mk_empty_array_with_capacity(v___x_524_);
v___y_544_ = v___x_721_;
v___y_545_ = v___x_722_;
v___y_546_ = v___y_715_;
v___y_547_ = v___y_710_;
v___y_548_ = v___y_709_;
v___y_549_ = v_id_713_;
v___y_550_ = v___x_720_;
v___y_551_ = v___x_725_;
v___y_552_ = v___x_724_;
v___y_553_ = v_quotContext_716_;
v___y_554_ = v_currMacroScope_717_;
v___y_555_ = v___y_711_;
v___y_556_ = v___x_723_;
v___y_557_ = v___x_726_;
v___y_558_ = v___y_712_;
v___y_559_ = v___x_719_;
v___y_560_ = v___x_729_;
goto v___jp_543_;
}
}
v___jp_730_:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__34));
lean_inc_ref(v___y_541_);
v___x_736_ = l_Lean_Macro_throwErrorAt___redArg(v_name_533_, v___x_735_, v___y_541_, v___y_542_);
lean_dec(v_name_533_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v_a_738_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
v_a_738_ = lean_ctor_get(v___x_736_, 1);
lean_inc(v_a_738_);
lean_dec_ref(v___x_736_);
v___y_709_ = v___y_732_;
v___y_710_ = v___y_731_;
v___y_711_ = v___y_733_;
v___y_712_ = v___y_734_;
v_id_713_ = v_a_737_;
v___y_714_ = v___y_541_;
v___y_715_ = v_a_738_;
goto v___jp_708_;
}
else
{
lean_dec(v___y_734_);
lean_dec(v___y_733_);
lean_dec(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_532_);
lean_dec(v___x_530_);
lean_dec_ref(v___x_529_);
lean_dec(v___x_528_);
lean_dec(v_fam_527_);
lean_dec_ref(v___x_526_);
return v___x_736_;
}
}
v___jp_740_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_inc(v___x_739_);
lean_inc(v_name_533_);
v___x_742_ = l_Lake_Name_quoteFrom(v_name_533_, v___x_739_, v___y_741_);
lean_inc(v___x_535_);
v___x_743_ = l_Lake_Name_quoteFrom(v_ns_534_, v___x_535_, v___x_536_);
lean_inc(v___x_739_);
v___x_744_ = l_Lean_Name_append(v___x_535_, v___x_739_);
lean_inc(v___x_744_);
v___x_745_ = l_Lean_mkIdentFrom(v_tk_537_, v___x_744_, v___x_536_);
v___x_746_ = l_Lake_Name_quoteFrom(v_tk_537_, v___x_744_, v___x_531_);
if (lean_obj_tag(v___y_538_) == 1)
{
lean_object* v_val_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec(v___x_739_);
lean_dec(v_name_533_);
v_val_747_ = lean_ctor_get(v___y_538_, 0);
v___x_748_ = l_Lean_Syntax_getArg(v_val_747_, v___x_524_);
v___x_749_ = l_Lean_Syntax_getId(v___x_748_);
v___x_750_ = l_Lean_Name_append(v___x_539_, v___x_749_);
v___x_751_ = l_Lean_mkIdentFrom(v___x_748_, v___x_750_, v___x_536_);
lean_dec(v___x_748_);
v___y_709_ = v___x_746_;
v___y_710_ = v___x_742_;
v___y_711_ = v___x_745_;
v___y_712_ = v___x_743_;
v_id_713_ = v___x_751_;
v___y_714_ = v___y_541_;
v___y_715_ = v___y_542_;
goto v___jp_708_;
}
else
{
if (lean_obj_tag(v___x_739_) == 1)
{
lean_object* v_pre_752_; 
v_pre_752_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_pre_752_);
if (lean_obj_tag(v_pre_752_) == 0)
{
lean_object* v_str_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_str_753_ = lean_ctor_get(v___x_739_, 1);
lean_inc_ref(v_str_753_);
lean_dec_ref(v___x_739_);
v___x_754_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__35));
v___x_755_ = lean_string_append(v_str_753_, v___x_754_);
v___x_756_ = l_Lean_Name_str___override(v___x_539_, v___x_755_);
v___x_757_ = l_Lean_mkIdentFrom(v_name_533_, v___x_756_, v___x_536_);
lean_dec(v_name_533_);
v___y_709_ = v___x_746_;
v___y_710_ = v___x_742_;
v___y_711_ = v___x_745_;
v___y_712_ = v___x_743_;
v_id_713_ = v___x_757_;
v___y_714_ = v___y_541_;
v___y_715_ = v___y_542_;
goto v___jp_708_;
}
else
{
lean_dec_ref(v___x_739_);
lean_dec(v_pre_752_);
lean_dec(v___x_539_);
v___y_731_ = v___x_742_;
v___y_732_ = v___x_746_;
v___y_733_ = v___x_745_;
v___y_734_ = v___x_743_;
goto v___jp_730_;
}
}
else
{
lean_dec(v___x_739_);
lean_dec(v___x_539_);
v___y_731_ = v___x_742_;
v___y_732_ = v___x_746_;
v___y_733_ = v___x_745_;
v___y_734_ = v___x_743_;
goto v___jp_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_758_ = _args[0];
lean_object* v___x_759_ = _args[1];
lean_object* v___x_760_ = _args[2];
lean_object* v_fam_761_ = _args[3];
lean_object* v___x_762_ = _args[4];
lean_object* v___x_763_ = _args[5];
lean_object* v___x_764_ = _args[6];
lean_object* v___x_765_ = _args[7];
lean_object* v___y_766_ = _args[8];
lean_object* v_name_767_ = _args[9];
lean_object* v_ns_768_ = _args[10];
lean_object* v___x_769_ = _args[11];
lean_object* v___x_770_ = _args[12];
lean_object* v_tk_771_ = _args[13];
lean_object* v___y_772_ = _args[14];
lean_object* v___x_773_ = _args[15];
lean_object* v_____r_774_ = _args[16];
lean_object* v___y_775_ = _args[17];
lean_object* v___y_776_ = _args[18];
_start:
{
uint8_t v___x_13207__boxed_777_; uint8_t v___x_13210__boxed_778_; lean_object* v_res_779_; 
v___x_13207__boxed_777_ = lean_unbox(v___x_765_);
v___x_13210__boxed_778_ = lean_unbox(v___x_770_);
v_res_779_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(v___x_758_, v___x_759_, v___x_760_, v_fam_761_, v___x_762_, v___x_763_, v___x_764_, v___x_13207__boxed_777_, v___y_766_, v_name_767_, v_ns_768_, v___x_769_, v___x_13210__boxed_778_, v_tk_771_, v___y_772_, v___x_773_, v_____r_774_, v___y_775_, v___y_776_);
lean_dec(v___y_772_);
lean_dec(v___x_759_);
lean_dec(v___x_758_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1(lean_object* v_x_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___y_791_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = ((lean_object*)(l_Lake_dataTypeDecl___closed__0));
v___x_811_ = ((lean_object*)(l_Lake_builtinFacetCommand___closed__1));
lean_inc(v_x_787_);
v___x_812_ = l_Lean_Syntax_isOfKind(v_x_787_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec_ref(v_a_788_);
lean_dec(v_x_787_);
v___x_813_ = lean_box(1);
v___x_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v_a_789_);
return v___x_814_;
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_tk_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_name_822_; lean_object* v___x_823_; lean_object* v_ns_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_892_; lean_object* v___x_903_; 
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = l_Lean_Syntax_getArg(v_x_787_, v___x_815_);
v___x_817_ = lean_unsigned_to_nat(1u);
v_tk_818_ = l_Lean_Syntax_getArg(v_x_787_, v___x_817_);
v___x_819_ = lean_unsigned_to_nat(2u);
v___x_820_ = l_Lean_Syntax_getArg(v_x_787_, v___x_819_);
v___x_821_ = lean_unsigned_to_nat(3u);
v_name_822_ = l_Lean_Syntax_getArg(v_x_787_, v___x_821_);
v___x_823_ = lean_unsigned_to_nat(5u);
v_ns_824_ = l_Lean_Syntax_getArg(v_x_787_, v___x_823_);
v___x_825_ = lean_unsigned_to_nat(7u);
v___x_826_ = l_Lean_Syntax_getArg(v_x_787_, v___x_825_);
lean_dec(v_x_787_);
v___x_903_ = l_Lean_Syntax_getOptional_x3f(v___x_820_);
lean_dec(v___x_820_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___x_904_; 
v___x_904_ = lean_box(0);
v___y_892_ = v___x_904_;
goto v___jp_891_;
}
else
{
lean_object* v_val_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_val_905_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_903_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_val_905_);
lean_dec(v___x_903_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_val_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
v___y_892_ = v___x_910_;
goto v___jp_891_;
}
}
}
v___jp_827_:
{
lean_object* v_methods_830_; lean_object* v_quotContext_831_; lean_object* v_currMacroScope_832_; lean_object* v_currRecDepth_833_; lean_object* v_maxRecDepth_834_; lean_object* v_ref_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_890_; 
v_methods_830_ = lean_ctor_get(v_a_788_, 0);
v_quotContext_831_ = lean_ctor_get(v_a_788_, 1);
v_currMacroScope_832_ = lean_ctor_get(v_a_788_, 2);
v_currRecDepth_833_ = lean_ctor_get(v_a_788_, 3);
v_maxRecDepth_834_ = lean_ctor_get(v_a_788_, 4);
v_ref_835_ = lean_ctor_get(v_a_788_, 5);
v_isSharedCheck_890_ = !lean_is_exclusive(v_a_788_);
if (v_isSharedCheck_890_ == 0)
{
v___x_837_ = v_a_788_;
v_isShared_838_ = v_isSharedCheck_890_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_ref_835_);
lean_inc(v_maxRecDepth_834_);
lean_inc(v_currRecDepth_833_);
lean_inc(v_currMacroScope_832_);
lean_inc(v_quotContext_831_);
lean_inc(v_methods_830_);
lean_dec(v_a_788_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_890_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v_ref_840_; lean_object* v___x_842_; 
v___x_839_ = l_Lean_TSyntax_getId(v_ns_824_);
v_ref_840_ = l_Lean_replaceRef(v_tk_818_, v_ref_835_);
lean_dec(v_ref_835_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 5, v_ref_840_);
v___x_842_ = v___x_837_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_methods_830_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_quotContext_831_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_currMacroScope_832_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_currRecDepth_833_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_maxRecDepth_834_);
lean_ctor_set(v_reuseFailAlloc_889_, 5, v_ref_840_);
v___x_842_ = v_reuseFailAlloc_889_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; 
lean_inc_ref(v___x_842_);
lean_inc(v___x_839_);
v___x_843_ = l_Lean_Macro_resolveNamespace(v___x_839_, v___x_842_, v_a_789_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
if (lean_obj_tag(v_a_844_) == 1)
{
lean_object* v_a_845_; lean_object* v_head_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; lean_object* v_fam_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_a_845_ = lean_ctor_get(v___x_843_, 1);
lean_inc(v_a_845_);
lean_dec_ref(v___x_843_);
v_head_846_ = lean_ctor_get(v_a_844_, 0);
lean_inc(v_head_846_);
lean_dec_ref(v_a_844_);
v___x_847_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0));
v___x_848_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1));
v___x_849_ = 0;
v_fam_850_ = l_Lean_mkCIdentFrom(v_tk_818_, v___x_848_, v___x_849_);
v___x_851_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace(v_head_846_);
lean_dec(v_head_846_);
v___x_852_ = l_Lean_Name_isAnonymous(v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_box(0);
v___x_854_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(v___x_815_, v___x_819_, v___x_810_, v_fam_850_, v___x_826_, v___x_847_, v___x_848_, v___x_849_, v___y_829_, v_name_822_, v_ns_824_, v___x_851_, v___x_812_, v_tk_818_, v___y_828_, v___x_839_, v___x_853_, v___x_842_, v_a_845_);
lean_dec(v___y_828_);
v___y_791_ = v___x_854_;
goto v___jp_790_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_855_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2));
lean_inc(v___x_839_);
v___x_856_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_839_, v___x_852_);
v___x_857_ = lean_string_append(v___x_855_, v___x_856_);
lean_dec_ref(v___x_856_);
v___x_858_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3));
v___x_859_ = lean_string_append(v___x_857_, v___x_858_);
lean_inc_ref(v___x_842_);
v___x_860_ = l_Lean_Macro_throwErrorAt___redArg(v_ns_824_, v___x_859_, v___x_842_, v_a_845_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
v_a_862_ = lean_ctor_get(v___x_860_, 1);
lean_inc(v_a_862_);
lean_dec_ref(v___x_860_);
v___x_863_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(v___x_815_, v___x_819_, v___x_810_, v_fam_850_, v___x_826_, v___x_847_, v___x_848_, v___x_849_, v___y_829_, v_name_822_, v_ns_824_, v___x_851_, v___x_812_, v_tk_818_, v___y_828_, v___x_839_, v_a_861_, v___x_842_, v_a_862_);
lean_dec(v___y_828_);
v___y_791_ = v___x_863_;
goto v___jp_790_;
}
else
{
lean_object* v_a_864_; lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v___x_851_);
lean_dec(v_fam_850_);
lean_dec_ref(v___x_842_);
lean_dec(v___x_839_);
lean_dec(v___y_829_);
lean_dec(v___y_828_);
lean_dec(v___x_826_);
lean_dec(v_ns_824_);
lean_dec(v_name_822_);
lean_dec(v_tk_818_);
v_a_864_ = lean_ctor_get(v___x_860_, 0);
v_a_865_ = lean_ctor_get(v___x_860_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_860_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_inc(v_a_864_);
lean_dec(v___x_860_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_864_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec(v_a_844_);
lean_dec(v___y_829_);
lean_dec(v___y_828_);
lean_dec(v___x_826_);
lean_dec(v_name_822_);
lean_dec(v_tk_818_);
v_a_873_ = lean_ctor_get(v___x_843_, 1);
lean_inc(v_a_873_);
lean_dec_ref(v___x_843_);
v___x_874_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4));
v___x_875_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_839_, v___x_812_);
v___x_876_ = lean_string_append(v___x_874_, v___x_875_);
lean_dec_ref(v___x_875_);
v___x_877_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3));
v___x_878_ = lean_string_append(v___x_876_, v___x_877_);
v___x_879_ = l_Lean_Macro_throwErrorAt___redArg(v_ns_824_, v___x_878_, v___x_842_, v_a_873_);
lean_dec(v_ns_824_);
v___y_791_ = v___x_879_;
goto v___jp_790_;
}
}
else
{
lean_object* v_a_880_; lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v___x_842_);
lean_dec(v___x_839_);
lean_dec(v___y_829_);
lean_dec(v___y_828_);
lean_dec(v___x_826_);
lean_dec(v_ns_824_);
lean_dec(v_name_822_);
lean_dec(v_tk_818_);
v_a_880_ = lean_ctor_get(v___x_843_, 0);
v_a_881_ = lean_ctor_get(v___x_843_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_843_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_inc(v_a_880_);
lean_dec(v___x_843_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_880_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
v___jp_891_:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Syntax_getOptional_x3f(v___x_816_);
lean_dec(v___x_816_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v___x_894_; 
v___x_894_ = lean_box(0);
v___y_828_ = v___y_892_;
v___y_829_ = v___x_894_;
goto v___jp_827_;
}
else
{
lean_object* v_val_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_val_895_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_893_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_val_895_);
lean_dec(v___x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_val_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
v___y_828_ = v___y_892_;
v___y_829_ = v___x_900_;
goto v___jp_827_;
}
}
}
}
}
v___jp_790_:
{
if (lean_obj_tag(v___y_791_) == 0)
{
lean_object* v_a_792_; lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
v_a_792_ = lean_ctor_get(v___y_791_, 0);
v_a_793_ = lean_ctor_get(v___y_791_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v___y_791_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___y_791_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_inc(v_a_792_);
lean_dec(v___y_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_792_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
else
{
lean_object* v_a_801_; lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
v_a_801_ = lean_ctor_get(v___y_791_, 0);
v_a_802_ = lean_ctor_get(v___y_791_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v___y_791_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___y_791_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_inc(v_a_801_);
lean_dec(v___y_791_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_801_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1(lean_object* v_x_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lake_facetDataDecl___closed__1));
lean_inc(v_x_989_);
v___x_993_ = l_Lean_Syntax_isOfKind(v_x_989_, v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec_ref(v_a_990_);
lean_dec(v_x_989_);
v___x_994_ = lean_box(1);
v___x_995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v_a_991_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v_tk_999_; lean_object* v___x_1000_; lean_object* v_kind_1001_; lean_object* v___x_1002_; lean_object* v_name_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1101_; lean_object* v___x_1124_; 
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = l_Lean_Syntax_getArg(v_x_989_, v___x_996_);
v___x_998_ = lean_unsigned_to_nat(1u);
v_tk_999_ = l_Lean_Syntax_getArg(v_x_989_, v___x_998_);
v___x_1000_ = lean_unsigned_to_nat(2u);
v_kind_1001_ = l_Lean_Syntax_getArg(v_x_989_, v___x_1000_);
v___x_1002_ = lean_unsigned_to_nat(3u);
v_name_1003_ = l_Lean_Syntax_getArg(v_x_989_, v___x_1002_);
v___x_1004_ = lean_unsigned_to_nat(5u);
v___x_1005_ = l_Lean_Syntax_getArg(v_x_989_, v___x_1004_);
lean_dec(v_x_989_);
v___x_1124_ = l_Lean_Syntax_getOptional_x3f(v___x_997_);
lean_dec(v___x_997_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_box(0);
v___y_1101_ = v___x_1125_;
goto v___jp_1100_;
}
else
{
lean_object* v_val_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_val_1126_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1124_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_val_1126_);
lean_dec(v___x_1124_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_val_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
v___y_1101_ = v___x_1131_;
goto v___jp_1100_;
}
}
}
v___jp_1006_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_inc_ref(v___y_1018_);
v___x_1021_ = l_Array_append___redArg(v___y_1018_, v___y_1020_);
lean_dec_ref(v___y_1020_);
lean_inc(v___y_1015_);
lean_inc(v___y_1011_);
v___x_1022_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1022_, 0, v___y_1011_);
lean_ctor_set(v___x_1022_, 1, v___y_1015_);
lean_ctor_set(v___x_1022_, 2, v___x_1021_);
v___x_1023_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0));
lean_inc(v___y_1011_);
v___x_1024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___y_1011_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_1011_);
v___x_1026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___y_1011_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2));
lean_inc(v___y_1011_);
v___x_1028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___y_1011_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
lean_inc(v___x_1005_);
lean_inc_ref(v___x_1028_);
lean_inc(v___y_1010_);
lean_inc_ref(v___x_1026_);
lean_inc(v___y_1011_);
v___x_1029_ = l_Lean_Syntax_node8(v___y_1011_, v___y_1007_, v___x_1022_, v___x_1024_, v___y_1012_, v___x_1026_, v___y_1019_, v___y_1010_, v___x_1028_, v___x_1005_);
v___x_1030_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7));
v___x_1031_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9));
lean_inc(v___y_1015_);
lean_inc(v___y_1011_);
v___x_1032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1032_, 0, v___y_1011_);
lean_ctor_set(v___x_1032_, 1, v___y_1015_);
lean_ctor_set(v___x_1032_, 2, v___y_1018_);
v___x_1033_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10));
v___x_1034_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11));
lean_inc(v___y_1011_);
v___x_1035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___y_1011_);
lean_ctor_set(v___x_1035_, 1, v___x_1033_);
lean_inc(v___y_1011_);
v___x_1036_ = l_Lean_Syntax_node1(v___y_1011_, v___x_1034_, v___x_1035_);
lean_inc(v___y_1015_);
lean_inc(v___y_1011_);
v___x_1037_ = l_Lean_Syntax_node1(v___y_1011_, v___y_1015_, v___x_1036_);
lean_inc_ref_n(v___x_1032_, 6);
lean_inc(v___y_1011_);
v___x_1038_ = l_Lean_Syntax_node7(v___y_1011_, v___x_1031_, v___x_1032_, v___x_1032_, v___x_1037_, v___x_1032_, v___x_1032_, v___x_1032_, v___x_1032_);
v___x_1039_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12));
v___x_1040_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13));
v___x_1041_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16));
lean_inc_ref(v___x_1032_);
lean_inc(v___y_1011_);
v___x_1042_ = l_Lean_Syntax_node1(v___y_1011_, v___x_1041_, v___x_1032_);
lean_inc(v___y_1011_);
v___x_1043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___y_1011_);
lean_ctor_set(v___x_1043_, 1, v___x_1039_);
v___x_1044_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18));
v___x_1045_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20));
v___x_1046_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22));
v___x_1047_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16);
v___x_1048_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17));
lean_inc(v___y_1017_);
lean_inc(v___y_1009_);
v___x_1049_ = l_Lean_addMacroScope(v___y_1009_, v___x_1048_, v___y_1017_);
v___x_1050_ = lean_box(0);
v___x_1051_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4));
lean_inc(v___y_1011_);
v___x_1052_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1052_, 0, v___y_1011_);
lean_ctor_set(v___x_1052_, 1, v___x_1047_);
lean_ctor_set(v___x_1052_, 2, v___x_1049_);
lean_ctor_set(v___x_1052_, 3, v___x_1051_);
lean_inc_ref(v___y_1008_);
v___x_1053_ = l_String_toRawSubstring_x27(v___y_1008_);
v___x_1054_ = l_Lean_Name_mkStr1(v___y_1008_);
lean_inc(v___y_1017_);
lean_inc(v___y_1009_);
v___x_1055_ = l_Lean_addMacroScope(v___y_1009_, v___x_1054_, v___y_1017_);
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___y_1016_);
lean_ctor_set(v___x_1056_, 1, v___x_1050_);
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1050_);
lean_inc(v___y_1011_);
v___x_1058_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1058_, 0, v___y_1011_);
lean_ctor_set(v___x_1058_, 1, v___x_1053_);
lean_ctor_set(v___x_1058_, 2, v___x_1055_);
lean_ctor_set(v___x_1058_, 3, v___x_1057_);
v___x_1059_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5));
v___x_1060_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6));
v___x_1061_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20));
lean_inc(v___y_1011_);
v___x_1062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___y_1011_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22));
v___x_1064_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
v___x_1065_ = lean_box(0);
lean_inc(v___y_1017_);
lean_inc(v___y_1009_);
v___x_1066_ = l_Lean_addMacroScope(v___y_1009_, v___x_1065_, v___y_1017_);
v___x_1067_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12));
lean_inc(v___y_1011_);
v___x_1068_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1068_, 0, v___y_1011_);
lean_ctor_set(v___x_1068_, 1, v___x_1064_);
lean_ctor_set(v___x_1068_, 2, v___x_1066_);
lean_ctor_set(v___x_1068_, 3, v___x_1067_);
lean_inc(v___y_1011_);
v___x_1069_ = l_Lean_Syntax_node1(v___y_1011_, v___x_1063_, v___x_1068_);
lean_inc(v___y_1011_);
v___x_1070_ = l_Lean_Syntax_node2(v___y_1011_, v___x_1060_, v___x_1062_, v___x_1069_);
v___x_1071_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26));
v___x_1072_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27));
lean_inc(v___y_1011_);
v___x_1073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___y_1011_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
lean_inc(v___y_1011_);
v___x_1074_ = l_Lean_Syntax_node3(v___y_1011_, v___x_1071_, v___y_1013_, v___x_1073_, v___y_1014_);
v___x_1075_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28));
lean_inc(v___y_1011_);
v___x_1076_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___y_1011_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
lean_inc_ref(v___x_1076_);
lean_inc(v___x_1070_);
lean_inc(v___y_1011_);
v___x_1077_ = l_Lean_Syntax_node3(v___y_1011_, v___x_1059_, v___x_1070_, v___x_1074_, v___x_1076_);
lean_inc(v___x_1005_);
lean_inc_ref(v___x_1058_);
lean_inc(v___y_1015_);
lean_inc(v___y_1011_);
v___x_1078_ = l_Lean_Syntax_node3(v___y_1011_, v___y_1015_, v___x_1058_, v___x_1077_, v___x_1005_);
lean_inc_ref(v___x_1052_);
lean_inc(v___y_1011_);
v___x_1079_ = l_Lean_Syntax_node2(v___y_1011_, v___x_1046_, v___x_1052_, v___x_1078_);
lean_inc(v___y_1011_);
v___x_1080_ = l_Lean_Syntax_node2(v___y_1011_, v___x_1045_, v___x_1026_, v___x_1079_);
lean_inc_ref(v___x_1032_);
lean_inc(v___y_1011_);
v___x_1081_ = l_Lean_Syntax_node2(v___y_1011_, v___x_1044_, v___x_1032_, v___x_1080_);
v___x_1082_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32));
v___x_1083_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30);
v___x_1084_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31));
v___x_1085_ = l_Lean_addMacroScope(v___y_1009_, v___x_1084_, v___y_1017_);
v___x_1086_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__14));
lean_inc(v___y_1011_);
v___x_1087_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1087_, 0, v___y_1011_);
lean_ctor_set(v___x_1087_, 1, v___x_1083_);
lean_ctor_set(v___x_1087_, 2, v___x_1085_);
lean_ctor_set(v___x_1087_, 3, v___x_1086_);
lean_inc(v___y_1015_);
lean_inc(v___y_1011_);
v___x_1088_ = l_Lean_Syntax_node3(v___y_1011_, v___y_1015_, v___x_1058_, v___y_1010_, v___x_1005_);
lean_inc(v___y_1011_);
v___x_1089_ = l_Lean_Syntax_node2(v___y_1011_, v___x_1046_, v___x_1052_, v___x_1088_);
lean_inc(v___y_1011_);
v___x_1090_ = l_Lean_Syntax_node3(v___y_1011_, v___x_1059_, v___x_1070_, v___x_1089_, v___x_1076_);
lean_inc(v___y_1015_);
lean_inc(v___y_1011_);
v___x_1091_ = l_Lean_Syntax_node1(v___y_1011_, v___y_1015_, v___x_1090_);
lean_inc(v___y_1011_);
v___x_1092_ = l_Lean_Syntax_node2(v___y_1011_, v___x_1046_, v___x_1087_, v___x_1091_);
v___x_1093_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64));
lean_inc_ref_n(v___x_1032_, 2);
lean_inc(v___y_1011_);
v___x_1094_ = l_Lean_Syntax_node2(v___y_1011_, v___x_1093_, v___x_1032_, v___x_1032_);
lean_inc_ref(v___x_1032_);
lean_inc(v___y_1011_);
v___x_1095_ = l_Lean_Syntax_node4(v___y_1011_, v___x_1082_, v___x_1028_, v___x_1092_, v___x_1094_, v___x_1032_);
lean_inc_ref(v___x_1032_);
lean_inc(v___y_1011_);
v___x_1096_ = l_Lean_Syntax_node6(v___y_1011_, v___x_1040_, v___x_1042_, v___x_1043_, v___x_1032_, v___x_1032_, v___x_1081_, v___x_1095_);
lean_inc(v___y_1011_);
v___x_1097_ = l_Lean_Syntax_node2(v___y_1011_, v___x_1030_, v___x_1038_, v___x_1096_);
v___x_1098_ = l_Lean_Syntax_node2(v___y_1011_, v___y_1015_, v___x_1029_, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_a_991_);
return v___x_1099_;
}
v___jp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; lean_object* v_fam_1105_; lean_object* v___x_1106_; lean_object* v_kindLit_1107_; lean_object* v___x_1108_; lean_object* v_nameLit_1109_; lean_object* v_quotContext_1110_; lean_object* v_currMacroScope_1111_; lean_object* v_ref_1112_; lean_object* v_facet_1113_; lean_object* v_facetLit_1114_; lean_object* v_id_1115_; lean_object* v_ref_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1102_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0));
v___x_1103_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1));
v___x_1104_ = 0;
v_fam_1105_ = l_Lean_mkCIdentFrom(v_tk_999_, v___x_1103_, v___x_1104_);
v___x_1106_ = l_Lean_TSyntax_getId(v_kind_1001_);
lean_inc(v___x_1106_);
v_kindLit_1107_ = l_Lake_Name_quoteFrom(v_kind_1001_, v___x_1106_, v___x_1104_);
v___x_1108_ = l_Lean_TSyntax_getId(v_name_1003_);
lean_inc(v___x_1108_);
v_nameLit_1109_ = l_Lake_Name_quoteFrom(v_name_1003_, v___x_1108_, v___x_1104_);
v_quotContext_1110_ = lean_ctor_get(v_a_990_, 1);
lean_inc(v_quotContext_1110_);
v_currMacroScope_1111_ = lean_ctor_get(v_a_990_, 2);
lean_inc(v_currMacroScope_1111_);
v_ref_1112_ = lean_ctor_get(v_a_990_, 5);
lean_inc(v_ref_1112_);
lean_dec_ref(v_a_990_);
v_facet_1113_ = l_Lean_Name_append(v___x_1106_, v___x_1108_);
lean_inc(v_facet_1113_);
lean_inc(v_tk_999_);
v_facetLit_1114_ = l_Lake_Name_quoteFrom(v_tk_999_, v_facet_1113_, v___x_1104_);
v_id_1115_ = l_Lean_mkIdentFrom(v_tk_999_, v_facet_1113_, v___x_993_);
v_ref_1116_ = l_Lean_replaceRef(v_tk_999_, v_ref_1112_);
lean_dec(v_ref_1112_);
lean_dec(v_tk_999_);
v___x_1117_ = l_Lean_SourceInfo_fromRef(v_ref_1116_, v___x_1104_);
lean_dec(v_ref_1116_);
v___x_1118_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_1119_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70));
v___x_1120_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_1101_) == 1)
{
lean_object* v_val_1121_; lean_object* v___x_1122_; 
v_val_1121_ = lean_ctor_get(v___y_1101_, 0);
lean_inc(v_val_1121_);
lean_dec_ref(v___y_1101_);
v___x_1122_ = l_Array_mkArray1___redArg(v_val_1121_);
v___y_1007_ = v___x_1119_;
v___y_1008_ = v___x_1102_;
v___y_1009_ = v_quotContext_1110_;
v___y_1010_ = v_facetLit_1114_;
v___y_1011_ = v___x_1117_;
v___y_1012_ = v_id_1115_;
v___y_1013_ = v_kindLit_1107_;
v___y_1014_ = v_nameLit_1109_;
v___y_1015_ = v___x_1118_;
v___y_1016_ = v___x_1103_;
v___y_1017_ = v_currMacroScope_1111_;
v___y_1018_ = v___x_1120_;
v___y_1019_ = v_fam_1105_;
v___y_1020_ = v___x_1122_;
goto v___jp_1006_;
}
else
{
lean_object* v___x_1123_; 
lean_dec(v___y_1101_);
v___x_1123_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72));
v___y_1007_ = v___x_1119_;
v___y_1008_ = v___x_1102_;
v___y_1009_ = v_quotContext_1110_;
v___y_1010_ = v_facetLit_1114_;
v___y_1011_ = v___x_1117_;
v___y_1012_ = v_id_1115_;
v___y_1013_ = v_kindLit_1107_;
v___y_1014_ = v_nameLit_1109_;
v___y_1015_ = v___x_1118_;
v___y_1016_ = v___x_1103_;
v___y_1017_ = v_currMacroScope_1111_;
v___y_1018_ = v___x_1120_;
v___y_1019_ = v_fam_1105_;
v___y_1020_ = v___x_1123_;
goto v___jp_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1(lean_object* v_x_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lake_packageDataDecl___closed__1));
lean_inc(v_x_1163_);
v___x_1167_ = l_Lean_Syntax_isOfKind(v_x_1163_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec(v_x_1163_);
v___x_1168_ = lean_box(1);
v___x_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v_a_1165_);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v_tk_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; uint8_t v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1197_; lean_object* v___x_1207_; 
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = l_Lean_Syntax_getArg(v_x_1163_, v___x_1170_);
v___x_1172_ = lean_unsigned_to_nat(1u);
v_tk_1173_ = l_Lean_Syntax_getArg(v_x_1163_, v___x_1172_);
v___x_1174_ = lean_unsigned_to_nat(2u);
v___x_1175_ = l_Lean_Syntax_getArg(v_x_1163_, v___x_1174_);
v___x_1176_ = lean_unsigned_to_nat(4u);
v___x_1177_ = l_Lean_Syntax_getArg(v_x_1163_, v___x_1176_);
lean_dec(v_x_1163_);
v___x_1207_ = l_Lean_Syntax_getOptional_x3f(v___x_1171_);
lean_dec(v___x_1171_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_box(0);
v___y_1197_ = v___x_1208_;
goto v___jp_1196_;
}
else
{
lean_object* v_val_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_val_1209_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1207_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_val_1209_);
lean_dec(v___x_1207_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_val_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
v___y_1197_ = v___x_1214_;
goto v___jp_1196_;
}
}
}
v___jp_1178_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1185_ = l_Array_append___redArg(v___y_1182_, v___y_1184_);
lean_dec_ref(v___y_1184_);
lean_inc(v___y_1180_);
v___x_1186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1186_, 0, v___y_1180_);
lean_ctor_set(v___x_1186_, 1, v___y_1179_);
lean_ctor_set(v___x_1186_, 2, v___x_1185_);
v___x_1187_ = l_Lean_SourceInfo_fromRef(v_tk_1173_, v___x_1167_);
v___x_1188_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0));
v___x_1189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_Lake_Package_keyword;
v___x_1191_ = l_Lean_mkIdentFrom(v_tk_1173_, v___x_1190_, v___y_1183_);
lean_dec(v_tk_1173_);
v___x_1192_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_1180_);
v___x_1193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___y_1180_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = l_Lean_Syntax_node6(v___y_1180_, v___y_1181_, v___x_1186_, v___x_1189_, v___x_1191_, v___x_1175_, v___x_1193_, v___x_1177_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v_a_1165_);
return v___x_1195_;
}
v___jp_1196_:
{
lean_object* v_ref_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_ref_1198_ = lean_ctor_get(v_a_1164_, 5);
v___x_1199_ = 0;
v___x_1200_ = l_Lean_SourceInfo_fromRef(v_ref_1198_, v___x_1199_);
v___x_1201_ = ((lean_object*)(l_Lake_facetDataDecl___closed__1));
v___x_1202_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_1203_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_1197_) == 1)
{
lean_object* v_val_1204_; lean_object* v___x_1205_; 
v_val_1204_ = lean_ctor_get(v___y_1197_, 0);
lean_inc(v_val_1204_);
lean_dec_ref(v___y_1197_);
v___x_1205_ = l_Array_mkArray1___redArg(v_val_1204_);
v___y_1179_ = v___x_1202_;
v___y_1180_ = v___x_1200_;
v___y_1181_ = v___x_1201_;
v___y_1182_ = v___x_1203_;
v___y_1183_ = v___x_1199_;
v___y_1184_ = v___x_1205_;
goto v___jp_1178_;
}
else
{
lean_object* v___x_1206_; 
lean_dec(v___y_1197_);
v___x_1206_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72));
v___y_1179_ = v___x_1202_;
v___y_1180_ = v___x_1200_;
v___y_1181_ = v___x_1201_;
v___y_1182_ = v___x_1203_;
v___y_1183_ = v___x_1199_;
v___y_1184_ = v___x_1206_;
goto v___jp_1178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___boxed(lean_object* v_x_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1(v_x_1217_, v_a_1218_, v_a_1219_);
lean_dec_ref(v_a_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1(lean_object* v_x_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lake_moduleDataDecl___closed__1));
lean_inc(v_x_1249_);
v___x_1253_ = l_Lean_Syntax_isOfKind(v_x_1249_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec(v_x_1249_);
v___x_1254_ = lean_box(1);
v___x_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v_a_1251_);
return v___x_1255_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v_tk_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___y_1265_; lean_object* v___y_1266_; uint8_t v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1283_; lean_object* v___x_1293_; 
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = l_Lean_Syntax_getArg(v_x_1249_, v___x_1256_);
v___x_1258_ = lean_unsigned_to_nat(1u);
v_tk_1259_ = l_Lean_Syntax_getArg(v_x_1249_, v___x_1258_);
v___x_1260_ = lean_unsigned_to_nat(2u);
v___x_1261_ = l_Lean_Syntax_getArg(v_x_1249_, v___x_1260_);
v___x_1262_ = lean_unsigned_to_nat(4u);
v___x_1263_ = l_Lean_Syntax_getArg(v_x_1249_, v___x_1262_);
lean_dec(v_x_1249_);
v___x_1293_ = l_Lean_Syntax_getOptional_x3f(v___x_1257_);
lean_dec(v___x_1257_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_box(0);
v___y_1283_ = v___x_1294_;
goto v___jp_1282_;
}
else
{
lean_object* v_val_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_val_1295_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1293_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_val_1295_);
lean_dec(v___x_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
v___y_1283_ = v___x_1300_;
goto v___jp_1282_;
}
}
}
v___jp_1264_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1271_ = l_Array_append___redArg(v___y_1269_, v___y_1270_);
lean_dec_ref(v___y_1270_);
lean_inc(v___y_1266_);
v___x_1272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1272_, 0, v___y_1266_);
lean_ctor_set(v___x_1272_, 1, v___y_1268_);
lean_ctor_set(v___x_1272_, 2, v___x_1271_);
v___x_1273_ = l_Lean_SourceInfo_fromRef(v_tk_1259_, v___x_1253_);
v___x_1274_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0));
v___x_1275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Lake_Module_keyword;
v___x_1277_ = l_Lean_mkIdentFrom(v_tk_1259_, v___x_1276_, v___y_1267_);
lean_dec(v_tk_1259_);
v___x_1278_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_1266_);
v___x_1279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___y_1266_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Lean_Syntax_node6(v___y_1266_, v___y_1265_, v___x_1272_, v___x_1275_, v___x_1277_, v___x_1261_, v___x_1279_, v___x_1263_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v_a_1251_);
return v___x_1281_;
}
v___jp_1282_:
{
lean_object* v_ref_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_ref_1284_ = lean_ctor_get(v_a_1250_, 5);
v___x_1285_ = 0;
v___x_1286_ = l_Lean_SourceInfo_fromRef(v_ref_1284_, v___x_1285_);
v___x_1287_ = ((lean_object*)(l_Lake_facetDataDecl___closed__1));
v___x_1288_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_1289_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_1283_) == 1)
{
lean_object* v_val_1290_; lean_object* v___x_1291_; 
v_val_1290_ = lean_ctor_get(v___y_1283_, 0);
lean_inc(v_val_1290_);
lean_dec_ref(v___y_1283_);
v___x_1291_ = l_Array_mkArray1___redArg(v_val_1290_);
v___y_1265_ = v___x_1287_;
v___y_1266_ = v___x_1286_;
v___y_1267_ = v___x_1285_;
v___y_1268_ = v___x_1288_;
v___y_1269_ = v___x_1289_;
v___y_1270_ = v___x_1291_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1292_; 
lean_dec(v___y_1283_);
v___x_1292_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72));
v___y_1265_ = v___x_1287_;
v___y_1266_ = v___x_1286_;
v___y_1267_ = v___x_1285_;
v___y_1268_ = v___x_1288_;
v___y_1269_ = v___x_1289_;
v___y_1270_ = v___x_1292_;
goto v___jp_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1___boxed(lean_object* v_x_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1(v_x_1303_, v_a_1304_, v_a_1305_);
lean_dec_ref(v_a_1304_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1(lean_object* v_x_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = ((lean_object*)(l_Lake_libraryDataDecl___closed__1));
lean_inc(v_x_1338_);
v___x_1342_ = l_Lean_Syntax_isOfKind(v_x_1338_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec(v_x_1338_);
v___x_1343_ = lean_box(1);
v___x_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set(v___x_1344_, 1, v_a_1340_);
return v___x_1344_;
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v_tk_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___y_1354_; uint8_t v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1372_; lean_object* v___x_1382_; 
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = l_Lean_Syntax_getArg(v_x_1338_, v___x_1345_);
v___x_1347_ = lean_unsigned_to_nat(1u);
v_tk_1348_ = l_Lean_Syntax_getArg(v_x_1338_, v___x_1347_);
v___x_1349_ = lean_unsigned_to_nat(2u);
v___x_1350_ = l_Lean_Syntax_getArg(v_x_1338_, v___x_1349_);
v___x_1351_ = lean_unsigned_to_nat(4u);
v___x_1352_ = l_Lean_Syntax_getArg(v_x_1338_, v___x_1351_);
lean_dec(v_x_1338_);
v___x_1382_ = l_Lean_Syntax_getOptional_x3f(v___x_1346_);
lean_dec(v___x_1346_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_box(0);
v___y_1372_ = v___x_1383_;
goto v___jp_1371_;
}
else
{
lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_val_1384_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1382_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_dec(v___x_1382_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_val_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
v___y_1372_ = v___x_1389_;
goto v___jp_1371_;
}
}
}
v___jp_1353_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1360_ = l_Array_append___redArg(v___y_1357_, v___y_1359_);
lean_dec_ref(v___y_1359_);
lean_inc(v___y_1354_);
v___x_1361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1361_, 0, v___y_1354_);
lean_ctor_set(v___x_1361_, 1, v___y_1358_);
lean_ctor_set(v___x_1361_, 2, v___x_1360_);
v___x_1362_ = l_Lean_SourceInfo_fromRef(v_tk_1348_, v___x_1342_);
v___x_1363_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0));
v___x_1364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1));
v___x_1366_ = l_Lean_mkIdentFrom(v_tk_1348_, v___x_1365_, v___y_1355_);
lean_dec(v_tk_1348_);
v___x_1367_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_1354_);
v___x_1368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___y_1354_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = l_Lean_Syntax_node6(v___y_1354_, v___y_1356_, v___x_1361_, v___x_1364_, v___x_1366_, v___x_1350_, v___x_1368_, v___x_1352_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v_a_1340_);
return v___x_1370_;
}
v___jp_1371_:
{
lean_object* v_ref_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_ref_1373_ = lean_ctor_get(v_a_1339_, 5);
v___x_1374_ = 0;
v___x_1375_ = l_Lean_SourceInfo_fromRef(v_ref_1373_, v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Lake_facetDataDecl___closed__1));
v___x_1377_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_1378_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_1372_) == 1)
{
lean_object* v_val_1379_; lean_object* v___x_1380_; 
v_val_1379_ = lean_ctor_get(v___y_1372_, 0);
lean_inc(v_val_1379_);
lean_dec_ref(v___y_1372_);
v___x_1380_ = l_Array_mkArray1___redArg(v_val_1379_);
v___y_1354_ = v___x_1375_;
v___y_1355_ = v___x_1374_;
v___y_1356_ = v___x_1376_;
v___y_1357_ = v___x_1378_;
v___y_1358_ = v___x_1377_;
v___y_1359_ = v___x_1380_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1381_; 
lean_dec(v___y_1372_);
v___x_1381_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72));
v___y_1354_ = v___x_1375_;
v___y_1355_ = v___x_1374_;
v___y_1356_ = v___x_1376_;
v___y_1357_ = v___x_1378_;
v___y_1358_ = v___x_1377_;
v___y_1359_ = v___x_1381_;
goto v___jp_1353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___boxed(lean_object* v_x_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1(v_x_1392_, v_a_1393_, v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1(lean_object* v_x_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = ((lean_object*)(l_Lake_customDataDecl___closed__1));
lean_inc(v_x_1444_);
v___x_1448_ = l_Lean_Syntax_isOfKind(v_x_1444_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec_ref(v_a_1445_);
lean_dec(v_x_1444_);
v___x_1449_ = lean_box(1);
v___x_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v_a_1446_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v_tk_1454_; lean_object* v___x_1455_; lean_object* v_pkg_1456_; lean_object* v___x_1457_; lean_object* v_tgt_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1503_; lean_object* v___x_1524_; 
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1451_);
v___x_1453_ = lean_unsigned_to_nat(1u);
v_tk_1454_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1453_);
v___x_1455_ = lean_unsigned_to_nat(2u);
v_pkg_1456_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1455_);
v___x_1457_ = lean_unsigned_to_nat(3u);
v_tgt_1458_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1457_);
v___x_1459_ = lean_unsigned_to_nat(5u);
v___x_1460_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1459_);
lean_dec(v_x_1444_);
v___x_1524_ = l_Lean_Syntax_getOptional_x3f(v___x_1452_);
lean_dec(v___x_1452_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_box(0);
v___y_1503_ = v___x_1525_;
goto v___jp_1502_;
}
else
{
lean_object* v_val_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
v_val_1526_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1524_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_val_1526_);
lean_dec(v___x_1524_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_val_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
v___y_1503_ = v___x_1531_;
goto v___jp_1502_;
}
}
}
v___jp_1461_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1473_ = l_Array_append___redArg(v___y_1468_, v___y_1472_);
lean_dec_ref(v___y_1472_);
lean_inc(v___y_1466_);
lean_inc(v___y_1471_);
v___x_1474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1474_, 0, v___y_1471_);
lean_ctor_set(v___x_1474_, 1, v___y_1466_);
lean_ctor_set(v___x_1474_, 2, v___x_1473_);
v___x_1475_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0));
lean_inc(v___y_1471_);
v___x_1476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___y_1471_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_1471_);
v___x_1478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___y_1471_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1));
v___x_1480_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6));
v___x_1481_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20));
lean_inc(v___y_1471_);
v___x_1482_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___y_1471_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22));
v___x_1484_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
v___x_1485_ = lean_box(0);
v___x_1486_ = l_Lean_addMacroScope(v___y_1464_, v___x_1485_, v___y_1469_);
v___x_1487_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3));
lean_inc(v___y_1471_);
v___x_1488_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1488_, 0, v___y_1471_);
lean_ctor_set(v___x_1488_, 1, v___x_1484_);
lean_ctor_set(v___x_1488_, 2, v___x_1486_);
lean_ctor_set(v___x_1488_, 3, v___x_1487_);
lean_inc(v___y_1471_);
v___x_1489_ = l_Lean_Syntax_node1(v___y_1471_, v___x_1483_, v___x_1488_);
lean_inc(v___y_1471_);
v___x_1490_ = l_Lean_Syntax_node2(v___y_1471_, v___x_1480_, v___x_1482_, v___x_1489_);
v___x_1491_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36));
lean_inc(v___y_1471_);
v___x_1492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1471_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
lean_inc(v___y_1466_);
lean_inc(v___y_1471_);
v___x_1493_ = l_Lean_Syntax_node1(v___y_1471_, v___y_1466_, v___y_1470_);
lean_inc(v___y_1471_);
v___x_1494_ = l_Lean_Syntax_node3(v___y_1471_, v___y_1466_, v___y_1462_, v___x_1492_, v___x_1493_);
v___x_1495_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28));
lean_inc(v___y_1471_);
v___x_1496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1471_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
lean_inc(v___y_1471_);
v___x_1497_ = l_Lean_Syntax_node3(v___y_1471_, v___x_1479_, v___x_1490_, v___x_1494_, v___x_1496_);
v___x_1498_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2));
lean_inc(v___y_1471_);
v___x_1499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___y_1471_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = l_Lean_Syntax_node8(v___y_1471_, v___y_1467_, v___x_1474_, v___x_1476_, v___y_1465_, v___x_1478_, v___y_1463_, v___x_1497_, v___x_1499_, v___x_1460_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v_a_1446_);
return v___x_1501_;
}
v___jp_1502_:
{
lean_object* v_quotContext_1504_; lean_object* v_currMacroScope_1505_; lean_object* v_ref_1506_; lean_object* v_ref_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_quotContext_1504_ = lean_ctor_get(v_a_1445_, 1);
lean_inc(v_quotContext_1504_);
v_currMacroScope_1505_ = lean_ctor_get(v_a_1445_, 2);
lean_inc(v_currMacroScope_1505_);
v_ref_1506_ = lean_ctor_get(v_a_1445_, 5);
lean_inc(v_ref_1506_);
lean_dec_ref(v_a_1445_);
v_ref_1507_ = l_Lean_replaceRef(v_tk_1454_, v_ref_1506_);
lean_dec(v_ref_1506_);
lean_dec(v_tk_1454_);
v___x_1508_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5));
v___x_1509_ = 0;
v___x_1510_ = l_Lean_mkCIdentFrom(v_ref_1507_, v___x_1508_, v___x_1509_);
v___x_1511_ = l_Lean_TSyntax_getId(v_pkg_1456_);
v___x_1512_ = l_Lean_TSyntax_getId(v_tgt_1458_);
lean_inc(v___x_1512_);
lean_inc(v___x_1511_);
v___x_1513_ = l_Lean_Name_append(v___x_1511_, v___x_1512_);
v___x_1514_ = l_Lean_mkIdentFrom(v_tgt_1458_, v___x_1513_, v___x_1509_);
lean_dec(v_tgt_1458_);
v___x_1515_ = l_Lake_Name_quoteFrom(v_pkg_1456_, v___x_1511_, v___x_1509_);
lean_inc(v___x_1515_);
v___x_1516_ = l_Lake_Name_quoteFrom(v___x_1515_, v___x_1512_, v___x_1509_);
v___x_1517_ = l_Lean_SourceInfo_fromRef(v_ref_1507_, v___x_1509_);
lean_dec(v_ref_1507_);
v___x_1518_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70));
v___x_1519_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_1520_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_1503_) == 1)
{
lean_object* v_val_1521_; lean_object* v___x_1522_; 
v_val_1521_ = lean_ctor_get(v___y_1503_, 0);
lean_inc(v_val_1521_);
lean_dec_ref(v___y_1503_);
v___x_1522_ = l_Array_mkArray1___redArg(v_val_1521_);
v___y_1462_ = v___x_1515_;
v___y_1463_ = v___x_1510_;
v___y_1464_ = v_quotContext_1504_;
v___y_1465_ = v___x_1514_;
v___y_1466_ = v___x_1519_;
v___y_1467_ = v___x_1518_;
v___y_1468_ = v___x_1520_;
v___y_1469_ = v_currMacroScope_1505_;
v___y_1470_ = v___x_1516_;
v___y_1471_ = v___x_1517_;
v___y_1472_ = v___x_1522_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1523_; 
lean_dec(v___y_1503_);
v___x_1523_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72));
v___y_1462_ = v___x_1515_;
v___y_1463_ = v___x_1510_;
v___y_1464_ = v_quotContext_1504_;
v___y_1465_ = v___x_1514_;
v___y_1466_ = v___x_1519_;
v___y_1467_ = v___x_1518_;
v___y_1468_ = v___x_1520_;
v___y_1469_ = v_currMacroScope_1505_;
v___y_1470_ = v___x_1516_;
v___y_1471_ = v___x_1517_;
v___y_1472_ = v___x_1523_;
goto v___jp_1461_;
}
}
}
}
}
lean_object* runtime_initialize_Lake_Build_Key(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Family(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Kinds(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Kinds(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Data(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Build_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Family(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Dynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Kinds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Kinds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Config_Kinds(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Data(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Config_Kinds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Key(uint8_t builtin);
lean_object* initialize_Lake_Util_Family(uint8_t builtin);
lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* initialize_Lake_Config_Kinds(uint8_t builtin);
lean_object* initialize_Lake_Config_Kinds(uint8_t builtin);
lean_object* initialize_Lake_Util_Name(uint8_t builtin);
lean_object* initialize_Lake_Config_Kinds(uint8_t builtin);
lean_object* initialize_Lake_Util_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Data(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Family(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Kinds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Kinds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Kinds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Data(builtin);
}
#ifdef __cplusplus
}
#endif
