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
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "cannot generate facet declaration name from facet name"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30_value;
static const lean_string_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Facet"};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31_value;
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
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(136, 71, 28, 207, 18, 40, 68, 73)}};
static const lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13 = (const lean_object*)&l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___boxed(lean_object*, lean_object*, lean_object*);
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
lean_inc(v___y_280_);
lean_inc(v___y_281_);
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
v_currMacroScope_368_ = lean_ctor_get(v_a_263_, 2);
v_ref_369_ = lean_ctor_get(v_a_263_, 5);
v___x_370_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66));
v___x_371_ = 0;
v___x_372_ = l_Lean_mkCIdentFrom(v_ref_369_, v___x_370_, v___x_371_);
v___x_373_ = l_Lean_TSyntax_getId(v_kind_272_);
lean_inc(v_kind_272_);
v___x_374_ = l_Lake_Name_quoteFrom(v_kind_272_, v___x_373_, v___x_371_);
v___x_375_ = l_Lean_SourceInfo_fromRef(v_ref_369_, v___x_371_);
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
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___boxed(lean_object* v_x_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1(v_x_392_, v_a_393_, v_a_394_);
lean_dec_ref(v_a_393_);
return v_res_395_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5));
v___x_484_ = l_String_toRawSubstring_x27(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8));
v___x_489_ = l_String_toRawSubstring_x27(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15));
v___x_498_ = l_String_toRawSubstring_x27(v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23));
v___x_509_ = l_String_toRawSubstring_x27(v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v_fam_521_, lean_object* v___x_522_, lean_object* v___x_523_, lean_object* v___x_524_, uint8_t v___x_525_, lean_object* v___y_526_, lean_object* v_name_527_, lean_object* v_ns_528_, lean_object* v___x_529_, uint8_t v___x_530_, lean_object* v_tk_531_, lean_object* v___y_532_, lean_object* v___x_533_, lean_object* v_____r_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v_id_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___x_730_; uint8_t v___y_732_; 
v___x_730_ = l_Lean_TSyntax_getId(v_name_527_);
if (lean_obj_tag(v___y_532_) == 0)
{
v___y_732_ = v___x_525_;
goto v___jp_731_;
}
else
{
v___y_732_ = v___x_530_;
goto v___jp_731_;
}
v___jp_537_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
lean_inc_ref(v___y_551_);
v___x_555_ = l_Array_append___redArg(v___y_551_, v___y_554_);
lean_dec_ref(v___y_554_);
lean_inc(v___y_542_);
lean_inc(v___y_541_);
v___x_556_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_556_, 0, v___y_541_);
lean_ctor_set(v___x_556_, 1, v___y_542_);
lean_ctor_set(v___x_556_, 2, v___x_555_);
v___x_557_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14));
v___x_558_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0));
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_559_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___x_557_, v___x_558_);
v___x_560_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1));
lean_inc(v___y_541_);
v___x_561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_561_, 0, v___y_541_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2));
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_563_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___x_557_, v___x_562_);
v___x_564_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15));
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_565_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___x_557_, v___x_564_);
lean_inc(v___y_542_);
lean_inc(v___y_541_);
v___x_566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_566_, 0, v___y_541_);
lean_ctor_set(v___x_566_, 1, v___y_542_);
lean_ctor_set(v___x_566_, 2, v___y_551_);
lean_inc_ref(v___x_566_);
lean_inc(v___y_541_);
v___x_567_ = l_Lean_Syntax_node1(v___y_541_, v___x_565_, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3));
v___x_569_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4));
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_570_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___x_568_, v___x_569_);
v___x_571_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6);
v___x_572_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7));
lean_inc(v___y_545_);
lean_inc(v___y_550_);
v___x_573_ = l_Lean_addMacroScope(v___y_550_, v___x_572_, v___y_545_);
v___x_574_ = lean_box(0);
lean_inc(v___y_541_);
v___x_575_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_575_, 0, v___y_541_);
lean_ctor_set(v___x_575_, 1, v___x_571_);
lean_ctor_set(v___x_575_, 2, v___x_573_);
lean_ctor_set(v___x_575_, 3, v___x_574_);
lean_inc_ref(v___x_566_);
lean_inc(v___x_570_);
lean_inc(v___y_541_);
v___x_576_ = l_Lean_Syntax_node2(v___y_541_, v___x_570_, v___x_575_, v___x_566_);
lean_inc(v___x_567_);
lean_inc(v___x_563_);
lean_inc(v___y_541_);
v___x_577_ = l_Lean_Syntax_node2(v___y_541_, v___x_563_, v___x_567_, v___x_576_);
v___x_578_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36));
lean_inc(v___y_541_);
v___x_579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_579_, 0, v___y_541_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9);
v___x_581_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10));
lean_inc(v___y_545_);
lean_inc(v___y_550_);
v___x_582_ = l_Lean_addMacroScope(v___y_550_, v___x_581_, v___y_545_);
lean_inc(v___y_541_);
v___x_583_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_583_, 0, v___y_541_);
lean_ctor_set(v___x_583_, 1, v___x_580_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
lean_ctor_set(v___x_583_, 3, v___x_574_);
lean_inc_ref(v___x_566_);
lean_inc(v___y_541_);
v___x_584_ = l_Lean_Syntax_node2(v___y_541_, v___x_570_, v___x_583_, v___x_566_);
lean_inc(v___x_567_);
lean_inc(v___y_541_);
v___x_585_ = l_Lean_Syntax_node2(v___y_541_, v___x_563_, v___x_567_, v___x_584_);
lean_inc(v___y_542_);
lean_inc(v___y_541_);
v___x_586_ = l_Lean_Syntax_node3(v___y_541_, v___y_542_, v___x_577_, v___x_579_, v___x_585_);
v___x_587_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60));
lean_inc(v___y_541_);
v___x_588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_588_, 0, v___y_541_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
lean_inc(v___y_541_);
v___x_589_ = l_Lean_Syntax_node3(v___y_541_, v___x_559_, v___x_561_, v___x_586_, v___x_588_);
lean_inc(v___y_542_);
lean_inc(v___y_541_);
v___x_590_ = l_Lean_Syntax_node1(v___y_541_, v___y_542_, v___x_589_);
v___x_591_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10));
lean_inc_ref(v___y_544_);
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_592_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___y_544_, v___x_591_);
lean_inc(v___y_541_);
v___x_593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_593_, 0, v___y_541_);
lean_ctor_set(v___x_593_, 1, v___x_591_);
lean_inc(v___y_541_);
v___x_594_ = l_Lean_Syntax_node1(v___y_541_, v___x_592_, v___x_593_);
lean_inc(v___y_542_);
lean_inc(v___y_541_);
v___x_595_ = l_Lean_Syntax_node1(v___y_541_, v___y_542_, v___x_594_);
lean_inc_ref_n(v___x_566_, 4);
lean_inc(v___x_595_);
lean_inc(v___y_539_);
lean_inc(v___y_541_);
v___x_596_ = l_Lean_Syntax_node7(v___y_541_, v___y_539_, v___x_556_, v___x_590_, v___x_595_, v___x_566_, v___x_566_, v___x_566_, v___x_566_);
v___x_597_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11));
lean_inc_ref(v___y_544_);
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_598_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___y_544_, v___x_597_);
v___x_599_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12));
lean_inc(v___y_541_);
v___x_600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_600_, 0, v___y_541_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13));
lean_inc_ref(v___y_544_);
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_602_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___y_544_, v___x_601_);
v___x_603_ = lean_mk_empty_array_with_capacity(v___x_518_);
v___x_604_ = lean_box(2);
lean_inc(v___y_542_);
v___x_605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___y_542_);
lean_ctor_set(v___x_605_, 2, v___x_603_);
v___x_606_ = lean_mk_empty_array_with_capacity(v___x_519_);
v___x_607_ = lean_array_push(v___x_606_, v___y_547_);
v___x_608_ = lean_array_push(v___x_607_, v___x_605_);
v___x_609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_609_, 0, v___x_604_);
lean_ctor_set(v___x_609_, 1, v___x_602_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
v___x_610_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14));
lean_inc_ref(v___y_544_);
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_611_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___y_544_, v___x_610_);
lean_inc_ref_n(v___x_566_, 2);
lean_inc(v___y_541_);
v___x_612_ = l_Lean_Syntax_node2(v___y_541_, v___x_611_, v___x_566_, v___x_566_);
v___x_613_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31));
lean_inc_ref(v___y_544_);
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_614_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___y_544_, v___x_613_);
v___x_615_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2));
lean_inc(v___y_541_);
v___x_616_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_616_, 0, v___y_541_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62));
v___x_618_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63));
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_619_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___x_617_, v___x_618_);
lean_inc_ref_n(v___x_566_, 2);
lean_inc(v___y_541_);
v___x_620_ = l_Lean_Syntax_node2(v___y_541_, v___x_619_, v___x_566_, v___x_566_);
lean_inc_ref(v___x_566_);
lean_inc(v___x_620_);
lean_inc(v___y_548_);
lean_inc_ref(v___x_616_);
lean_inc(v___x_614_);
lean_inc(v___y_541_);
v___x_621_ = l_Lean_Syntax_node4(v___y_541_, v___x_614_, v___x_616_, v___y_548_, v___x_620_, v___x_566_);
lean_inc_ref(v___x_566_);
lean_inc(v___y_541_);
v___x_622_ = l_Lean_Syntax_node5(v___y_541_, v___x_598_, v___x_600_, v___x_609_, v___x_612_, v___x_621_, v___x_566_);
lean_inc(v___y_549_);
lean_inc(v___y_541_);
v___x_623_ = l_Lean_Syntax_node2(v___y_541_, v___y_549_, v___x_596_, v___x_622_);
v___x_624_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69));
lean_inc_ref(v___x_520_);
v___x_625_ = l_Lean_Name_mkStr2(v___x_520_, v___x_624_);
v___x_626_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0));
lean_inc(v___y_541_);
v___x_627_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_627_, 0, v___y_541_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_541_);
v___x_629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_629_, 0, v___y_541_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
lean_inc(v___x_522_);
lean_inc_ref(v___x_616_);
lean_inc(v___y_548_);
lean_inc_ref(v___x_629_);
lean_inc_ref(v___x_566_);
lean_inc(v___y_541_);
v___x_630_ = l_Lean_Syntax_node8(v___y_541_, v___x_625_, v___x_566_, v___x_627_, v___y_538_, v___x_629_, v_fam_521_, v___y_548_, v___x_616_, v___x_522_);
lean_inc_ref_n(v___x_566_, 6);
lean_inc(v___y_541_);
v___x_631_ = l_Lean_Syntax_node7(v___y_541_, v___y_539_, v___x_566_, v___x_566_, v___x_595_, v___x_566_, v___x_566_, v___x_566_, v___x_566_);
v___x_632_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12));
lean_inc_ref(v___y_544_);
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_633_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___y_544_, v___x_632_);
lean_inc(v___y_541_);
v___x_634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_634_, 0, v___y_541_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
v___x_635_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17));
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_636_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___y_544_, v___x_635_);
v___x_637_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19));
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_638_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___x_557_, v___x_637_);
v___x_639_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21));
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_640_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___x_557_, v___x_639_);
v___x_641_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15));
v___x_642_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16);
v___x_643_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17));
lean_inc(v___y_545_);
lean_inc(v___y_550_);
v___x_644_ = l_Lean_addMacroScope(v___y_550_, v___x_643_, v___y_545_);
lean_inc_ref(v___x_520_);
v___x_645_ = l_Lean_Name_mkStr2(v___x_520_, v___x_641_);
lean_inc(v___x_645_);
v___x_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_574_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
v___x_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___x_574_);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_646_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
lean_inc(v___y_541_);
v___x_650_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_650_, 0, v___y_541_);
lean_ctor_set(v___x_650_, 1, v___x_642_);
lean_ctor_set(v___x_650_, 2, v___x_644_);
lean_ctor_set(v___x_650_, 3, v___x_649_);
lean_inc_ref(v___x_523_);
v___x_651_ = l_String_toRawSubstring_x27(v___x_523_);
v___x_652_ = l_Lean_Name_mkStr1(v___x_523_);
lean_inc(v___y_545_);
lean_inc(v___y_550_);
v___x_653_ = l_Lean_addMacroScope(v___y_550_, v___x_652_, v___y_545_);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_524_);
lean_ctor_set(v___x_654_, 1, v___x_574_);
v___x_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_574_);
lean_inc(v___y_541_);
v___x_656_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_656_, 0, v___y_541_);
lean_ctor_set(v___x_656_, 1, v___x_651_);
lean_ctor_set(v___x_656_, 2, v___x_653_);
lean_ctor_set(v___x_656_, 3, v___x_655_);
v___x_657_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18));
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_658_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___x_557_, v___x_657_);
v___x_659_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19));
lean_inc_ref(v___y_546_);
lean_inc_ref(v___y_543_);
v___x_660_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___x_557_, v___x_659_);
v___x_661_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20));
lean_inc(v___y_541_);
v___x_662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_662_, 0, v___y_541_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22));
v___x_664_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
v___x_665_ = lean_box(0);
lean_inc(v___y_545_);
lean_inc(v___y_550_);
v___x_666_ = l_Lean_addMacroScope(v___y_550_, v___x_665_, v___y_545_);
v___x_667_ = l_Lean_Name_mkStr1(v___x_520_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_inc_ref(v___y_543_);
v___x_669_ = l_Lean_Name_mkStr1(v___y_543_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
v___x_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_574_);
v___x_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_668_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
lean_inc(v___y_541_);
v___x_673_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_673_, 0, v___y_541_);
lean_ctor_set(v___x_673_, 1, v___x_664_);
lean_ctor_set(v___x_673_, 2, v___x_666_);
lean_ctor_set(v___x_673_, 3, v___x_672_);
lean_inc(v___y_541_);
v___x_674_ = l_Lean_Syntax_node1(v___y_541_, v___x_663_, v___x_673_);
lean_inc(v___y_541_);
v___x_675_ = l_Lean_Syntax_node2(v___y_541_, v___x_660_, v___x_662_, v___x_674_);
v___x_676_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26));
v___x_677_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27));
lean_inc(v___y_541_);
v___x_678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_678_, 0, v___y_541_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
lean_inc(v___y_541_);
v___x_679_ = l_Lean_Syntax_node3(v___y_541_, v___x_676_, v___y_540_, v___x_678_, v___y_553_);
v___x_680_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28));
lean_inc(v___y_541_);
v___x_681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_681_, 0, v___y_541_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
lean_inc_ref(v___x_681_);
lean_inc(v___x_675_);
lean_inc(v___x_658_);
lean_inc(v___y_541_);
v___x_682_ = l_Lean_Syntax_node3(v___y_541_, v___x_658_, v___x_675_, v___x_679_, v___x_681_);
lean_inc(v___x_522_);
lean_inc_ref(v___x_656_);
lean_inc(v___y_542_);
lean_inc(v___y_541_);
v___x_683_ = l_Lean_Syntax_node3(v___y_541_, v___y_542_, v___x_656_, v___x_682_, v___x_522_);
lean_inc_ref(v___x_650_);
lean_inc(v___x_640_);
lean_inc(v___y_541_);
v___x_684_ = l_Lean_Syntax_node2(v___y_541_, v___x_640_, v___x_650_, v___x_683_);
lean_inc(v___y_541_);
v___x_685_ = l_Lean_Syntax_node2(v___y_541_, v___x_638_, v___x_629_, v___x_684_);
lean_inc_ref(v___x_566_);
lean_inc(v___y_541_);
v___x_686_ = l_Lean_Syntax_node2(v___y_541_, v___x_636_, v___x_566_, v___x_685_);
v___x_687_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29));
v___x_688_ = l_Lean_Name_mkStr4(v___y_543_, v___y_546_, v___x_557_, v___x_687_);
lean_inc(v___y_541_);
v___x_689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_689_, 0, v___y_541_);
lean_ctor_set(v___x_689_, 1, v___x_687_);
lean_inc(v___y_542_);
lean_inc(v___y_541_);
v___x_690_ = l_Lean_Syntax_node3(v___y_541_, v___y_542_, v___x_656_, v___y_548_, v___x_522_);
lean_inc(v___y_541_);
v___x_691_ = l_Lean_Syntax_node2(v___y_541_, v___x_640_, v___x_650_, v___x_690_);
lean_inc(v___y_541_);
v___x_692_ = l_Lean_Syntax_node3(v___y_541_, v___x_658_, v___x_675_, v___x_691_, v___x_681_);
lean_inc(v___y_541_);
v___x_693_ = l_Lean_Syntax_node2(v___y_541_, v___x_688_, v___x_689_, v___x_692_);
lean_inc_ref(v___x_566_);
lean_inc(v___y_541_);
v___x_694_ = l_Lean_Syntax_node4(v___y_541_, v___x_614_, v___x_616_, v___x_693_, v___x_620_, v___x_566_);
lean_inc_ref(v___x_566_);
lean_inc(v___y_541_);
v___x_695_ = l_Lean_Syntax_node6(v___y_541_, v___x_633_, v___x_567_, v___x_634_, v___x_566_, v___x_566_, v___x_686_, v___x_694_);
lean_inc(v___y_541_);
v___x_696_ = l_Lean_Syntax_node2(v___y_541_, v___y_549_, v___x_631_, v___x_695_);
v___x_697_ = l_Lean_Syntax_node3(v___y_541_, v___y_542_, v___x_623_, v___x_630_, v___x_696_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___y_552_);
return v___x_698_;
}
v___jp_699_:
{
lean_object* v_quotContext_707_; lean_object* v_currMacroScope_708_; lean_object* v_ref_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_quotContext_707_ = lean_ctor_get(v___y_705_, 1);
v_currMacroScope_708_ = lean_ctor_get(v___y_705_, 2);
v_ref_709_ = lean_ctor_get(v___y_705_, 5);
v___x_710_ = l_Lean_SourceInfo_fromRef(v_ref_709_, v___x_525_);
v___x_711_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_712_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3));
v___x_713_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4));
v___x_714_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5));
v___x_715_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7));
v___x_716_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9));
v___x_717_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_526_) == 1)
{
lean_object* v_val_718_; lean_object* v___x_719_; 
v_val_718_ = lean_ctor_get(v___y_526_, 0);
lean_inc(v_val_718_);
lean_dec_ref(v___y_526_);
v___x_719_ = l_Array_mkArray1___redArg(v_val_718_);
v___y_538_ = v___y_701_;
v___y_539_ = v___x_716_;
v___y_540_ = v___y_703_;
v___y_541_ = v___x_710_;
v___y_542_ = v___x_711_;
v___y_543_ = v___x_712_;
v___y_544_ = v___x_714_;
v___y_545_ = v_currMacroScope_708_;
v___y_546_ = v___x_713_;
v___y_547_ = v_id_704_;
v___y_548_ = v___y_700_;
v___y_549_ = v___x_715_;
v___y_550_ = v_quotContext_707_;
v___y_551_ = v___x_717_;
v___y_552_ = v___y_706_;
v___y_553_ = v___y_702_;
v___y_554_ = v___x_719_;
goto v___jp_537_;
}
else
{
lean_object* v___x_720_; 
lean_dec(v___y_526_);
v___x_720_ = lean_mk_empty_array_with_capacity(v___x_518_);
v___y_538_ = v___y_701_;
v___y_539_ = v___x_716_;
v___y_540_ = v___y_703_;
v___y_541_ = v___x_710_;
v___y_542_ = v___x_711_;
v___y_543_ = v___x_712_;
v___y_544_ = v___x_714_;
v___y_545_ = v_currMacroScope_708_;
v___y_546_ = v___x_713_;
v___y_547_ = v_id_704_;
v___y_548_ = v___y_700_;
v___y_549_ = v___x_715_;
v___y_550_ = v_quotContext_707_;
v___y_551_ = v___x_717_;
v___y_552_ = v___y_706_;
v___y_553_ = v___y_702_;
v___y_554_ = v___x_720_;
goto v___jp_537_;
}
}
v___jp_721_:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30));
v___x_727_ = l_Lean_Macro_throwErrorAt___redArg(v_name_527_, v___x_726_, v___y_535_, v___y_536_);
lean_dec(v_name_527_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v_a_729_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
v_a_729_ = lean_ctor_get(v___x_727_, 1);
lean_inc(v_a_729_);
lean_dec_ref(v___x_727_);
v___y_700_ = v___y_722_;
v___y_701_ = v___y_723_;
v___y_702_ = v___y_724_;
v___y_703_ = v___y_725_;
v_id_704_ = v_a_728_;
v___y_705_ = v___y_535_;
v___y_706_ = v_a_729_;
goto v___jp_699_;
}
else
{
lean_dec(v___y_725_);
lean_dec(v___y_724_);
lean_dec(v___y_723_);
lean_dec(v___y_722_);
lean_dec(v___y_526_);
lean_dec(v___x_524_);
lean_dec_ref(v___x_523_);
lean_dec(v___x_522_);
lean_dec(v_fam_521_);
lean_dec_ref(v___x_520_);
return v___x_727_;
}
}
v___jp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_inc(v___x_730_);
lean_inc(v_name_527_);
v___x_733_ = l_Lake_Name_quoteFrom(v_name_527_, v___x_730_, v___y_732_);
lean_inc(v___x_529_);
v___x_734_ = l_Lake_Name_quoteFrom(v_ns_528_, v___x_529_, v___x_530_);
lean_inc(v___x_730_);
v___x_735_ = l_Lean_Name_append(v___x_529_, v___x_730_);
lean_inc(v___x_735_);
v___x_736_ = l_Lean_mkIdentFrom(v_tk_531_, v___x_735_, v___x_530_);
v___x_737_ = l_Lake_Name_quoteFrom(v_tk_531_, v___x_735_, v___x_525_);
if (lean_obj_tag(v___y_532_) == 1)
{
lean_object* v_val_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec(v___x_730_);
lean_dec(v_name_527_);
v_val_738_ = lean_ctor_get(v___y_532_, 0);
v___x_739_ = l_Lean_Syntax_getArg(v_val_738_, v___x_518_);
v___x_740_ = l_Lean_Syntax_getId(v___x_739_);
v___x_741_ = l_Lean_Name_append(v___x_533_, v___x_740_);
v___x_742_ = l_Lean_mkIdentFrom(v___x_739_, v___x_741_, v___x_530_);
lean_dec(v___x_739_);
v___y_700_ = v___x_737_;
v___y_701_ = v___x_736_;
v___y_702_ = v___x_733_;
v___y_703_ = v___x_734_;
v_id_704_ = v___x_742_;
v___y_705_ = v___y_535_;
v___y_706_ = v___y_536_;
goto v___jp_699_;
}
else
{
if (lean_obj_tag(v___x_730_) == 1)
{
lean_object* v_pre_743_; 
v_pre_743_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_pre_743_);
if (lean_obj_tag(v_pre_743_) == 0)
{
lean_object* v_str_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_str_744_ = lean_ctor_get(v___x_730_, 1);
lean_inc_ref(v_str_744_);
lean_dec_ref(v___x_730_);
v___x_745_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31));
v___x_746_ = lean_string_append(v_str_744_, v___x_745_);
v___x_747_ = l_Lean_Name_str___override(v___x_533_, v___x_746_);
v___x_748_ = l_Lean_mkIdentFrom(v_name_527_, v___x_747_, v___x_530_);
lean_dec(v_name_527_);
v___y_700_ = v___x_737_;
v___y_701_ = v___x_736_;
v___y_702_ = v___x_733_;
v___y_703_ = v___x_734_;
v_id_704_ = v___x_748_;
v___y_705_ = v___y_535_;
v___y_706_ = v___y_536_;
goto v___jp_699_;
}
else
{
lean_dec_ref(v___x_730_);
lean_dec(v_pre_743_);
lean_dec(v___x_533_);
v___y_722_ = v___x_737_;
v___y_723_ = v___x_736_;
v___y_724_ = v___x_733_;
v___y_725_ = v___x_734_;
goto v___jp_721_;
}
}
else
{
lean_dec(v___x_730_);
lean_dec(v___x_533_);
v___y_722_ = v___x_737_;
v___y_723_ = v___x_736_;
v___y_724_ = v___x_733_;
v___y_725_ = v___x_734_;
goto v___jp_721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___boxed(lean_object** _args){
lean_object* v___x_749_ = _args[0];
lean_object* v___x_750_ = _args[1];
lean_object* v___x_751_ = _args[2];
lean_object* v_fam_752_ = _args[3];
lean_object* v___x_753_ = _args[4];
lean_object* v___x_754_ = _args[5];
lean_object* v___x_755_ = _args[6];
lean_object* v___x_756_ = _args[7];
lean_object* v___y_757_ = _args[8];
lean_object* v_name_758_ = _args[9];
lean_object* v_ns_759_ = _args[10];
lean_object* v___x_760_ = _args[11];
lean_object* v___x_761_ = _args[12];
lean_object* v_tk_762_ = _args[13];
lean_object* v___y_763_ = _args[14];
lean_object* v___x_764_ = _args[15];
lean_object* v_____r_765_ = _args[16];
lean_object* v___y_766_ = _args[17];
lean_object* v___y_767_ = _args[18];
_start:
{
uint8_t v___x_12981__boxed_768_; uint8_t v___x_12984__boxed_769_; lean_object* v_res_770_; 
v___x_12981__boxed_768_ = lean_unbox(v___x_756_);
v___x_12984__boxed_769_ = lean_unbox(v___x_761_);
v_res_770_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(v___x_749_, v___x_750_, v___x_751_, v_fam_752_, v___x_753_, v___x_754_, v___x_755_, v___x_12981__boxed_768_, v___y_757_, v_name_758_, v_ns_759_, v___x_760_, v___x_12984__boxed_769_, v_tk_762_, v___y_763_, v___x_764_, v_____r_765_, v___y_766_, v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_763_);
lean_dec(v___x_750_);
lean_dec(v___x_749_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1(lean_object* v_x_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___y_782_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_801_ = ((lean_object*)(l_Lake_dataTypeDecl___closed__0));
v___x_802_ = ((lean_object*)(l_Lake_builtinFacetCommand___closed__1));
lean_inc(v_x_778_);
v___x_803_ = l_Lean_Syntax_isOfKind(v_x_778_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec(v_x_778_);
v___x_804_ = lean_box(1);
v___x_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v_a_780_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_tk_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_name_813_; lean_object* v___x_814_; lean_object* v_ns_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_877_; lean_object* v___x_888_; 
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = l_Lean_Syntax_getArg(v_x_778_, v___x_806_);
v___x_808_ = lean_unsigned_to_nat(1u);
v_tk_809_ = l_Lean_Syntax_getArg(v_x_778_, v___x_808_);
v___x_810_ = lean_unsigned_to_nat(2u);
v___x_811_ = l_Lean_Syntax_getArg(v_x_778_, v___x_810_);
v___x_812_ = lean_unsigned_to_nat(3u);
v_name_813_ = l_Lean_Syntax_getArg(v_x_778_, v___x_812_);
v___x_814_ = lean_unsigned_to_nat(5u);
v_ns_815_ = l_Lean_Syntax_getArg(v_x_778_, v___x_814_);
v___x_816_ = lean_unsigned_to_nat(7u);
v___x_817_ = l_Lean_Syntax_getArg(v_x_778_, v___x_816_);
lean_dec(v_x_778_);
v___x_888_ = l_Lean_Syntax_getOptional_x3f(v___x_811_);
lean_dec(v___x_811_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_889_; 
v___x_889_ = lean_box(0);
v___y_877_ = v___x_889_;
goto v___jp_876_;
}
else
{
lean_object* v_val_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_val_890_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_888_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_val_890_);
lean_dec(v___x_888_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_val_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
v___y_877_ = v___x_895_;
goto v___jp_876_;
}
}
}
v___jp_818_:
{
lean_object* v_methods_821_; lean_object* v_quotContext_822_; lean_object* v_currMacroScope_823_; lean_object* v_currRecDepth_824_; lean_object* v_maxRecDepth_825_; lean_object* v_ref_826_; lean_object* v___x_827_; lean_object* v_ref_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_methods_821_ = lean_ctor_get(v_a_779_, 0);
v_quotContext_822_ = lean_ctor_get(v_a_779_, 1);
v_currMacroScope_823_ = lean_ctor_get(v_a_779_, 2);
v_currRecDepth_824_ = lean_ctor_get(v_a_779_, 3);
v_maxRecDepth_825_ = lean_ctor_get(v_a_779_, 4);
v_ref_826_ = lean_ctor_get(v_a_779_, 5);
v___x_827_ = l_Lean_TSyntax_getId(v_ns_815_);
v_ref_828_ = l_Lean_replaceRef(v_tk_809_, v_ref_826_);
lean_inc(v_maxRecDepth_825_);
lean_inc(v_currRecDepth_824_);
lean_inc(v_currMacroScope_823_);
lean_inc(v_quotContext_822_);
lean_inc(v_methods_821_);
v___x_829_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_829_, 0, v_methods_821_);
lean_ctor_set(v___x_829_, 1, v_quotContext_822_);
lean_ctor_set(v___x_829_, 2, v_currMacroScope_823_);
lean_ctor_set(v___x_829_, 3, v_currRecDepth_824_);
lean_ctor_set(v___x_829_, 4, v_maxRecDepth_825_);
lean_ctor_set(v___x_829_, 5, v_ref_828_);
lean_inc(v___x_827_);
v___x_830_ = l_Lean_Macro_resolveNamespace(v___x_827_, v___x_829_, v_a_780_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
if (lean_obj_tag(v_a_831_) == 1)
{
lean_object* v_a_832_; lean_object* v_head_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; lean_object* v_fam_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_a_832_ = lean_ctor_get(v___x_830_, 1);
lean_inc(v_a_832_);
lean_dec_ref(v___x_830_);
v_head_833_ = lean_ctor_get(v_a_831_, 0);
lean_inc(v_head_833_);
lean_dec_ref(v_a_831_);
v___x_834_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0));
v___x_835_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1));
v___x_836_ = 0;
v_fam_837_ = l_Lean_mkCIdentFrom(v_tk_809_, v___x_835_, v___x_836_);
v___x_838_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace(v_head_833_);
lean_dec(v_head_833_);
v___x_839_ = l_Lean_Name_isAnonymous(v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_box(0);
v___x_841_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(v___x_806_, v___x_810_, v___x_801_, v_fam_837_, v___x_817_, v___x_834_, v___x_835_, v___x_836_, v___y_820_, v_name_813_, v_ns_815_, v___x_838_, v___x_803_, v_tk_809_, v___y_819_, v___x_827_, v___x_840_, v___x_829_, v_a_832_);
lean_dec_ref(v___x_829_);
lean_dec(v___y_819_);
v___y_782_ = v___x_841_;
goto v___jp_781_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_842_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2));
lean_inc(v___x_827_);
v___x_843_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_827_, v___x_839_);
v___x_844_ = lean_string_append(v___x_842_, v___x_843_);
lean_dec_ref(v___x_843_);
v___x_845_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3));
v___x_846_ = lean_string_append(v___x_844_, v___x_845_);
v___x_847_ = l_Lean_Macro_throwErrorAt___redArg(v_ns_815_, v___x_846_, v___x_829_, v_a_832_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v_a_849_; lean_object* v___x_850_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
v_a_849_ = lean_ctor_get(v___x_847_, 1);
lean_inc(v_a_849_);
lean_dec_ref(v___x_847_);
v___x_850_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(v___x_806_, v___x_810_, v___x_801_, v_fam_837_, v___x_817_, v___x_834_, v___x_835_, v___x_836_, v___y_820_, v_name_813_, v_ns_815_, v___x_838_, v___x_803_, v_tk_809_, v___y_819_, v___x_827_, v_a_848_, v___x_829_, v_a_849_);
lean_dec_ref(v___x_829_);
lean_dec(v___y_819_);
v___y_782_ = v___x_850_;
goto v___jp_781_;
}
else
{
lean_object* v_a_851_; lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v___x_838_);
lean_dec(v_fam_837_);
lean_dec_ref(v___x_829_);
lean_dec(v___x_827_);
lean_dec(v___y_820_);
lean_dec(v___y_819_);
lean_dec(v___x_817_);
lean_dec(v_ns_815_);
lean_dec(v_name_813_);
lean_dec(v_tk_809_);
v_a_851_ = lean_ctor_get(v___x_847_, 0);
v_a_852_ = lean_ctor_get(v___x_847_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_847_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_inc(v_a_851_);
lean_dec(v___x_847_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_851_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec(v_a_831_);
lean_dec(v___y_820_);
lean_dec(v___y_819_);
lean_dec(v___x_817_);
lean_dec(v_name_813_);
lean_dec(v_tk_809_);
v_a_860_ = lean_ctor_get(v___x_830_, 1);
lean_inc(v_a_860_);
lean_dec_ref(v___x_830_);
v___x_861_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4));
v___x_862_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_827_, v___x_803_);
v___x_863_ = lean_string_append(v___x_861_, v___x_862_);
lean_dec_ref(v___x_862_);
v___x_864_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3));
v___x_865_ = lean_string_append(v___x_863_, v___x_864_);
v___x_866_ = l_Lean_Macro_throwErrorAt___redArg(v_ns_815_, v___x_865_, v___x_829_, v_a_860_);
lean_dec_ref(v___x_829_);
lean_dec(v_ns_815_);
v___y_782_ = v___x_866_;
goto v___jp_781_;
}
}
else
{
lean_object* v_a_867_; lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref(v___x_829_);
lean_dec(v___x_827_);
lean_dec(v___y_820_);
lean_dec(v___y_819_);
lean_dec(v___x_817_);
lean_dec(v_ns_815_);
lean_dec(v_name_813_);
lean_dec(v_tk_809_);
v_a_867_ = lean_ctor_get(v___x_830_, 0);
v_a_868_ = lean_ctor_get(v___x_830_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_830_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_inc(v_a_867_);
lean_dec(v___x_830_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_867_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
v___jp_876_:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Syntax_getOptional_x3f(v___x_807_);
lean_dec(v___x_807_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_879_; 
v___x_879_ = lean_box(0);
v___y_819_ = v___y_877_;
v___y_820_ = v___x_879_;
goto v___jp_818_;
}
else
{
lean_object* v_val_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_val_880_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_878_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_val_880_);
lean_dec(v___x_878_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_val_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
v___y_819_ = v___y_877_;
v___y_820_ = v___x_885_;
goto v___jp_818_;
}
}
}
}
}
v___jp_781_:
{
if (lean_obj_tag(v___y_782_) == 0)
{
lean_object* v_a_783_; lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_a_783_ = lean_ctor_get(v___y_782_, 0);
v_a_784_ = lean_ctor_get(v___y_782_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v___y_782_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___y_782_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_inc(v_a_783_);
lean_dec(v___y_782_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_783_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_a_792_; lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
v_a_792_ = lean_ctor_get(v___y_782_, 0);
v_a_793_ = lean_ctor_get(v___y_782_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v___y_782_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___y_782_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_inc(v_a_792_);
lean_dec(v___y_782_);
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
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 2, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___boxed(lean_object* v_x_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1(v_x_898_, v_a_899_, v_a_900_);
lean_dec_ref(v_a_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1(lean_object* v_x_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = ((lean_object*)(l_Lake_facetDataDecl___closed__1));
lean_inc(v_x_977_);
v___x_981_ = l_Lean_Syntax_isOfKind(v_x_977_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec(v_x_977_);
v___x_982_ = lean_box(1);
v___x_983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v_a_979_);
return v___x_983_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_tk_987_; lean_object* v___x_988_; lean_object* v_kind_989_; lean_object* v___x_990_; lean_object* v_name_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1086_; lean_object* v___x_1109_; 
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = l_Lean_Syntax_getArg(v_x_977_, v___x_984_);
v___x_986_ = lean_unsigned_to_nat(1u);
v_tk_987_ = l_Lean_Syntax_getArg(v_x_977_, v___x_986_);
v___x_988_ = lean_unsigned_to_nat(2u);
v_kind_989_ = l_Lean_Syntax_getArg(v_x_977_, v___x_988_);
v___x_990_ = lean_unsigned_to_nat(3u);
v_name_991_ = l_Lean_Syntax_getArg(v_x_977_, v___x_990_);
v___x_992_ = lean_unsigned_to_nat(5u);
v___x_993_ = l_Lean_Syntax_getArg(v_x_977_, v___x_992_);
lean_dec(v_x_977_);
v___x_1109_ = l_Lean_Syntax_getOptional_x3f(v___x_985_);
lean_dec(v___x_985_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_box(0);
v___y_1086_ = v___x_1110_;
goto v___jp_1085_;
}
else
{
lean_object* v_val_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_val_1111_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1109_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_val_1111_);
lean_dec(v___x_1109_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_val_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
v___y_1086_ = v___x_1116_;
goto v___jp_1085_;
}
}
}
v___jp_994_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_inc_ref(v___y_996_);
v___x_1009_ = l_Array_append___redArg(v___y_996_, v___y_1008_);
lean_dec_ref(v___y_1008_);
lean_inc(v___y_999_);
lean_inc(v___y_1002_);
v___x_1010_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1010_, 0, v___y_1002_);
lean_ctor_set(v___x_1010_, 1, v___y_999_);
lean_ctor_set(v___x_1010_, 2, v___x_1009_);
v___x_1011_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0));
lean_inc(v___y_1002_);
v___x_1012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___y_1002_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_1002_);
v___x_1014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___y_1002_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2));
lean_inc(v___y_1002_);
v___x_1016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___y_1002_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
lean_inc(v___x_993_);
lean_inc_ref(v___x_1016_);
lean_inc(v___y_1006_);
lean_inc_ref(v___x_1014_);
lean_inc(v___y_1002_);
v___x_1017_ = l_Lean_Syntax_node8(v___y_1002_, v___y_1003_, v___x_1010_, v___x_1012_, v___y_1000_, v___x_1014_, v___y_995_, v___y_1006_, v___x_1016_, v___x_993_);
v___x_1018_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7));
v___x_1019_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9));
lean_inc(v___y_999_);
lean_inc(v___y_1002_);
v___x_1020_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1020_, 0, v___y_1002_);
lean_ctor_set(v___x_1020_, 1, v___y_999_);
lean_ctor_set(v___x_1020_, 2, v___y_996_);
v___x_1021_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10));
v___x_1022_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11));
lean_inc(v___y_1002_);
v___x_1023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___y_1002_);
lean_ctor_set(v___x_1023_, 1, v___x_1021_);
lean_inc(v___y_1002_);
v___x_1024_ = l_Lean_Syntax_node1(v___y_1002_, v___x_1022_, v___x_1023_);
lean_inc(v___y_999_);
lean_inc(v___y_1002_);
v___x_1025_ = l_Lean_Syntax_node1(v___y_1002_, v___y_999_, v___x_1024_);
lean_inc_ref_n(v___x_1020_, 6);
lean_inc(v___y_1002_);
v___x_1026_ = l_Lean_Syntax_node7(v___y_1002_, v___x_1019_, v___x_1020_, v___x_1020_, v___x_1025_, v___x_1020_, v___x_1020_, v___x_1020_, v___x_1020_);
v___x_1027_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12));
v___x_1028_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13));
v___x_1029_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16));
lean_inc_ref(v___x_1020_);
lean_inc(v___y_1002_);
v___x_1030_ = l_Lean_Syntax_node1(v___y_1002_, v___x_1029_, v___x_1020_);
lean_inc(v___y_1002_);
v___x_1031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___y_1002_);
lean_ctor_set(v___x_1031_, 1, v___x_1027_);
v___x_1032_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18));
v___x_1033_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20));
v___x_1034_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22));
v___x_1035_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16);
v___x_1036_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17));
lean_inc(v___y_1007_);
lean_inc(v___y_1001_);
v___x_1037_ = l_Lean_addMacroScope(v___y_1001_, v___x_1036_, v___y_1007_);
v___x_1038_ = lean_box(0);
v___x_1039_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4));
lean_inc(v___y_1002_);
v___x_1040_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1040_, 0, v___y_1002_);
lean_ctor_set(v___x_1040_, 1, v___x_1035_);
lean_ctor_set(v___x_1040_, 2, v___x_1037_);
lean_ctor_set(v___x_1040_, 3, v___x_1039_);
lean_inc_ref(v___y_1004_);
v___x_1041_ = l_String_toRawSubstring_x27(v___y_1004_);
v___x_1042_ = l_Lean_Name_mkStr1(v___y_1004_);
lean_inc(v___y_1007_);
lean_inc(v___y_1001_);
v___x_1043_ = l_Lean_addMacroScope(v___y_1001_, v___x_1042_, v___y_1007_);
v___x_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___y_997_);
lean_ctor_set(v___x_1044_, 1, v___x_1038_);
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v___x_1038_);
lean_inc(v___y_1002_);
v___x_1046_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1046_, 0, v___y_1002_);
lean_ctor_set(v___x_1046_, 1, v___x_1041_);
lean_ctor_set(v___x_1046_, 2, v___x_1043_);
lean_ctor_set(v___x_1046_, 3, v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5));
v___x_1048_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6));
v___x_1049_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20));
lean_inc(v___y_1002_);
v___x_1050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___y_1002_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22));
v___x_1052_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
v___x_1053_ = lean_box(0);
lean_inc(v___y_1007_);
lean_inc(v___y_1001_);
v___x_1054_ = l_Lean_addMacroScope(v___y_1001_, v___x_1053_, v___y_1007_);
v___x_1055_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12));
lean_inc(v___y_1002_);
v___x_1056_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1056_, 0, v___y_1002_);
lean_ctor_set(v___x_1056_, 1, v___x_1052_);
lean_ctor_set(v___x_1056_, 2, v___x_1054_);
lean_ctor_set(v___x_1056_, 3, v___x_1055_);
lean_inc(v___y_1002_);
v___x_1057_ = l_Lean_Syntax_node1(v___y_1002_, v___x_1051_, v___x_1056_);
lean_inc(v___y_1002_);
v___x_1058_ = l_Lean_Syntax_node2(v___y_1002_, v___x_1048_, v___x_1050_, v___x_1057_);
v___x_1059_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26));
v___x_1060_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27));
lean_inc(v___y_1002_);
v___x_1061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___y_1002_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
lean_inc(v___y_1002_);
v___x_1062_ = l_Lean_Syntax_node3(v___y_1002_, v___x_1059_, v___y_1005_, v___x_1061_, v___y_998_);
v___x_1063_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28));
lean_inc(v___y_1002_);
v___x_1064_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___y_1002_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
lean_inc_ref(v___x_1064_);
lean_inc(v___x_1058_);
lean_inc(v___y_1002_);
v___x_1065_ = l_Lean_Syntax_node3(v___y_1002_, v___x_1047_, v___x_1058_, v___x_1062_, v___x_1064_);
lean_inc(v___x_993_);
lean_inc_ref(v___x_1046_);
lean_inc(v___y_999_);
lean_inc(v___y_1002_);
v___x_1066_ = l_Lean_Syntax_node3(v___y_1002_, v___y_999_, v___x_1046_, v___x_1065_, v___x_993_);
lean_inc_ref(v___x_1040_);
lean_inc(v___y_1002_);
v___x_1067_ = l_Lean_Syntax_node2(v___y_1002_, v___x_1034_, v___x_1040_, v___x_1066_);
lean_inc(v___y_1002_);
v___x_1068_ = l_Lean_Syntax_node2(v___y_1002_, v___x_1033_, v___x_1014_, v___x_1067_);
lean_inc_ref(v___x_1020_);
lean_inc(v___y_1002_);
v___x_1069_ = l_Lean_Syntax_node2(v___y_1002_, v___x_1032_, v___x_1020_, v___x_1068_);
v___x_1070_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32));
v___x_1071_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29));
v___x_1072_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13));
lean_inc(v___y_1002_);
v___x_1073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___y_1002_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
lean_inc(v___y_999_);
lean_inc(v___y_1002_);
v___x_1074_ = l_Lean_Syntax_node3(v___y_1002_, v___y_999_, v___x_1046_, v___y_1006_, v___x_993_);
lean_inc(v___y_1002_);
v___x_1075_ = l_Lean_Syntax_node2(v___y_1002_, v___x_1034_, v___x_1040_, v___x_1074_);
lean_inc(v___y_1002_);
v___x_1076_ = l_Lean_Syntax_node3(v___y_1002_, v___x_1047_, v___x_1058_, v___x_1075_, v___x_1064_);
lean_inc(v___y_1002_);
v___x_1077_ = l_Lean_Syntax_node2(v___y_1002_, v___x_1072_, v___x_1073_, v___x_1076_);
v___x_1078_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64));
lean_inc_ref_n(v___x_1020_, 2);
lean_inc(v___y_1002_);
v___x_1079_ = l_Lean_Syntax_node2(v___y_1002_, v___x_1078_, v___x_1020_, v___x_1020_);
lean_inc_ref(v___x_1020_);
lean_inc(v___y_1002_);
v___x_1080_ = l_Lean_Syntax_node4(v___y_1002_, v___x_1070_, v___x_1016_, v___x_1077_, v___x_1079_, v___x_1020_);
lean_inc_ref(v___x_1020_);
lean_inc(v___y_1002_);
v___x_1081_ = l_Lean_Syntax_node6(v___y_1002_, v___x_1028_, v___x_1030_, v___x_1031_, v___x_1020_, v___x_1020_, v___x_1069_, v___x_1080_);
lean_inc(v___y_1002_);
v___x_1082_ = l_Lean_Syntax_node2(v___y_1002_, v___x_1018_, v___x_1026_, v___x_1081_);
v___x_1083_ = l_Lean_Syntax_node2(v___y_1002_, v___y_999_, v___x_1017_, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_979_);
return v___x_1084_;
}
v___jp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; lean_object* v_fam_1090_; lean_object* v___x_1091_; lean_object* v_kindLit_1092_; lean_object* v___x_1093_; lean_object* v_nameLit_1094_; lean_object* v_quotContext_1095_; lean_object* v_currMacroScope_1096_; lean_object* v_ref_1097_; lean_object* v_facet_1098_; lean_object* v_facetLit_1099_; lean_object* v_id_1100_; lean_object* v_ref_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1087_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0));
v___x_1088_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1));
v___x_1089_ = 0;
v_fam_1090_ = l_Lean_mkCIdentFrom(v_tk_987_, v___x_1088_, v___x_1089_);
v___x_1091_ = l_Lean_TSyntax_getId(v_kind_989_);
lean_inc(v___x_1091_);
v_kindLit_1092_ = l_Lake_Name_quoteFrom(v_kind_989_, v___x_1091_, v___x_1089_);
v___x_1093_ = l_Lean_TSyntax_getId(v_name_991_);
lean_inc(v___x_1093_);
v_nameLit_1094_ = l_Lake_Name_quoteFrom(v_name_991_, v___x_1093_, v___x_1089_);
v_quotContext_1095_ = lean_ctor_get(v_a_978_, 1);
v_currMacroScope_1096_ = lean_ctor_get(v_a_978_, 2);
v_ref_1097_ = lean_ctor_get(v_a_978_, 5);
v_facet_1098_ = l_Lean_Name_append(v___x_1091_, v___x_1093_);
lean_inc(v_facet_1098_);
lean_inc(v_tk_987_);
v_facetLit_1099_ = l_Lake_Name_quoteFrom(v_tk_987_, v_facet_1098_, v___x_1089_);
v_id_1100_ = l_Lean_mkIdentFrom(v_tk_987_, v_facet_1098_, v___x_981_);
v_ref_1101_ = l_Lean_replaceRef(v_tk_987_, v_ref_1097_);
lean_dec(v_tk_987_);
v___x_1102_ = l_Lean_SourceInfo_fromRef(v_ref_1101_, v___x_1089_);
lean_dec(v_ref_1101_);
v___x_1103_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_1104_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70));
v___x_1105_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_1086_) == 1)
{
lean_object* v_val_1106_; lean_object* v___x_1107_; 
v_val_1106_ = lean_ctor_get(v___y_1086_, 0);
lean_inc(v_val_1106_);
lean_dec_ref(v___y_1086_);
v___x_1107_ = l_Array_mkArray1___redArg(v_val_1106_);
v___y_995_ = v_fam_1090_;
v___y_996_ = v___x_1105_;
v___y_997_ = v___x_1088_;
v___y_998_ = v_nameLit_1094_;
v___y_999_ = v___x_1103_;
v___y_1000_ = v_id_1100_;
v___y_1001_ = v_quotContext_1095_;
v___y_1002_ = v___x_1102_;
v___y_1003_ = v___x_1104_;
v___y_1004_ = v___x_1087_;
v___y_1005_ = v_kindLit_1092_;
v___y_1006_ = v_facetLit_1099_;
v___y_1007_ = v_currMacroScope_1096_;
v___y_1008_ = v___x_1107_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1108_; 
lean_dec(v___y_1086_);
v___x_1108_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72));
v___y_995_ = v_fam_1090_;
v___y_996_ = v___x_1105_;
v___y_997_ = v___x_1088_;
v___y_998_ = v_nameLit_1094_;
v___y_999_ = v___x_1103_;
v___y_1000_ = v_id_1100_;
v___y_1001_ = v_quotContext_1095_;
v___y_1002_ = v___x_1102_;
v___y_1003_ = v___x_1104_;
v___y_1004_ = v___x_1087_;
v___y_1005_ = v_kindLit_1092_;
v___y_1006_ = v_facetLit_1099_;
v___y_1007_ = v_currMacroScope_1096_;
v___y_1008_ = v___x_1108_;
goto v___jp_994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___boxed(lean_object* v_x_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1(v_x_1119_, v_a_1120_, v_a_1121_);
lean_dec_ref(v_a_1120_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1(lean_object* v_x_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = ((lean_object*)(l_Lake_packageDataDecl___closed__1));
lean_inc(v_x_1152_);
v___x_1156_ = l_Lean_Syntax_isOfKind(v_x_1152_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v_x_1152_);
v___x_1157_ = lean_box(1);
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v_a_1154_);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v_tk_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___y_1168_; lean_object* v___y_1169_; uint8_t v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1186_; lean_object* v___x_1196_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = l_Lean_Syntax_getArg(v_x_1152_, v___x_1159_);
v___x_1161_ = lean_unsigned_to_nat(1u);
v_tk_1162_ = l_Lean_Syntax_getArg(v_x_1152_, v___x_1161_);
v___x_1163_ = lean_unsigned_to_nat(2u);
v___x_1164_ = l_Lean_Syntax_getArg(v_x_1152_, v___x_1163_);
v___x_1165_ = lean_unsigned_to_nat(4u);
v___x_1166_ = l_Lean_Syntax_getArg(v_x_1152_, v___x_1165_);
lean_dec(v_x_1152_);
v___x_1196_ = l_Lean_Syntax_getOptional_x3f(v___x_1160_);
lean_dec(v___x_1160_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_box(0);
v___y_1186_ = v___x_1197_;
goto v___jp_1185_;
}
else
{
lean_object* v_val_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_val_1198_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1196_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_val_1198_);
lean_dec(v___x_1196_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_val_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
v___y_1186_ = v___x_1203_;
goto v___jp_1185_;
}
}
}
v___jp_1167_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1174_ = l_Array_append___redArg(v___y_1169_, v___y_1173_);
lean_dec_ref(v___y_1173_);
lean_inc(v___y_1172_);
v___x_1175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1175_, 0, v___y_1172_);
lean_ctor_set(v___x_1175_, 1, v___y_1171_);
lean_ctor_set(v___x_1175_, 2, v___x_1174_);
v___x_1176_ = l_Lean_SourceInfo_fromRef(v_tk_1162_, v___x_1156_);
v___x_1177_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0));
v___x_1178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lake_Package_keyword;
v___x_1180_ = l_Lean_mkIdentFrom(v_tk_1162_, v___x_1179_, v___y_1170_);
lean_dec(v_tk_1162_);
v___x_1181_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_1172_);
v___x_1182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___y_1172_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = l_Lean_Syntax_node6(v___y_1172_, v___y_1168_, v___x_1175_, v___x_1178_, v___x_1180_, v___x_1164_, v___x_1182_, v___x_1166_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v_a_1154_);
return v___x_1184_;
}
v___jp_1185_:
{
lean_object* v_ref_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_ref_1187_ = lean_ctor_get(v_a_1153_, 5);
v___x_1188_ = 0;
v___x_1189_ = l_Lean_SourceInfo_fromRef(v_ref_1187_, v___x_1188_);
v___x_1190_ = ((lean_object*)(l_Lake_facetDataDecl___closed__1));
v___x_1191_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_1192_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_1186_) == 1)
{
lean_object* v_val_1193_; lean_object* v___x_1194_; 
v_val_1193_ = lean_ctor_get(v___y_1186_, 0);
lean_inc(v_val_1193_);
lean_dec_ref(v___y_1186_);
v___x_1194_ = l_Array_mkArray1___redArg(v_val_1193_);
v___y_1168_ = v___x_1190_;
v___y_1169_ = v___x_1192_;
v___y_1170_ = v___x_1188_;
v___y_1171_ = v___x_1191_;
v___y_1172_ = v___x_1189_;
v___y_1173_ = v___x_1194_;
goto v___jp_1167_;
}
else
{
lean_object* v___x_1195_; 
lean_dec(v___y_1186_);
v___x_1195_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72));
v___y_1168_ = v___x_1190_;
v___y_1169_ = v___x_1192_;
v___y_1170_ = v___x_1188_;
v___y_1171_ = v___x_1191_;
v___y_1172_ = v___x_1189_;
v___y_1173_ = v___x_1195_;
goto v___jp_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___boxed(lean_object* v_x_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1(v_x_1206_, v_a_1207_, v_a_1208_);
lean_dec_ref(v_a_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1(lean_object* v_x_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lake_moduleDataDecl___closed__1));
lean_inc(v_x_1238_);
v___x_1242_ = l_Lean_Syntax_isOfKind(v_x_1238_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v_x_1238_);
v___x_1243_ = lean_box(1);
v___x_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v_a_1240_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v_tk_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; uint8_t v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1272_; lean_object* v___x_1282_; 
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1246_ = l_Lean_Syntax_getArg(v_x_1238_, v___x_1245_);
v___x_1247_ = lean_unsigned_to_nat(1u);
v_tk_1248_ = l_Lean_Syntax_getArg(v_x_1238_, v___x_1247_);
v___x_1249_ = lean_unsigned_to_nat(2u);
v___x_1250_ = l_Lean_Syntax_getArg(v_x_1238_, v___x_1249_);
v___x_1251_ = lean_unsigned_to_nat(4u);
v___x_1252_ = l_Lean_Syntax_getArg(v_x_1238_, v___x_1251_);
lean_dec(v_x_1238_);
v___x_1282_ = l_Lean_Syntax_getOptional_x3f(v___x_1246_);
lean_dec(v___x_1246_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_box(0);
v___y_1272_ = v___x_1283_;
goto v___jp_1271_;
}
else
{
lean_object* v_val_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_val_1284_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1282_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_val_1284_);
lean_dec(v___x_1282_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_val_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
v___y_1272_ = v___x_1289_;
goto v___jp_1271_;
}
}
}
v___jp_1253_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1260_ = l_Array_append___redArg(v___y_1256_, v___y_1259_);
lean_dec_ref(v___y_1259_);
lean_inc(v___y_1257_);
v___x_1261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1261_, 0, v___y_1257_);
lean_ctor_set(v___x_1261_, 1, v___y_1254_);
lean_ctor_set(v___x_1261_, 2, v___x_1260_);
v___x_1262_ = l_Lean_SourceInfo_fromRef(v_tk_1248_, v___x_1242_);
v___x_1263_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0));
v___x_1264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = l_Lake_Module_keyword;
v___x_1266_ = l_Lean_mkIdentFrom(v_tk_1248_, v___x_1265_, v___y_1258_);
lean_dec(v_tk_1248_);
v___x_1267_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_1257_);
v___x_1268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___y_1257_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = l_Lean_Syntax_node6(v___y_1257_, v___y_1255_, v___x_1261_, v___x_1264_, v___x_1266_, v___x_1250_, v___x_1268_, v___x_1252_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v_a_1240_);
return v___x_1270_;
}
v___jp_1271_:
{
lean_object* v_ref_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_ref_1273_ = lean_ctor_get(v_a_1239_, 5);
v___x_1274_ = 0;
v___x_1275_ = l_Lean_SourceInfo_fromRef(v_ref_1273_, v___x_1274_);
v___x_1276_ = ((lean_object*)(l_Lake_facetDataDecl___closed__1));
v___x_1277_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_1278_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_1272_) == 1)
{
lean_object* v_val_1279_; lean_object* v___x_1280_; 
v_val_1279_ = lean_ctor_get(v___y_1272_, 0);
lean_inc(v_val_1279_);
lean_dec_ref(v___y_1272_);
v___x_1280_ = l_Array_mkArray1___redArg(v_val_1279_);
v___y_1254_ = v___x_1277_;
v___y_1255_ = v___x_1276_;
v___y_1256_ = v___x_1278_;
v___y_1257_ = v___x_1275_;
v___y_1258_ = v___x_1274_;
v___y_1259_ = v___x_1280_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1281_; 
lean_dec(v___y_1272_);
v___x_1281_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72));
v___y_1254_ = v___x_1277_;
v___y_1255_ = v___x_1276_;
v___y_1256_ = v___x_1278_;
v___y_1257_ = v___x_1275_;
v___y_1258_ = v___x_1274_;
v___y_1259_ = v___x_1281_;
goto v___jp_1253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1___boxed(lean_object* v_x_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1(v_x_1292_, v_a_1293_, v_a_1294_);
lean_dec_ref(v_a_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1(lean_object* v_x_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lake_libraryDataDecl___closed__1));
lean_inc(v_x_1327_);
v___x_1331_ = l_Lean_Syntax_isOfKind(v_x_1327_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec(v_x_1327_);
v___x_1332_ = lean_box(1);
v___x_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v_a_1329_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v_tk_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; uint8_t v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1361_; lean_object* v___x_1371_; 
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = l_Lean_Syntax_getArg(v_x_1327_, v___x_1334_);
v___x_1336_ = lean_unsigned_to_nat(1u);
v_tk_1337_ = l_Lean_Syntax_getArg(v_x_1327_, v___x_1336_);
v___x_1338_ = lean_unsigned_to_nat(2u);
v___x_1339_ = l_Lean_Syntax_getArg(v_x_1327_, v___x_1338_);
v___x_1340_ = lean_unsigned_to_nat(4u);
v___x_1341_ = l_Lean_Syntax_getArg(v_x_1327_, v___x_1340_);
lean_dec(v_x_1327_);
v___x_1371_ = l_Lean_Syntax_getOptional_x3f(v___x_1335_);
lean_dec(v___x_1335_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_box(0);
v___y_1361_ = v___x_1372_;
goto v___jp_1360_;
}
else
{
lean_object* v_val_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_val_1373_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1371_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_val_1373_);
lean_dec(v___x_1371_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_val_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
v___y_1361_ = v___x_1378_;
goto v___jp_1360_;
}
}
}
v___jp_1342_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1349_ = l_Array_append___redArg(v___y_1343_, v___y_1348_);
lean_dec_ref(v___y_1348_);
lean_inc(v___y_1344_);
v___x_1350_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1350_, 0, v___y_1344_);
lean_ctor_set(v___x_1350_, 1, v___y_1346_);
lean_ctor_set(v___x_1350_, 2, v___x_1349_);
v___x_1351_ = l_Lean_SourceInfo_fromRef(v_tk_1337_, v___x_1331_);
v___x_1352_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0));
v___x_1353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1));
v___x_1355_ = l_Lean_mkIdentFrom(v_tk_1337_, v___x_1354_, v___y_1347_);
lean_dec(v_tk_1337_);
v___x_1356_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_1344_);
v___x_1357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___y_1344_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_Syntax_node6(v___y_1344_, v___y_1345_, v___x_1350_, v___x_1353_, v___x_1355_, v___x_1339_, v___x_1357_, v___x_1341_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v_a_1329_);
return v___x_1359_;
}
v___jp_1360_:
{
lean_object* v_ref_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_ref_1362_ = lean_ctor_get(v_a_1328_, 5);
v___x_1363_ = 0;
v___x_1364_ = l_Lean_SourceInfo_fromRef(v_ref_1362_, v___x_1363_);
v___x_1365_ = ((lean_object*)(l_Lake_facetDataDecl___closed__1));
v___x_1366_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_1367_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_1361_) == 1)
{
lean_object* v_val_1368_; lean_object* v___x_1369_; 
v_val_1368_ = lean_ctor_get(v___y_1361_, 0);
lean_inc(v_val_1368_);
lean_dec_ref(v___y_1361_);
v___x_1369_ = l_Array_mkArray1___redArg(v_val_1368_);
v___y_1343_ = v___x_1367_;
v___y_1344_ = v___x_1364_;
v___y_1345_ = v___x_1365_;
v___y_1346_ = v___x_1366_;
v___y_1347_ = v___x_1363_;
v___y_1348_ = v___x_1369_;
goto v___jp_1342_;
}
else
{
lean_object* v___x_1370_; 
lean_dec(v___y_1361_);
v___x_1370_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72));
v___y_1343_ = v___x_1367_;
v___y_1344_ = v___x_1364_;
v___y_1345_ = v___x_1365_;
v___y_1346_ = v___x_1366_;
v___y_1347_ = v___x_1363_;
v___y_1348_ = v___x_1370_;
goto v___jp_1342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___boxed(lean_object* v_x_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1(v_x_1381_, v_a_1382_, v_a_1383_);
lean_dec_ref(v_a_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1(lean_object* v_x_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_Lake_customDataDecl___closed__1));
lean_inc(v_x_1433_);
v___x_1437_ = l_Lean_Syntax_isOfKind(v_x_1433_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec(v_x_1433_);
v___x_1438_ = lean_box(1);
v___x_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
lean_ctor_set(v___x_1439_, 1, v_a_1435_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v_tk_1443_; lean_object* v___x_1444_; lean_object* v_pkg_1445_; lean_object* v___x_1446_; lean_object* v_tgt_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1492_; lean_object* v___x_1513_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = l_Lean_Syntax_getArg(v_x_1433_, v___x_1440_);
v___x_1442_ = lean_unsigned_to_nat(1u);
v_tk_1443_ = l_Lean_Syntax_getArg(v_x_1433_, v___x_1442_);
v___x_1444_ = lean_unsigned_to_nat(2u);
v_pkg_1445_ = l_Lean_Syntax_getArg(v_x_1433_, v___x_1444_);
v___x_1446_ = lean_unsigned_to_nat(3u);
v_tgt_1447_ = l_Lean_Syntax_getArg(v_x_1433_, v___x_1446_);
v___x_1448_ = lean_unsigned_to_nat(5u);
v___x_1449_ = l_Lean_Syntax_getArg(v_x_1433_, v___x_1448_);
lean_dec(v_x_1433_);
v___x_1513_ = l_Lean_Syntax_getOptional_x3f(v___x_1441_);
lean_dec(v___x_1441_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_box(0);
v___y_1492_ = v___x_1514_;
goto v___jp_1491_;
}
else
{
lean_object* v_val_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
v_val_1515_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1513_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_val_1515_);
lean_dec(v___x_1513_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_val_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
v___y_1492_ = v___x_1520_;
goto v___jp_1491_;
}
}
}
v___jp_1450_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1462_ = l_Array_append___redArg(v___y_1456_, v___y_1461_);
lean_dec_ref(v___y_1461_);
lean_inc(v___y_1459_);
lean_inc(v___y_1454_);
v___x_1463_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1463_, 0, v___y_1454_);
lean_ctor_set(v___x_1463_, 1, v___y_1459_);
lean_ctor_set(v___x_1463_, 2, v___x_1462_);
v___x_1464_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0));
lean_inc(v___y_1454_);
v___x_1465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___y_1454_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1));
lean_inc(v___y_1454_);
v___x_1467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1454_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1));
v___x_1469_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6));
v___x_1470_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20));
lean_inc(v___y_1454_);
v___x_1471_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1454_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22));
v___x_1473_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
v___x_1474_ = lean_box(0);
lean_inc(v___y_1458_);
lean_inc(v___y_1460_);
v___x_1475_ = l_Lean_addMacroScope(v___y_1460_, v___x_1474_, v___y_1458_);
v___x_1476_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3));
lean_inc(v___y_1454_);
v___x_1477_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1477_, 0, v___y_1454_);
lean_ctor_set(v___x_1477_, 1, v___x_1473_);
lean_ctor_set(v___x_1477_, 2, v___x_1475_);
lean_ctor_set(v___x_1477_, 3, v___x_1476_);
lean_inc(v___y_1454_);
v___x_1478_ = l_Lean_Syntax_node1(v___y_1454_, v___x_1472_, v___x_1477_);
lean_inc(v___y_1454_);
v___x_1479_ = l_Lean_Syntax_node2(v___y_1454_, v___x_1469_, v___x_1471_, v___x_1478_);
v___x_1480_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36));
lean_inc(v___y_1454_);
v___x_1481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___y_1454_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
lean_inc(v___y_1459_);
lean_inc(v___y_1454_);
v___x_1482_ = l_Lean_Syntax_node1(v___y_1454_, v___y_1459_, v___y_1453_);
lean_inc(v___y_1454_);
v___x_1483_ = l_Lean_Syntax_node3(v___y_1454_, v___y_1459_, v___y_1452_, v___x_1481_, v___x_1482_);
v___x_1484_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28));
lean_inc(v___y_1454_);
v___x_1485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___y_1454_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
lean_inc(v___y_1454_);
v___x_1486_ = l_Lean_Syntax_node3(v___y_1454_, v___x_1468_, v___x_1479_, v___x_1483_, v___x_1485_);
v___x_1487_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2));
lean_inc(v___y_1454_);
v___x_1488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___y_1454_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_Syntax_node8(v___y_1454_, v___y_1455_, v___x_1463_, v___x_1465_, v___y_1451_, v___x_1467_, v___y_1457_, v___x_1486_, v___x_1488_, v___x_1449_);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
lean_ctor_set(v___x_1490_, 1, v_a_1435_);
return v___x_1490_;
}
v___jp_1491_:
{
lean_object* v_quotContext_1493_; lean_object* v_currMacroScope_1494_; lean_object* v_ref_1495_; lean_object* v_ref_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_quotContext_1493_ = lean_ctor_get(v_a_1434_, 1);
v_currMacroScope_1494_ = lean_ctor_get(v_a_1434_, 2);
v_ref_1495_ = lean_ctor_get(v_a_1434_, 5);
v_ref_1496_ = l_Lean_replaceRef(v_tk_1443_, v_ref_1495_);
lean_dec(v_tk_1443_);
v___x_1497_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5));
v___x_1498_ = 0;
v___x_1499_ = l_Lean_mkCIdentFrom(v_ref_1496_, v___x_1497_, v___x_1498_);
v___x_1500_ = l_Lean_TSyntax_getId(v_pkg_1445_);
v___x_1501_ = l_Lean_TSyntax_getId(v_tgt_1447_);
lean_inc(v___x_1501_);
lean_inc(v___x_1500_);
v___x_1502_ = l_Lean_Name_append(v___x_1500_, v___x_1501_);
v___x_1503_ = l_Lean_mkIdentFrom(v_tgt_1447_, v___x_1502_, v___x_1498_);
lean_dec(v_tgt_1447_);
v___x_1504_ = l_Lake_Name_quoteFrom(v_pkg_1445_, v___x_1500_, v___x_1498_);
lean_inc(v___x_1504_);
v___x_1505_ = l_Lake_Name_quoteFrom(v___x_1504_, v___x_1501_, v___x_1498_);
v___x_1506_ = l_Lean_SourceInfo_fromRef(v_ref_1496_, v___x_1498_);
lean_dec(v_ref_1496_);
v___x_1507_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70));
v___x_1508_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68));
v___x_1509_ = lean_obj_once(&l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71, &l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once, _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
if (lean_obj_tag(v___y_1492_) == 1)
{
lean_object* v_val_1510_; lean_object* v___x_1511_; 
v_val_1510_ = lean_ctor_get(v___y_1492_, 0);
lean_inc(v_val_1510_);
lean_dec_ref(v___y_1492_);
v___x_1511_ = l_Array_mkArray1___redArg(v_val_1510_);
v___y_1451_ = v___x_1503_;
v___y_1452_ = v___x_1504_;
v___y_1453_ = v___x_1505_;
v___y_1454_ = v___x_1506_;
v___y_1455_ = v___x_1507_;
v___y_1456_ = v___x_1509_;
v___y_1457_ = v___x_1499_;
v___y_1458_ = v_currMacroScope_1494_;
v___y_1459_ = v___x_1508_;
v___y_1460_ = v_quotContext_1493_;
v___y_1461_ = v___x_1511_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1512_; 
lean_dec(v___y_1492_);
v___x_1512_ = ((lean_object*)(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72));
v___y_1451_ = v___x_1503_;
v___y_1452_ = v___x_1504_;
v___y_1453_ = v___x_1505_;
v___y_1454_ = v___x_1506_;
v___y_1455_ = v___x_1507_;
v___y_1456_ = v___x_1509_;
v___y_1457_ = v___x_1499_;
v___y_1458_ = v_currMacroScope_1494_;
v___y_1459_ = v___x_1508_;
v___y_1460_ = v_quotContext_1493_;
v___y_1461_ = v___x_1512_;
goto v___jp_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___boxed(lean_object* v_x_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1(v_x_1523_, v_a_1524_, v_a_1525_);
lean_dec_ref(v_a_1524_);
return v_res_1526_;
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
