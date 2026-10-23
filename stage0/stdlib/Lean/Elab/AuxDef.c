// Lean compiler output
// Module: Lean.Elab.AuxDef
// Imports: public import Lean.Elab.Command
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
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_DeclNameGenerator_ofPrefix(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__0 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__1 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__2 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__3 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__3_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__4 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__5 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__6 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__7 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__7_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__8 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__9 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__9_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__10 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__10_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__11 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__8_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__11_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__12 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__13 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__14 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__14_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__15 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__13_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__15_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__16 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__16_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__17 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__8_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__17_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__18 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__6_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__12_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__18_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__19 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "visibility"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__20 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 205, 25, 140, 55, 50, 241, 254)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__21 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__21_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__22 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__6_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__19_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__22_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__23 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__3_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__24 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__6_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__23_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__24_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__25 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__25_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__26 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__26_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__27 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__27_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__28 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__29_value_aux_0),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__13_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__29_value_aux_1),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__29_value_aux_2),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__28_value),LEAN_SCALAR_PTR_LITERAL(36, 143, 235, 174, 172, 186, 143, 206)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__29 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__29_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__30 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__27_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__30_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__31 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__6_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__25_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__31_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__32 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__32_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__33 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__33_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__33_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__34 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__6_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__32_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__34_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__35 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__35_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__36 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__36_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__37 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__37_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__38 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__6_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__35_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__38_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__39 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__39_value;
static const lean_string_object l_Lean_Elab_Command_aux__def___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__40 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__40_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__41 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__6_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__39_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__41_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__42 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__6_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__42_value),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__38_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__43 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__43_value;
static const lean_ctor_object l_Lean_Elab_Command_aux__def___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_aux__def___closed__4_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__43_value)}};
static const lean_object* l_Lean_Elab_Command_aux__def___closed__44 = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__44_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Command_aux__def = (const lean_object*)&l_Lean_Elab_Command_aux__def___closed__44_value;
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_mkAuxDefName_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_mkAuxDefName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_aux"};
static const lean_object* l_Lean_Elab_Command_mkAuxDefName___closed__0 = (const lean_object*)&l_Lean_Elab_Command_mkAuxDefName___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_mkAuxDefName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkAuxDefName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 43, 245, 0, 252, 151, 26, 151)}};
static const lean_object* l_Lean_Elab_Command_mkAuxDefName___closed__1 = (const lean_object*)&l_Lean_Elab_Command_mkAuxDefName___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_mkAuxDefName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_mkAuxDefName___closed__2 = (const lean_object*)&l_Lean_Elab_Command_mkAuxDefName___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_mkAuxDefName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkAuxDefName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Elab_Command_mkAuxDefName___closed__3 = (const lean_object*)&l_Lean_Elab_Command_mkAuxDefName___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkAuxDefName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkAuxDefName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__8_value;
static const lean_array_object l_Lean_Elab_Command_elabAuxDef___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__9_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Command_elabAuxDef___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Command_elabAuxDef___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabAuxDef___closed__14;
static const lean_ctor_object l_Lean_Elab_Command_elabAuxDef___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAuxDef___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__13_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAuxDef___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAuxDef___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__9_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAuxDef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAuxDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabAuxDef"};
static const lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 19, 161, 49, 27, 65, 68, 32)}};
static const lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(33) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(14) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__4_value),((lean_object*)(((size_t)(14) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0___redArg(lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; lean_object* v_env_110_; lean_object* v___x_111_; lean_object* v_mainModule_112_; lean_object* v___x_113_; 
v___x_109_ = lean_st_ref_get(v___y_107_);
v_env_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc_ref(v_env_110_);
lean_dec(v___x_109_);
v___x_111_ = l_Lean_Environment_header(v_env_110_);
lean_dec_ref(v_env_110_);
v_mainModule_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_mainModule_112_);
lean_dec_ref(v___x_111_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v_mainModule_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0___redArg___boxed(lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0___redArg(v___y_114_);
lean_dec(v___y_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0(lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0___redArg(v___y_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0___boxed(lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0(v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_mkAuxDefName_spec__1(lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
if (lean_obj_tag(v_a_125_) == 0)
{
lean_object* v___x_127_; 
v___x_127_ = l_List_reverse___redArg(v_a_126_);
return v___x_127_;
}
else
{
lean_object* v_head_128_; lean_object* v_tail_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_139_; 
v_head_128_ = lean_ctor_get(v_a_125_, 0);
v_tail_129_ = lean_ctor_get(v_a_125_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_a_125_);
if (v_isSharedCheck_139_ == 0)
{
v___x_131_ = v_a_125_;
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_tail_129_);
lean_inc(v_head_128_);
lean_dec(v_a_125_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_133_ = 0;
v___x_134_ = l_Lean_Name_toString(v_head_128_, v___x_133_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v_a_126_);
lean_ctor_set(v___x_131_, 0, v___x_134_);
v___x_136_ = v___x_131_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_a_126_);
v___x_136_ = v_reuseFailAlloc_138_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
v_a_125_ = v_tail_129_;
v_a_126_ = v___x_136_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkAuxDefName(lean_object* v_suggestion_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_150_; lean_object* v_a_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_150_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0___redArg(v_a_148_);
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref(v___x_150_);
v___x_152_ = ((lean_object*)(l_Lean_Elab_Command_mkAuxDefName___closed__1));
v___x_153_ = l_Lean_Name_append(v___x_152_, v_a_151_);
v___x_154_ = ((lean_object*)(l_Lean_Elab_Command_mkAuxDefName___closed__2));
v___x_155_ = ((lean_object*)(l_Lean_Elab_Command_mkAuxDefName___closed__3));
v___x_156_ = l_Lean_Name_append(v___x_153_, v___x_155_);
v___x_157_ = l_Lean_Name_append(v___x_156_, v_suggestion_146_);
v___x_158_ = l_Lean_Name_components(v___x_157_);
v___x_159_ = lean_box(0);
v___x_160_ = l_List_mapTR_loop___at___00Lean_Elab_Command_mkAuxDefName_spec__1(v___x_158_, v___x_159_);
v___x_161_ = l_String_intercalate(v___x_154_, v___x_160_);
v___x_162_ = l_Lean_Elab_Command_getScope___redArg(v_a_148_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_181_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_181_ == 0)
{
v___x_165_ = v___x_162_;
v_isShared_166_ = v_isSharedCheck_181_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_181_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_currNamespace_167_; lean_object* v___x_168_; lean_object* v_env_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_fst_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v_currNamespace_167_ = lean_ctor_get(v_a_163_, 2);
lean_inc_n(v_currNamespace_167_, 2);
lean_dec(v_a_163_);
v___x_168_ = lean_st_ref_get(v_a_148_);
v_env_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc_ref(v_env_169_);
lean_dec(v___x_168_);
v___x_170_ = 1;
v___x_171_ = l_Lean_Environment_setExporting(v_env_169_, v___x_170_);
v___x_172_ = l_Lean_DeclNameGenerator_ofPrefix(v_currNamespace_167_);
v___x_173_ = lean_box(0);
v___x_174_ = l_Lean_Name_str___override(v___x_173_, v___x_161_);
v___x_175_ = l_Lean_DeclNameGenerator_mkUniqueName(v___x_171_, v___x_172_, v___x_174_);
v_fst_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_fst_176_);
lean_dec_ref(v___x_175_);
v___x_177_ = l_Lean_Name_replacePrefix(v_fst_176_, v_currNamespace_167_, v___x_173_);
lean_dec(v_currNamespace_167_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_177_);
v___x_179_ = v___x_165_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref(v___x_161_);
v_a_182_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_162_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_162_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkAuxDefName___boxed(lean_object* v_suggestion_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Elab_Command_mkAuxDefName(v_suggestion_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
return v_res_194_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_box(0);
v___x_196_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg(){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0);
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___boxed(lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0(lean_object* v_00_u03b1_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___boxed(lean_object* v_00_u03b1_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0(v_00_u03b1_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__1(size_t v_sz_213_, size_t v_i_214_, lean_object* v_bs_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_usize_dec_lt(v_i_214_, v_sz_213_);
if (v___x_216_ == 0)
{
return v_bs_215_;
}
else
{
lean_object* v_v_217_; lean_object* v___x_218_; lean_object* v_bs_x27_219_; lean_object* v___x_220_; lean_object* v___x_221_; size_t v___x_222_; size_t v___x_223_; lean_object* v___x_224_; 
v_v_217_ = lean_array_uget(v_bs_215_, v_i_214_);
v___x_218_ = lean_unsigned_to_nat(0u);
v_bs_x27_219_ = lean_array_uset(v_bs_215_, v_i_214_, v___x_218_);
v___x_220_ = l_Lean_TSyntax_getId(v_v_217_);
lean_dec(v_v_217_);
v___x_221_ = l_Lean_Name_eraseMacroScopes(v___x_220_);
lean_dec(v___x_220_);
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_add(v_i_214_, v___x_222_);
v___x_224_ = lean_array_uset(v_bs_x27_219_, v_i_214_, v___x_221_);
v_i_214_ = v___x_223_;
v_bs_215_ = v___x_224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__1___boxed(lean_object* v_sz_226_, lean_object* v_i_227_, lean_object* v_bs_228_){
_start:
{
size_t v_sz_boxed_229_; size_t v_i_boxed_230_; lean_object* v_res_231_; 
v_sz_boxed_229_ = lean_unbox_usize(v_sz_226_);
lean_dec(v_sz_226_);
v_i_boxed_230_ = lean_unbox_usize(v_i_227_);
lean_dec(v_i_227_);
v_res_231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__1(v_sz_boxed_229_, v_i_boxed_230_, v_bs_228_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__2(lean_object* v_as_232_, size_t v_i_233_, size_t v_stop_234_, lean_object* v_b_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = lean_usize_dec_eq(v_i_233_, v_stop_234_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; size_t v___x_239_; size_t v___x_240_; 
v___x_237_ = lean_array_uget_borrowed(v_as_232_, v_i_233_);
lean_inc(v___x_237_);
v___x_238_ = l_Lean_Name_append(v_b_235_, v___x_237_);
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_add(v_i_233_, v___x_239_);
v_i_233_ = v___x_240_;
v_b_235_ = v___x_238_;
goto _start;
}
else
{
return v_b_235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__2___boxed(lean_object* v_as_242_, lean_object* v_i_243_, lean_object* v_stop_244_, lean_object* v_b_245_){
_start:
{
size_t v_i_boxed_246_; size_t v_stop_boxed_247_; lean_object* v_res_248_; 
v_i_boxed_246_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_stop_boxed_247_ = lean_unbox_usize(v_stop_244_);
lean_dec(v_stop_244_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__2(v_as_242_, v_i_boxed_246_, v_stop_boxed_247_, v_b_245_);
lean_dec_ref(v_as_242_);
return v_res_248_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAuxDef___closed__14(void){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Array_mkArray0___redArg();
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAuxDef(lean_object* v_x_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; 
v___x_275_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__0));
v___x_276_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__2));
v___x_277_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__4));
lean_inc(v_x_271_);
v___x_278_ = l_Lean_Syntax_isOfKind(v_x_271_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_337_; 
lean_dec(v_x_271_);
v___x_337_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_337_;
}
else
{
lean_object* v___x_338_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_426_; lean_object* v_attrs_x3f_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v_doc_x3f_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_463_ = l_Lean_Syntax_getArg(v_x_271_, v___x_338_);
v___x_464_ = l_Lean_Syntax_isNone(v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_463_);
v___x_466_ = l_Lean_Syntax_matchesNull(v___x_463_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
lean_dec(v___x_463_);
lean_dec(v_x_271_);
v___x_467_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_467_;
}
else
{
lean_object* v_doc_x3f_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_doc_x3f_468_ = l_Lean_Syntax_getArg(v___x_463_, v___x_338_);
lean_dec(v___x_463_);
v___x_469_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__15));
lean_inc(v_doc_x3f_468_);
v___x_470_ = l_Lean_Syntax_isOfKind(v_doc_x3f_468_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
lean_dec(v_doc_x3f_468_);
lean_dec(v_x_271_);
v___x_471_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_471_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v_doc_x3f_468_);
v_doc_x3f_449_ = v___x_472_;
v___y_450_ = v_a_272_;
v___y_451_ = v_a_273_;
goto v___jp_448_;
}
}
}
else
{
lean_object* v___x_473_; 
lean_dec(v___x_463_);
v___x_473_ = lean_box(0);
v_doc_x3f_449_ = v___x_473_;
v___y_450_ = v_a_272_;
v___y_451_ = v_a_273_;
goto v___jp_448_;
}
v___jp_339_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_inc_ref(v___y_349_);
v___x_355_ = l_Array_append___redArg(v___y_349_, v___y_354_);
lean_dec_ref(v___y_354_);
lean_inc(v___y_348_);
lean_inc(v___y_344_);
v___x_356_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_356_, 0, v___y_344_);
lean_ctor_set(v___x_356_, 1, v___y_348_);
lean_ctor_set(v___x_356_, 2, v___x_355_);
if (lean_obj_tag(v___y_346_) == 1)
{
lean_object* v_val_357_; lean_object* v___x_358_; 
v_val_357_ = lean_ctor_get(v___y_346_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v___y_346_, 1);
v___x_358_ = l_Array_mkArray1___redArg(v_val_357_);
v___y_280_ = v___y_340_;
v___y_281_ = v___y_341_;
v___y_282_ = v___y_342_;
v___y_283_ = v___y_343_;
v___y_284_ = v___y_344_;
v___y_285_ = v___y_345_;
v___y_286_ = v___y_347_;
v___y_287_ = v___y_348_;
v___y_288_ = v___y_349_;
v___y_289_ = v___x_356_;
v___y_290_ = v___y_350_;
v___y_291_ = v___y_351_;
v___y_292_ = v___y_352_;
v___y_293_ = v___y_353_;
v___y_294_ = v___x_358_;
goto v___jp_279_;
}
else
{
lean_object* v___x_359_; 
lean_dec(v___y_346_);
v___x_359_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__9));
v___y_280_ = v___y_340_;
v___y_281_ = v___y_341_;
v___y_282_ = v___y_342_;
v___y_283_ = v___y_343_;
v___y_284_ = v___y_344_;
v___y_285_ = v___y_345_;
v___y_286_ = v___y_347_;
v___y_287_ = v___y_348_;
v___y_288_ = v___y_349_;
v___y_289_ = v___x_356_;
v___y_290_ = v___y_350_;
v___y_291_ = v___y_351_;
v___y_292_ = v___y_352_;
v___y_293_ = v___y_353_;
v___y_294_ = v___x_359_;
goto v___jp_279_;
}
}
v___jp_360_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_372_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__10));
lean_inc_ref_n(v___y_371_, 2);
v___x_373_ = l_Lean_Name_mkStr4(v___x_275_, v___y_371_, v___x_276_, v___x_372_);
v___x_374_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__11));
v___x_375_ = l_Lean_Name_mkStr4(v___x_275_, v___y_371_, v___x_276_, v___x_374_);
v___x_376_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__13));
v___x_377_ = lean_obj_once(&l_Lean_Elab_Command_elabAuxDef___closed__14, &l_Lean_Elab_Command_elabAuxDef___closed__14_once, _init_l_Lean_Elab_Command_elabAuxDef___closed__14);
if (lean_obj_tag(v___y_367_) == 1)
{
lean_object* v_val_378_; lean_object* v___x_379_; 
v_val_378_ = lean_ctor_get(v___y_367_, 0);
lean_inc(v_val_378_);
lean_dec_ref_known(v___y_367_, 1);
v___x_379_ = l_Array_mkArray1___redArg(v_val_378_);
v___y_340_ = v___y_361_;
v___y_341_ = v___y_363_;
v___y_342_ = v___y_366_;
v___y_343_ = v___y_365_;
v___y_344_ = v___y_369_;
v___y_345_ = v___y_368_;
v___y_346_ = v___y_370_;
v___y_347_ = v___x_375_;
v___y_348_ = v___x_376_;
v___y_349_ = v___x_377_;
v___y_350_ = v___y_362_;
v___y_351_ = v___y_364_;
v___y_352_ = v___x_373_;
v___y_353_ = v___y_371_;
v___y_354_ = v___x_379_;
goto v___jp_339_;
}
else
{
lean_object* v___x_380_; 
lean_dec(v___y_367_);
v___x_380_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__9));
v___y_340_ = v___y_361_;
v___y_341_ = v___y_363_;
v___y_342_ = v___y_366_;
v___y_343_ = v___y_365_;
v___y_344_ = v___y_369_;
v___y_345_ = v___y_368_;
v___y_346_ = v___y_370_;
v___y_347_ = v___x_375_;
v___y_348_ = v___x_376_;
v___y_349_ = v___x_377_;
v___y_350_ = v___y_362_;
v___y_351_ = v___y_364_;
v___y_352_ = v___x_373_;
v___y_353_ = v___y_371_;
v___y_354_ = v___x_380_;
goto v___jp_339_;
}
}
v___jp_381_:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Elab_Command_mkAuxDefName(v___y_391_, v___y_382_, v___y_386_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_394_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v___x_392_, 1);
v___x_394_ = l_Lean_Elab_Command_getRef___redArg(v___y_382_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_396_ = 0;
v___x_397_ = l_Lean_SourceInfo_fromRef(v_a_395_, v___x_396_);
lean_dec(v_a_395_);
v___x_398_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_382_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_quotContext_x3f_399_; 
lean_dec_ref_known(v___x_398_, 1);
v_quotContext_x3f_399_ = lean_ctor_get(v___y_382_, 5);
if (lean_obj_tag(v_quotContext_x3f_399_) == 0)
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkAuxDefName_spec__0___redArg(v___y_386_);
lean_dec_ref(v___x_400_);
v___y_361_ = v___y_382_;
v___y_362_ = v___y_384_;
v___y_363_ = v___y_383_;
v___y_364_ = v_a_393_;
v___y_365_ = v___y_385_;
v___y_366_ = v___y_386_;
v___y_367_ = v___y_387_;
v___y_368_ = v___y_388_;
v___y_369_ = v___x_397_;
v___y_370_ = v___y_389_;
v___y_371_ = v___y_390_;
goto v___jp_360_;
}
else
{
v___y_361_ = v___y_382_;
v___y_362_ = v___y_384_;
v___y_363_ = v___y_383_;
v___y_364_ = v_a_393_;
v___y_365_ = v___y_385_;
v___y_366_ = v___y_386_;
v___y_367_ = v___y_387_;
v___y_368_ = v___y_388_;
v___y_369_ = v___x_397_;
v___y_370_ = v___y_389_;
v___y_371_ = v___y_390_;
goto v___jp_360_;
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v___x_397_);
lean_dec(v_a_393_);
lean_dec(v___y_389_);
lean_dec(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec(v___y_383_);
v_a_401_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_398_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_398_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec(v_a_393_);
lean_dec(v___y_389_);
lean_dec(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec(v___y_383_);
v_a_409_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_394_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_394_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v___y_389_);
lean_dec(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec(v___y_383_);
v_a_417_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_392_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_392_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
v___jp_425_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_suggestion_438_; lean_object* v___x_439_; lean_object* v___x_440_; size_t v_sz_441_; size_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_430_ = lean_unsigned_to_nat(2u);
v___x_431_ = l_Lean_Syntax_getArg(v_x_271_, v___x_430_);
v___x_432_ = lean_unsigned_to_nat(4u);
v___x_433_ = l_Lean_Syntax_getArg(v_x_271_, v___x_432_);
v___x_434_ = lean_unsigned_to_nat(6u);
v___x_435_ = l_Lean_Syntax_getArg(v_x_271_, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(8u);
v___x_437_ = l_Lean_Syntax_getArg(v_x_271_, v___x_436_);
lean_dec(v_x_271_);
v_suggestion_438_ = l_Lean_Syntax_getArgs(v___x_433_);
lean_dec(v___x_433_);
v___x_439_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__13));
v___x_440_ = lean_box(0);
v_sz_441_ = lean_array_size(v_suggestion_438_);
v___x_442_ = ((size_t)0ULL);
lean_inc_ref(v_suggestion_438_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__1(v_sz_441_, v___x_442_, v_suggestion_438_);
v___x_444_ = lean_array_get_size(v___x_443_);
v___x_445_ = lean_nat_dec_lt(v___x_338_, v___x_444_);
if (v___x_445_ == 0)
{
lean_dec_ref(v___x_443_);
v___y_382_ = v___y_428_;
v___y_383_ = v___x_437_;
v___y_384_ = v___x_431_;
v___y_385_ = v_suggestion_438_;
v___y_386_ = v___y_429_;
v___y_387_ = v___y_426_;
v___y_388_ = v___x_435_;
v___y_389_ = v_attrs_x3f_427_;
v___y_390_ = v___x_439_;
v___y_391_ = v___x_440_;
goto v___jp_381_;
}
else
{
size_t v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_usize_of_nat(v___x_444_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__2(v___x_443_, v___x_442_, v___x_446_, v___x_440_);
lean_dec_ref(v___x_443_);
v___y_382_ = v___y_428_;
v___y_383_ = v___x_437_;
v___y_384_ = v___x_431_;
v___y_385_ = v_suggestion_438_;
v___y_386_ = v___y_429_;
v___y_387_ = v___y_426_;
v___y_388_ = v___x_435_;
v___y_389_ = v_attrs_x3f_427_;
v___y_390_ = v___x_439_;
v___y_391_ = v___x_447_;
goto v___jp_381_;
}
}
v___jp_448_:
{
lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = l_Lean_Syntax_getArg(v_x_271_, v___x_452_);
v___x_454_ = l_Lean_Syntax_isNone(v___x_453_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
lean_inc(v___x_453_);
v___x_455_ = l_Lean_Syntax_matchesNull(v___x_453_, v___x_452_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
lean_dec(v___x_453_);
lean_dec(v_doc_x3f_449_);
lean_dec(v_x_271_);
v___x_456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_456_;
}
else
{
lean_object* v_attrs_x3f_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_attrs_x3f_457_ = l_Lean_Syntax_getArg(v___x_453_, v___x_338_);
lean_dec(v___x_453_);
v___x_458_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__16));
lean_inc(v_attrs_x3f_457_);
v___x_459_ = l_Lean_Syntax_isOfKind(v_attrs_x3f_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v_attrs_x3f_457_);
lean_dec(v_doc_x3f_449_);
lean_dec(v_x_271_);
v___x_460_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_460_;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_attrs_x3f_457_);
v___y_426_ = v_doc_x3f_449_;
v_attrs_x3f_427_ = v___x_461_;
v___y_428_ = v___y_450_;
v___y_429_ = v___y_451_;
goto v___jp_425_;
}
}
}
else
{
lean_object* v___x_462_; 
lean_dec(v___x_453_);
v___x_462_ = lean_box(0);
v___y_426_ = v_doc_x3f_449_;
v_attrs_x3f_427_ = v___x_462_;
v___y_428_ = v___y_450_;
v___y_429_ = v___y_451_;
goto v___jp_425_;
}
}
}
v___jp_279_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_inc_ref_n(v___y_288_, 2);
v___x_295_ = l_Array_append___redArg(v___y_288_, v___y_294_);
lean_dec_ref(v___y_294_);
lean_inc_n(v___y_287_, 6);
lean_inc_n(v___y_284_, 17);
v___x_296_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_296_, 0, v___y_284_);
lean_ctor_set(v___x_296_, 1, v___y_287_);
lean_ctor_set(v___x_296_, 2, v___x_295_);
v___x_297_ = l_Lean_Syntax_node1(v___y_284_, v___y_287_, v___y_290_);
v___x_298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_298_, 0, v___y_284_);
lean_ctor_set(v___x_298_, 1, v___y_287_);
lean_ctor_set(v___x_298_, 2, v___y_288_);
v___x_299_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__0));
lean_inc_ref_n(v___y_293_, 7);
v___x_300_ = l_Lean_Name_mkStr4(v___x_275_, v___y_293_, v___x_276_, v___x_299_);
v___x_301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_301_, 0, v___y_284_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
v___x_302_ = l_Lean_Syntax_node1(v___y_284_, v___x_300_, v___x_301_);
v___x_303_ = l_Lean_Syntax_node1(v___y_284_, v___y_287_, v___x_302_);
lean_inc_ref_n(v___x_298_, 8);
v___x_304_ = l_Lean_Syntax_node7(v___y_284_, v___y_286_, v___y_289_, v___x_296_, v___x_297_, v___x_298_, v___x_303_, v___x_298_, v___x_298_);
v___x_305_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__1));
v___x_306_ = l_Lean_Name_mkStr4(v___x_275_, v___y_293_, v___x_276_, v___x_305_);
v___x_307_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__2));
v___x_308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_308_, 0, v___y_284_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__3));
v___x_310_ = l_Lean_Name_mkStr4(v___x_275_, v___y_293_, v___x_276_, v___x_309_);
v___x_311_ = lean_box(2);
v___x_312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v___y_287_);
lean_ctor_set(v___x_312_, 2, v___y_283_);
v___x_313_ = l_Lean_mkIdentFrom(v___x_312_, v___y_291_, v___x_278_);
lean_dec_ref_known(v___x_312_, 3);
v___x_314_ = l_Lean_Syntax_node2(v___y_284_, v___x_310_, v___x_313_, v___x_298_);
v___x_315_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__4));
v___x_316_ = l_Lean_Name_mkStr4(v___x_275_, v___y_293_, v___x_276_, v___x_315_);
v___x_317_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__14));
v___x_318_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__5));
v___x_319_ = l_Lean_Name_mkStr4(v___x_275_, v___y_293_, v___x_317_, v___x_318_);
v___x_320_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__33));
v___x_321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_321_, 0, v___y_284_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = l_Lean_Syntax_node2(v___y_284_, v___x_319_, v___x_321_, v___y_285_);
v___x_323_ = l_Lean_Syntax_node1(v___y_284_, v___y_287_, v___x_322_);
v___x_324_ = l_Lean_Syntax_node2(v___y_284_, v___x_316_, v___x_298_, v___x_323_);
v___x_325_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__6));
v___x_326_ = l_Lean_Name_mkStr4(v___x_275_, v___y_293_, v___x_276_, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__40));
v___x_328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_328_, 0, v___y_284_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__7));
v___x_330_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__8));
v___x_331_ = l_Lean_Name_mkStr4(v___x_275_, v___y_293_, v___x_329_, v___x_330_);
v___x_332_ = l_Lean_Syntax_node2(v___y_284_, v___x_331_, v___x_298_, v___x_298_);
v___x_333_ = l_Lean_Syntax_node4(v___y_284_, v___x_326_, v___x_328_, v___y_281_, v___x_332_, v___x_298_);
v___x_334_ = l_Lean_Syntax_node5(v___y_284_, v___x_306_, v___x_308_, v___x_314_, v___x_324_, v___x_333_, v___x_298_);
v___x_335_ = l_Lean_Syntax_node2(v___y_284_, v___y_292_, v___x_304_, v___x_334_);
v___x_336_ = l_Lean_Elab_Command_elabCommand(v___x_335_, v___y_280_, v___y_282_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAuxDef___boxed(lean_object* v_x_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Elab_Command_elabAuxDef(v_x_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1(){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_486_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_487_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__4));
v___x_488_ = ((lean_object*)(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1));
v___x_489_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAuxDef___boxed), 4, 0);
v___x_490_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_486_, v___x_487_, v___x_488_, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___boxed(lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1();
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3(){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((lean_object*)(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1));
v___x_520_ = ((lean_object*)(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__6));
v___x_521_ = l_Lean_addBuiltinDeclarationRanges(v___x_519_, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___boxed(lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3();
return v_res_523_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_AuxDef(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_AuxDef(builtin);
}
#ifdef __cplusplus
}
#endif
