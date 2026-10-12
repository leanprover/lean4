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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_elabAuxDef_spec__2(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_aux"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Command_elabAuxDef___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__15_value),LEAN_SCALAR_PTR_LITERAL(239, 43, 245, 0, 252, 151, 26, 151)}};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__16_value;
static const lean_string_object l_Lean_Elab_Command_elabAuxDef___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__17 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Command_elabAuxDef___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__17_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__13_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabAuxDef___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Command_aux__def___closed__9_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabAuxDef___closed__19 = (const lean_object*)&l_Lean_Elab_Command_elabAuxDef___closed__19_value;
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
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_box(0);
v___x_108_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_107_);
return v___x_109_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg(){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_113_;
v_res_113_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___boxed(lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v_res_115_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0(lean_object* v_00_u03b1_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_120_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_117_ = stack[1].m_obj;
lean_object* v___y_118_ = stack[2].m_obj;
lean_object* v_res_121_;
v_res_121_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0(lean_box(0), v___y_117_, v___y_118_);
stack->m_obj
 = v_res_121_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___boxed(lean_object* v_00_u03b1_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0(v_00_u03b1_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_126_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v_env_130_; lean_object* v___x_131_; lean_object* v_mainModule_132_; lean_object* v___x_133_; 
v___x_129_ = lean_st_ref_get(v___y_127_);
v_env_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc_ref(v_env_130_);
lean_dec(v___x_129_);
v___x_131_ = l_Lean_Environment_header(v_env_130_);
lean_dec_ref(v_env_130_);
v_mainModule_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_mainModule_132_);
lean_dec_ref(v___x_131_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v_mainModule_132_);
return v___x_133_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_127_ = stack[0].m_obj;
lean_object* v_res_134_;
v_res_134_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_127_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg___boxed(lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_135_);
lean_dec(v___y_135_);
return v_res_137_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1(lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_139_);
return v___x_141_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_138_ = stack[0].m_obj;
lean_object* v___y_139_ = stack[1].m_obj;
lean_object* v_res_142_;
v_res_142_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1(v___y_138_, v___y_139_);
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___boxed(lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1(v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
return v_res_146_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3(size_t v_sz_147_, size_t v_i_148_, lean_object* v_bs_149_){
_start:
{
uint8_t v___x_150_; 
v___x_150_ = lean_usize_dec_lt(v_i_148_, v_sz_147_);
if (v___x_150_ == 0)
{
return v_bs_149_;
}
else
{
lean_object* v_v_151_; lean_object* v___x_152_; lean_object* v_bs_x27_153_; lean_object* v___x_154_; lean_object* v___x_155_; size_t v___x_156_; size_t v___x_157_; lean_object* v___x_158_; 
v_v_151_ = lean_array_uget(v_bs_149_, v_i_148_);
v___x_152_ = lean_unsigned_to_nat(0u);
v_bs_x27_153_ = lean_array_uset(v_bs_149_, v_i_148_, v___x_152_);
v___x_154_ = l_Lean_TSyntax_getId(v_v_151_);
lean_dec(v_v_151_);
v___x_155_ = l_Lean_Name_eraseMacroScopes(v___x_154_);
lean_dec(v___x_154_);
v___x_156_ = ((size_t)1ULL);
v___x_157_ = lean_usize_add(v_i_148_, v___x_156_);
v___x_158_ = lean_array_uset(v_bs_x27_153_, v_i_148_, v___x_155_);
v_i_148_ = v___x_157_;
v_bs_149_ = v___x_158_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_147_ = stack[0].m_num;
size_t v_i_148_ = stack[1].m_num;
lean_object* v_bs_149_ = stack[2].m_obj;
lean_object* v_res_160_;
v_res_160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3(v_sz_147_, v_i_148_, v_bs_149_);
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3___boxed(lean_object* v_sz_161_, lean_object* v_i_162_, lean_object* v_bs_163_){
_start:
{
size_t v_sz_boxed_164_; size_t v_i_boxed_165_; lean_object* v_res_166_; 
v_sz_boxed_164_ = lean_unbox_usize(v_sz_161_);
lean_dec(v_sz_161_);
v_i_boxed_165_ = lean_unbox_usize(v_i_162_);
lean_dec(v_i_162_);
v_res_166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3(v_sz_boxed_164_, v_i_boxed_165_, v_bs_163_);
return v_res_166_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(lean_object* v_as_167_, size_t v_i_168_, size_t v_stop_169_, lean_object* v_b_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = lean_usize_dec_eq(v_i_168_, v_stop_169_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; size_t v___x_174_; size_t v___x_175_; 
v___x_172_ = lean_array_uget_borrowed(v_as_167_, v_i_168_);
lean_inc(v___x_172_);
v___x_173_ = l_Lean_Name_append(v_b_170_, v___x_172_);
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_add(v_i_168_, v___x_174_);
v_i_168_ = v___x_175_;
v_b_170_ = v___x_173_;
goto _start;
}
else
{
return v_b_170_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_167_ = stack[0].m_obj;
size_t v_i_168_ = stack[1].m_num;
size_t v_stop_169_ = stack[2].m_num;
lean_object* v_b_170_ = stack[3].m_obj;
lean_object* v_res_177_;
v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(v_as_167_, v_i_168_, v_stop_169_, v_b_170_);
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4___boxed(lean_object* v_as_178_, lean_object* v_i_179_, lean_object* v_stop_180_, lean_object* v_b_181_){
_start:
{
size_t v_i_boxed_182_; size_t v_stop_boxed_183_; lean_object* v_res_184_; 
v_i_boxed_182_ = lean_unbox_usize(v_i_179_);
lean_dec(v_i_179_);
v_stop_boxed_183_ = lean_unbox_usize(v_stop_180_);
lean_dec(v_stop_180_);
v_res_184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(v_as_178_, v_i_boxed_182_, v_stop_boxed_183_, v_b_181_);
lean_dec_ref(v_as_178_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_elabAuxDef_spec__2(lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
if (lean_obj_tag(v_a_185_) == 0)
{
lean_object* v___x_187_; 
v___x_187_ = l_List_reverse___redArg(v_a_186_);
return v___x_187_;
}
else
{
lean_object* v_head_188_; lean_object* v_tail_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_199_; 
v_head_188_ = lean_ctor_get(v_a_185_, 0);
v_tail_189_ = lean_ctor_get(v_a_185_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_a_185_);
if (v_isSharedCheck_199_ == 0)
{
v___x_191_ = v_a_185_;
v_isShared_192_ = v_isSharedCheck_199_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_tail_189_);
lean_inc(v_head_188_);
lean_dec(v_a_185_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_199_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_193_ = 0;
v___x_194_ = l_Lean_Name_toString(v_head_188_, v___x_193_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v_a_186_);
lean_ctor_set(v___x_191_, 0, v___x_194_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_a_186_);
v___x_196_ = v_reuseFailAlloc_198_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
v_a_185_ = v_tail_189_;
v_a_186_ = v___x_196_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAuxDef___closed__14(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Array_mkArray0___redArg();
return v___x_216_;
}
}
lean_object* l_Lean_Elab_Command_elabAuxDef(lean_object* v_x_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; 
v___x_232_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__0));
v___x_233_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__2));
v___x_234_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__4));
lean_inc(v_x_228_);
v___x_235_ = l_Lean_Syntax_isOfKind(v_x_228_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_294_; 
lean_dec(v_x_228_);
v___x_294_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_405_; lean_object* v_attrs_x3f_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v_doc_x3f_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_450_ = l_Lean_Syntax_getArg(v_x_228_, v___x_295_);
v___x_451_ = l_Lean_Syntax_isNone(v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_450_);
v___x_453_ = l_Lean_Syntax_matchesNull(v___x_450_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_dec(v___x_450_);
lean_dec(v_x_228_);
v___x_454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_454_;
}
else
{
lean_object* v_doc_x3f_455_; 
v_doc_x3f_455_ = l_Lean_Syntax_getArg(v___x_450_, v___x_295_);
lean_dec(v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__19));
lean_inc(v_doc_x3f_455_);
v___x_459_ = l_Lean_Syntax_isOfKind(v_doc_x3f_455_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v_doc_x3f_455_);
lean_dec(v_x_228_);
v___x_460_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_460_;
}
else
{
goto v___jp_456_;
}
}
else
{
goto v___jp_456_;
}
v___jp_456_:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v_doc_x3f_455_);
v_doc_x3f_437_ = v___x_457_;
v___y_438_ = v_a_229_;
v___y_439_ = v_a_230_;
goto v___jp_436_;
}
}
}
else
{
lean_object* v___x_461_; 
lean_dec(v___x_450_);
v___x_461_ = lean_box(0);
v_doc_x3f_437_ = v___x_461_;
v___y_438_ = v_a_229_;
v___y_439_ = v_a_230_;
goto v___jp_436_;
}
v___jp_296_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_inc_ref(v___y_307_);
v___x_312_ = l_Array_append___redArg(v___y_307_, v___y_311_);
lean_dec_ref(v___y_311_);
lean_inc(v___y_297_);
lean_inc(v___y_304_);
v___x_313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_313_, 0, v___y_304_);
lean_ctor_set(v___x_313_, 1, v___y_297_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
if (lean_obj_tag(v___y_310_) == 1)
{
lean_object* v_val_314_; lean_object* v___x_315_; 
v_val_314_ = lean_ctor_get(v___y_310_, 0);
lean_inc(v_val_314_);
lean_dec_ref_known(v___y_310_, 1);
v___x_315_ = l_Array_mkArray1___redArg(v_val_314_);
v___y_237_ = v___y_297_;
v___y_238_ = v___x_313_;
v___y_239_ = v___y_298_;
v___y_240_ = v___y_299_;
v___y_241_ = v___y_300_;
v___y_242_ = v___y_301_;
v___y_243_ = v___y_302_;
v___y_244_ = v___y_303_;
v___y_245_ = v___y_304_;
v___y_246_ = v___y_305_;
v___y_247_ = v___y_306_;
v___y_248_ = v___y_307_;
v___y_249_ = v___y_309_;
v___y_250_ = v___y_308_;
v___y_251_ = v___x_315_;
goto v___jp_236_;
}
else
{
lean_object* v___x_316_; 
lean_dec(v___y_310_);
v___x_316_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__9));
v___y_237_ = v___y_297_;
v___y_238_ = v___x_313_;
v___y_239_ = v___y_298_;
v___y_240_ = v___y_299_;
v___y_241_ = v___y_300_;
v___y_242_ = v___y_301_;
v___y_243_ = v___y_302_;
v___y_244_ = v___y_303_;
v___y_245_ = v___y_304_;
v___y_246_ = v___y_305_;
v___y_247_ = v___y_306_;
v___y_248_ = v___y_307_;
v___y_249_ = v___y_309_;
v___y_250_ = v___y_308_;
v___y_251_ = v___x_316_;
goto v___jp_236_;
}
}
v___jp_317_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_329_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__10));
lean_inc_ref_n(v___y_321_, 2);
v___x_330_ = l_Lean_Name_mkStr4(v___x_232_, v___y_321_, v___x_233_, v___x_329_);
v___x_331_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__11));
v___x_332_ = l_Lean_Name_mkStr4(v___x_232_, v___y_321_, v___x_233_, v___x_331_);
v___x_333_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__13));
v___x_334_ = lean_obj_once(&l_Lean_Elab_Command_elabAuxDef___closed__14, &l_Lean_Elab_Command_elabAuxDef___closed__14_once, _init_l_Lean_Elab_Command_elabAuxDef___closed__14);
if (lean_obj_tag(v___y_322_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_336_; 
v_val_335_ = lean_ctor_get(v___y_322_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v___y_322_, 1);
v___x_336_ = l_Array_mkArray1___redArg(v_val_335_);
v___y_297_ = v___x_333_;
v___y_298_ = v___y_326_;
v___y_299_ = v___x_330_;
v___y_300_ = v___y_318_;
v___y_301_ = v___y_320_;
v___y_302_ = v___y_321_;
v___y_303_ = v___y_319_;
v___y_304_ = v___y_324_;
v___y_305_ = v___y_323_;
v___y_306_ = v___y_325_;
v___y_307_ = v___x_334_;
v___y_308_ = v___y_327_;
v___y_309_ = v___x_332_;
v___y_310_ = v___y_328_;
v___y_311_ = v___x_336_;
goto v___jp_296_;
}
else
{
lean_object* v___x_337_; 
lean_dec(v___y_322_);
v___x_337_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__9));
v___y_297_ = v___x_333_;
v___y_298_ = v___y_326_;
v___y_299_ = v___x_330_;
v___y_300_ = v___y_318_;
v___y_301_ = v___y_320_;
v___y_302_ = v___y_321_;
v___y_303_ = v___y_319_;
v___y_304_ = v___y_324_;
v___y_305_ = v___y_323_;
v___y_306_ = v___y_325_;
v___y_307_ = v___x_334_;
v___y_308_ = v___y_327_;
v___y_309_ = v___x_332_;
v___y_310_ = v___y_328_;
v___y_311_ = v___x_337_;
goto v___jp_296_;
}
}
v___jp_338_:
{
lean_object* v___x_350_; lean_object* v_a_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_350_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_341_);
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref(v___x_350_);
v___x_352_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__16));
v___x_353_ = l_Lean_Name_append(v___x_352_, v_a_351_);
v___x_354_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__17));
v___x_355_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__18));
v___x_356_ = l_Lean_Name_append(v___x_353_, v___x_355_);
v___x_357_ = l_Lean_Name_append(v___x_356_, v___y_349_);
v___x_358_ = l_Lean_Name_components(v___x_357_);
v___x_359_ = lean_box(0);
v___x_360_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabAuxDef_spec__2(v___x_358_, v___x_359_);
v___x_361_ = l_String_intercalate(v___x_354_, v___x_360_);
v___x_362_ = l_Lean_Elab_Command_getScope___redArg(v___y_341_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v_currNamespace_364_; lean_object* v___x_365_; lean_object* v_env_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_fst_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v_currNamespace_364_ = lean_ctor_get(v_a_363_, 2);
lean_inc_n(v_currNamespace_364_, 2);
lean_dec(v_a_363_);
v___x_365_ = lean_st_ref_get(v___y_341_);
v_env_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_366_);
lean_dec(v___x_365_);
v___x_367_ = l_Lean_Environment_setExporting(v_env_366_, v___x_235_);
v___x_368_ = l_Lean_DeclNameGenerator_ofPrefix(v_currNamespace_364_);
lean_inc(v___y_343_);
v___x_369_ = l_Lean_Name_str___override(v___y_343_, v___x_361_);
v___x_370_ = l_Lean_DeclNameGenerator_mkUniqueName(v___x_367_, v___x_368_, v___x_369_);
v_fst_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_fst_371_);
lean_dec_ref(v___x_370_);
v___x_372_ = l_Lean_Name_replacePrefix(v_fst_371_, v_currNamespace_364_, v___y_343_);
lean_dec(v___y_343_);
lean_dec(v_currNamespace_364_);
v___x_373_ = l_Lean_Elab_Command_getRef___redArg(v___y_342_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_373_, 1);
v___x_375_ = 0;
v___x_376_ = l_Lean_SourceInfo_fromRef(v_a_374_, v___x_375_);
lean_dec(v_a_374_);
v___x_377_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_342_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_quotContext_x3f_378_; 
lean_dec_ref_known(v___x_377_, 1);
v_quotContext_x3f_378_ = lean_ctor_get(v___y_342_, 5);
if (lean_obj_tag(v_quotContext_x3f_378_) == 0)
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_341_);
lean_dec_ref(v___x_379_);
v___y_318_ = v___y_339_;
v___y_319_ = v___y_342_;
v___y_320_ = v___y_341_;
v___y_321_ = v___y_340_;
v___y_322_ = v___y_344_;
v___y_323_ = v___y_345_;
v___y_324_ = v___x_376_;
v___y_325_ = v___y_347_;
v___y_326_ = v___y_346_;
v___y_327_ = v___x_372_;
v___y_328_ = v___y_348_;
goto v___jp_317_;
}
else
{
v___y_318_ = v___y_339_;
v___y_319_ = v___y_342_;
v___y_320_ = v___y_341_;
v___y_321_ = v___y_340_;
v___y_322_ = v___y_344_;
v___y_323_ = v___y_345_;
v___y_324_ = v___x_376_;
v___y_325_ = v___y_347_;
v___y_326_ = v___y_346_;
v___y_327_ = v___x_372_;
v___y_328_ = v___y_348_;
goto v___jp_317_;
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec(v___x_376_);
lean_dec(v___x_372_);
lean_dec(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec(v___y_344_);
lean_dec(v___y_339_);
v_a_380_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_377_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_377_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v___x_372_);
lean_dec(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec(v___y_344_);
lean_dec(v___y_339_);
v_a_388_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_373_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_373_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v___x_361_);
lean_dec(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec(v___y_344_);
lean_dec(v___y_343_);
lean_dec(v___y_339_);
v_a_396_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_362_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_362_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
v___jp_404_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_suggestion_417_; lean_object* v___x_418_; lean_object* v___x_419_; size_t v_sz_420_; size_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_409_ = lean_unsigned_to_nat(2u);
v___x_410_ = l_Lean_Syntax_getArg(v_x_228_, v___x_409_);
v___x_411_ = lean_unsigned_to_nat(4u);
v___x_412_ = l_Lean_Syntax_getArg(v_x_228_, v___x_411_);
v___x_413_ = lean_unsigned_to_nat(6u);
v___x_414_ = l_Lean_Syntax_getArg(v_x_228_, v___x_413_);
v___x_415_ = lean_unsigned_to_nat(8u);
v___x_416_ = l_Lean_Syntax_getArg(v_x_228_, v___x_415_);
lean_dec(v_x_228_);
v_suggestion_417_ = l_Lean_Syntax_getArgs(v___x_412_);
lean_dec(v___x_412_);
v___x_418_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__13));
v___x_419_ = lean_box(0);
v_sz_420_ = lean_array_size(v_suggestion_417_);
v___x_421_ = ((size_t)0ULL);
lean_inc_ref(v_suggestion_417_);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3(v_sz_420_, v___x_421_, v_suggestion_417_);
v___x_423_ = lean_array_get_size(v___x_422_);
v___x_424_ = lean_nat_dec_lt(v___x_295_, v___x_423_);
if (v___x_424_ == 0)
{
lean_dec_ref(v___x_422_);
v___y_339_ = v___x_414_;
v___y_340_ = v___x_418_;
v___y_341_ = v___y_408_;
v___y_342_ = v___y_407_;
v___y_343_ = v___x_419_;
v___y_344_ = v___y_405_;
v___y_345_ = v___x_416_;
v___y_346_ = v_suggestion_417_;
v___y_347_ = v___x_410_;
v___y_348_ = v_attrs_x3f_406_;
v___y_349_ = v___x_419_;
goto v___jp_338_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = lean_nat_dec_le(v___x_423_, v___x_423_);
if (v___x_425_ == 0)
{
if (v___x_424_ == 0)
{
lean_dec_ref(v___x_422_);
v___y_339_ = v___x_414_;
v___y_340_ = v___x_418_;
v___y_341_ = v___y_408_;
v___y_342_ = v___y_407_;
v___y_343_ = v___x_419_;
v___y_344_ = v___y_405_;
v___y_345_ = v___x_416_;
v___y_346_ = v_suggestion_417_;
v___y_347_ = v___x_410_;
v___y_348_ = v_attrs_x3f_406_;
v___y_349_ = v___x_419_;
goto v___jp_338_;
}
else
{
size_t v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_usize_of_nat(v___x_423_);
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(v___x_422_, v___x_421_, v___x_426_, v___x_419_);
lean_dec_ref(v___x_422_);
v___y_339_ = v___x_414_;
v___y_340_ = v___x_418_;
v___y_341_ = v___y_408_;
v___y_342_ = v___y_407_;
v___y_343_ = v___x_419_;
v___y_344_ = v___y_405_;
v___y_345_ = v___x_416_;
v___y_346_ = v_suggestion_417_;
v___y_347_ = v___x_410_;
v___y_348_ = v_attrs_x3f_406_;
v___y_349_ = v___x_427_;
goto v___jp_338_;
}
}
else
{
size_t v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_usize_of_nat(v___x_423_);
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(v___x_422_, v___x_421_, v___x_428_, v___x_419_);
lean_dec_ref(v___x_422_);
v___y_339_ = v___x_414_;
v___y_340_ = v___x_418_;
v___y_341_ = v___y_408_;
v___y_342_ = v___y_407_;
v___y_343_ = v___x_419_;
v___y_344_ = v___y_405_;
v___y_345_ = v___x_416_;
v___y_346_ = v_suggestion_417_;
v___y_347_ = v___x_410_;
v___y_348_ = v_attrs_x3f_406_;
v___y_349_ = v___x_429_;
goto v___jp_338_;
}
}
}
v___jp_430_:
{
lean_object* v___x_435_; 
v___x_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_435_, 0, v___y_434_);
v___y_405_ = v___y_431_;
v_attrs_x3f_406_ = v___x_435_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_433_;
goto v___jp_404_;
}
v___jp_436_:
{
lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = l_Lean_Syntax_getArg(v_x_228_, v___x_440_);
v___x_442_ = l_Lean_Syntax_isNone(v___x_441_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; 
lean_inc(v___x_441_);
v___x_443_ = l_Lean_Syntax_matchesNull(v___x_441_, v___x_440_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_dec(v___x_441_);
lean_dec(v_doc_x3f_437_);
lean_dec(v_x_228_);
v___x_444_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_444_;
}
else
{
lean_object* v_attrs_x3f_445_; 
v_attrs_x3f_445_ = l_Lean_Syntax_getArg(v___x_441_, v___x_295_);
lean_dec(v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__16));
lean_inc(v_attrs_x3f_445_);
v___x_447_ = l_Lean_Syntax_isOfKind(v_attrs_x3f_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
lean_dec(v_attrs_x3f_445_);
lean_dec(v_doc_x3f_437_);
lean_dec(v_x_228_);
v___x_448_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_448_;
}
else
{
v___y_431_ = v_doc_x3f_437_;
v___y_432_ = v___y_438_;
v___y_433_ = v___y_439_;
v___y_434_ = v_attrs_x3f_445_;
goto v___jp_430_;
}
}
else
{
v___y_431_ = v_doc_x3f_437_;
v___y_432_ = v___y_438_;
v___y_433_ = v___y_439_;
v___y_434_ = v_attrs_x3f_445_;
goto v___jp_430_;
}
}
}
else
{
lean_object* v___x_449_; 
lean_dec(v___x_441_);
v___x_449_ = lean_box(0);
v___y_405_ = v_doc_x3f_437_;
v_attrs_x3f_406_ = v___x_449_;
v___y_407_ = v___y_438_;
v___y_408_ = v___y_439_;
goto v___jp_404_;
}
}
}
v___jp_236_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
lean_inc_ref_n(v___y_248_, 2);
v___x_252_ = l_Array_append___redArg(v___y_248_, v___y_251_);
lean_dec_ref(v___y_251_);
lean_inc_n(v___y_237_, 6);
lean_inc_n(v___y_245_, 17);
v___x_253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_253_, 0, v___y_245_);
lean_ctor_set(v___x_253_, 1, v___y_237_);
lean_ctor_set(v___x_253_, 2, v___x_252_);
v___x_254_ = l_Lean_Syntax_node1(v___y_245_, v___y_237_, v___y_247_);
v___x_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_255_, 0, v___y_245_);
lean_ctor_set(v___x_255_, 1, v___y_237_);
lean_ctor_set(v___x_255_, 2, v___y_248_);
v___x_256_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__0));
lean_inc_ref_n(v___y_243_, 7);
v___x_257_ = l_Lean_Name_mkStr4(v___x_232_, v___y_243_, v___x_233_, v___x_256_);
v___x_258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_258_, 0, v___y_245_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
v___x_259_ = l_Lean_Syntax_node1(v___y_245_, v___x_257_, v___x_258_);
v___x_260_ = l_Lean_Syntax_node1(v___y_245_, v___y_237_, v___x_259_);
lean_inc_ref_n(v___x_255_, 8);
v___x_261_ = l_Lean_Syntax_node7(v___y_245_, v___y_249_, v___y_238_, v___x_253_, v___x_254_, v___x_255_, v___x_260_, v___x_255_, v___x_255_);
v___x_262_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__1));
v___x_263_ = l_Lean_Name_mkStr4(v___x_232_, v___y_243_, v___x_233_, v___x_262_);
v___x_264_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__2));
v___x_265_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_265_, 0, v___y_245_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__3));
v___x_267_ = l_Lean_Name_mkStr4(v___x_232_, v___y_243_, v___x_233_, v___x_266_);
v___x_268_ = lean_box(2);
v___x_269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___y_237_);
lean_ctor_set(v___x_269_, 2, v___y_239_);
v___x_270_ = l_Lean_mkIdentFrom(v___x_269_, v___y_250_, v___x_235_);
lean_dec_ref_known(v___x_269_, 3);
v___x_271_ = l_Lean_Syntax_node2(v___y_245_, v___x_267_, v___x_270_, v___x_255_);
v___x_272_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__4));
v___x_273_ = l_Lean_Name_mkStr4(v___x_232_, v___y_243_, v___x_233_, v___x_272_);
v___x_274_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__14));
v___x_275_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__5));
v___x_276_ = l_Lean_Name_mkStr4(v___x_232_, v___y_243_, v___x_274_, v___x_275_);
v___x_277_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__33));
v___x_278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_278_, 0, v___y_245_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = l_Lean_Syntax_node2(v___y_245_, v___x_276_, v___x_278_, v___y_241_);
v___x_280_ = l_Lean_Syntax_node1(v___y_245_, v___y_237_, v___x_279_);
v___x_281_ = l_Lean_Syntax_node2(v___y_245_, v___x_273_, v___x_255_, v___x_280_);
v___x_282_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__6));
v___x_283_ = l_Lean_Name_mkStr4(v___x_232_, v___y_243_, v___x_233_, v___x_282_);
v___x_284_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__40));
v___x_285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_285_, 0, v___y_245_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__7));
v___x_287_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__8));
v___x_288_ = l_Lean_Name_mkStr4(v___x_232_, v___y_243_, v___x_286_, v___x_287_);
v___x_289_ = l_Lean_Syntax_node2(v___y_245_, v___x_288_, v___x_255_, v___x_255_);
v___x_290_ = l_Lean_Syntax_node4(v___y_245_, v___x_283_, v___x_285_, v___y_246_, v___x_289_, v___x_255_);
v___x_291_ = l_Lean_Syntax_node5(v___y_245_, v___x_263_, v___x_265_, v___x_271_, v___x_281_, v___x_290_, v___x_255_);
v___x_292_ = l_Lean_Syntax_node2(v___y_245_, v___y_240_, v___x_261_, v___x_291_);
v___x_293_ = l_Lean_Elab_Command_elabCommand(v___x_292_, v___y_244_, v___y_242_);
return v___x_293_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabAuxDef_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_228_ = stack[0].m_obj;
lean_object* v_a_229_ = stack[1].m_obj;
lean_object* v_a_230_ = stack[2].m_obj;
lean_object* v_res_462_;
v_res_462_ = l_Lean_Elab_Command_elabAuxDef(v_x_228_, v_a_229_, v_a_230_);
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAuxDef___boxed(lean_object* v_x_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Elab_Command_elabAuxDef(v_x_463_, v_a_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
return v_res_467_;
}
}
lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1(){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_475_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_476_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__4));
v___x_477_ = ((lean_object*)(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1));
v___x_478_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAuxDef___boxed), 4, 0);
v___x_479_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_475_, v___x_476_, v___x_477_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_480_;
v_res_480_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1();
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___boxed(lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1();
return v_res_482_;
}
}
lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3(){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = ((lean_object*)(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1));
v___x_510_ = ((lean_object*)(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__6));
v___x_511_ = l_Lean_addBuiltinDeclarationRanges(v___x_509_, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_512_;
v_res_512_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3();
stack->m_obj
 = v_res_512_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___boxed(lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3();
return v_res_514_;
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
