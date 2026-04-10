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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_DeclNameGenerator_ofPrefix(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg(){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___boxed(lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0(lean_object* v_00_u03b1_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___boxed(lean_object* v_00_u03b1_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0(v_00_u03b1_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; lean_object* v_env_128_; lean_object* v___x_129_; lean_object* v_mainModule_130_; lean_object* v___x_131_; 
v___x_127_ = lean_st_ref_get(v___y_125_);
v_env_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc_ref(v_env_128_);
lean_dec(v___x_127_);
v___x_129_ = l_Lean_Environment_header(v_env_128_);
lean_dec_ref(v_env_128_);
v_mainModule_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_mainModule_130_);
lean_dec_ref(v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v_mainModule_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg___boxed(lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_132_);
lean_dec(v___y_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1(lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___boxed(lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1(v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3(size_t v_sz_143_, size_t v_i_144_, lean_object* v_bs_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = lean_usize_dec_lt(v_i_144_, v_sz_143_);
if (v___x_146_ == 0)
{
return v_bs_145_;
}
else
{
lean_object* v_v_147_; lean_object* v___x_148_; lean_object* v_bs_x27_149_; lean_object* v___x_150_; lean_object* v___x_151_; size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; 
v_v_147_ = lean_array_uget(v_bs_145_, v_i_144_);
v___x_148_ = lean_unsigned_to_nat(0u);
v_bs_x27_149_ = lean_array_uset(v_bs_145_, v_i_144_, v___x_148_);
v___x_150_ = l_Lean_TSyntax_getId(v_v_147_);
lean_dec(v_v_147_);
v___x_151_ = lean_erase_macro_scopes(v___x_150_);
v___x_152_ = ((size_t)1ULL);
v___x_153_ = lean_usize_add(v_i_144_, v___x_152_);
v___x_154_ = lean_array_uset(v_bs_x27_149_, v_i_144_, v___x_151_);
v_i_144_ = v___x_153_;
v_bs_145_ = v___x_154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3___boxed(lean_object* v_sz_156_, lean_object* v_i_157_, lean_object* v_bs_158_){
_start:
{
size_t v_sz_boxed_159_; size_t v_i_boxed_160_; lean_object* v_res_161_; 
v_sz_boxed_159_ = lean_unbox_usize(v_sz_156_);
lean_dec(v_sz_156_);
v_i_boxed_160_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_res_161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3(v_sz_boxed_159_, v_i_boxed_160_, v_bs_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(lean_object* v_as_162_, size_t v_i_163_, size_t v_stop_164_, lean_object* v_b_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = lean_usize_dec_eq(v_i_163_, v_stop_164_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; size_t v___x_169_; size_t v___x_170_; 
v___x_167_ = lean_array_uget_borrowed(v_as_162_, v_i_163_);
lean_inc(v___x_167_);
v___x_168_ = l_Lean_Name_append(v_b_165_, v___x_167_);
v___x_169_ = ((size_t)1ULL);
v___x_170_ = lean_usize_add(v_i_163_, v___x_169_);
v_i_163_ = v___x_170_;
v_b_165_ = v___x_168_;
goto _start;
}
else
{
return v_b_165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4___boxed(lean_object* v_as_172_, lean_object* v_i_173_, lean_object* v_stop_174_, lean_object* v_b_175_){
_start:
{
size_t v_i_boxed_176_; size_t v_stop_boxed_177_; lean_object* v_res_178_; 
v_i_boxed_176_ = lean_unbox_usize(v_i_173_);
lean_dec(v_i_173_);
v_stop_boxed_177_ = lean_unbox_usize(v_stop_174_);
lean_dec(v_stop_174_);
v_res_178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(v_as_172_, v_i_boxed_176_, v_stop_boxed_177_, v_b_175_);
lean_dec_ref(v_as_172_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_elabAuxDef_spec__2(lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
if (lean_obj_tag(v_a_179_) == 0)
{
lean_object* v___x_181_; 
v___x_181_ = l_List_reverse___redArg(v_a_180_);
return v___x_181_;
}
else
{
lean_object* v_head_182_; lean_object* v_tail_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_193_; 
v_head_182_ = lean_ctor_get(v_a_179_, 0);
v_tail_183_ = lean_ctor_get(v_a_179_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v_a_179_);
if (v_isSharedCheck_193_ == 0)
{
v___x_185_ = v_a_179_;
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_tail_183_);
lean_inc(v_head_182_);
lean_dec(v_a_179_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
uint8_t v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_187_ = 0;
v___x_188_ = l_Lean_Name_toString(v_head_182_, v___x_187_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v_a_180_);
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_190_ = v___x_185_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_a_180_);
v___x_190_ = v_reuseFailAlloc_192_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
v_a_179_ = v_tail_183_;
v_a_180_ = v___x_190_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAuxDef___closed__14(void){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Array_mkArray0(lean_box(0));
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAuxDef(lean_object* v_x_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; 
v___x_226_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__0));
v___x_227_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__2));
v___x_228_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__4));
lean_inc(v_x_222_);
v___x_229_ = l_Lean_Syntax_isOfKind(v_x_222_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_288_; 
lean_dec(v_x_222_);
v___x_288_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_288_;
}
else
{
lean_object* v___x_289_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_399_; lean_object* v_attrs_x3f_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v_doc_x3f_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_439_ = l_Lean_Syntax_getArg(v_x_222_, v___x_289_);
v___x_440_ = l_Lean_Syntax_isNone(v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_439_);
v___x_442_ = l_Lean_Syntax_matchesNull(v___x_439_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
lean_dec(v___x_439_);
lean_dec(v_x_222_);
v___x_443_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_443_;
}
else
{
lean_object* v_doc_x3f_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_doc_x3f_444_ = l_Lean_Syntax_getArg(v___x_439_, v___x_289_);
lean_dec(v___x_439_);
v___x_445_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__19));
lean_inc(v_doc_x3f_444_);
v___x_446_ = l_Lean_Syntax_isOfKind(v_doc_x3f_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec(v_doc_x3f_444_);
lean_dec(v_x_222_);
v___x_447_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_447_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_doc_x3f_444_);
v_doc_x3f_425_ = v___x_448_;
v___y_426_ = v_a_223_;
v___y_427_ = v_a_224_;
goto v___jp_424_;
}
}
}
else
{
lean_object* v___x_449_; 
lean_dec(v___x_439_);
v___x_449_ = lean_box(0);
v_doc_x3f_425_ = v___x_449_;
v___y_426_ = v_a_223_;
v___y_427_ = v_a_224_;
goto v___jp_424_;
}
v___jp_290_:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_inc_ref(v___y_298_);
v___x_306_ = l_Array_append___redArg(v___y_298_, v___y_305_);
lean_dec_ref(v___y_305_);
lean_inc(v___y_291_);
lean_inc(v___y_301_);
v___x_307_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_307_, 0, v___y_301_);
lean_ctor_set(v___x_307_, 1, v___y_291_);
lean_ctor_set(v___x_307_, 2, v___x_306_);
if (lean_obj_tag(v___y_297_) == 1)
{
lean_object* v_val_308_; lean_object* v___x_309_; 
v_val_308_ = lean_ctor_get(v___y_297_, 0);
lean_inc(v_val_308_);
lean_dec_ref(v___y_297_);
v___x_309_ = l_Array_mkArray1___redArg(v_val_308_);
v___y_231_ = v___y_291_;
v___y_232_ = v___y_292_;
v___y_233_ = v___y_293_;
v___y_234_ = v___y_294_;
v___y_235_ = v___x_307_;
v___y_236_ = v___y_295_;
v___y_237_ = v___y_296_;
v___y_238_ = v___y_298_;
v___y_239_ = v___y_299_;
v___y_240_ = v___y_300_;
v___y_241_ = v___y_301_;
v___y_242_ = v___y_302_;
v___y_243_ = v___y_303_;
v___y_244_ = v___y_304_;
v___y_245_ = v___x_309_;
goto v___jp_230_;
}
else
{
lean_object* v___x_310_; 
lean_dec(v___y_297_);
v___x_310_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__9));
v___y_231_ = v___y_291_;
v___y_232_ = v___y_292_;
v___y_233_ = v___y_293_;
v___y_234_ = v___y_294_;
v___y_235_ = v___x_307_;
v___y_236_ = v___y_295_;
v___y_237_ = v___y_296_;
v___y_238_ = v___y_298_;
v___y_239_ = v___y_299_;
v___y_240_ = v___y_300_;
v___y_241_ = v___y_301_;
v___y_242_ = v___y_302_;
v___y_243_ = v___y_303_;
v___y_244_ = v___y_304_;
v___y_245_ = v___x_310_;
goto v___jp_230_;
}
}
v___jp_311_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__10));
lean_inc_ref_n(v___y_313_, 2);
v___x_324_ = l_Lean_Name_mkStr4(v___x_226_, v___y_313_, v___x_227_, v___x_323_);
v___x_325_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__11));
v___x_326_ = l_Lean_Name_mkStr4(v___x_226_, v___y_313_, v___x_227_, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__13));
v___x_328_ = lean_obj_once(&l_Lean_Elab_Command_elabAuxDef___closed__14, &l_Lean_Elab_Command_elabAuxDef___closed__14_once, _init_l_Lean_Elab_Command_elabAuxDef___closed__14);
if (lean_obj_tag(v___y_317_) == 1)
{
lean_object* v_val_329_; lean_object* v___x_330_; 
v_val_329_ = lean_ctor_get(v___y_317_, 0);
lean_inc(v_val_329_);
lean_dec_ref(v___y_317_);
v___x_330_ = l_Array_mkArray1___redArg(v_val_329_);
v___y_291_ = v___x_327_;
v___y_292_ = v___y_313_;
v___y_293_ = v___y_312_;
v___y_294_ = v___y_314_;
v___y_295_ = v___y_316_;
v___y_296_ = v___y_318_;
v___y_297_ = v___y_319_;
v___y_298_ = v___x_328_;
v___y_299_ = v___y_321_;
v___y_300_ = v___y_320_;
v___y_301_ = v___y_322_;
v___y_302_ = v___x_324_;
v___y_303_ = v___x_326_;
v___y_304_ = v___y_315_;
v___y_305_ = v___x_330_;
goto v___jp_290_;
}
else
{
lean_object* v___x_331_; 
lean_dec(v___y_317_);
v___x_331_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__9));
v___y_291_ = v___x_327_;
v___y_292_ = v___y_313_;
v___y_293_ = v___y_312_;
v___y_294_ = v___y_314_;
v___y_295_ = v___y_316_;
v___y_296_ = v___y_318_;
v___y_297_ = v___y_319_;
v___y_298_ = v___x_328_;
v___y_299_ = v___y_321_;
v___y_300_ = v___y_320_;
v___y_301_ = v___y_322_;
v___y_302_ = v___x_324_;
v___y_303_ = v___x_326_;
v___y_304_ = v___y_315_;
v___y_305_ = v___x_331_;
goto v___jp_290_;
}
}
v___jp_332_:
{
lean_object* v___x_344_; lean_object* v_a_345_; lean_object* v___x_346_; 
v___x_344_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_335_);
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref(v___x_344_);
v___x_346_ = l_Lean_Elab_Command_getScope___redArg(v___y_335_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; lean_object* v_currNamespace_349_; lean_object* v_env_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_fst_365_; lean_object* v___x_366_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref(v___x_346_);
v___x_348_ = lean_st_ref_get(v___y_335_);
v_currNamespace_349_ = lean_ctor_get(v_a_347_, 2);
lean_inc_n(v_currNamespace_349_, 2);
lean_dec(v_a_347_);
v_env_350_ = lean_ctor_get(v___x_348_, 0);
lean_inc_ref(v_env_350_);
lean_dec(v___x_348_);
v___x_351_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__16));
v___x_352_ = l_Lean_Name_append(v___x_351_, v_a_345_);
v___x_353_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__17));
v___x_354_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__18));
v___x_355_ = l_Lean_Name_append(v___x_352_, v___x_354_);
v___x_356_ = l_Lean_Name_append(v___x_355_, v___y_343_);
v___x_357_ = l_Lean_Name_components(v___x_356_);
v___x_358_ = lean_box(0);
v___x_359_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabAuxDef_spec__2(v___x_357_, v___x_358_);
v___x_360_ = l_String_intercalate(v___x_353_, v___x_359_);
v___x_361_ = l_Lean_Environment_setExporting(v_env_350_, v___x_229_);
v___x_362_ = l_Lean_DeclNameGenerator_ofPrefix(v_currNamespace_349_);
lean_inc(v___y_342_);
v___x_363_ = l_Lean_Name_str___override(v___y_342_, v___x_360_);
v___x_364_ = l_Lean_DeclNameGenerator_mkUniqueName(v___x_361_, v___x_362_, v___x_363_);
v_fst_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_fst_365_);
lean_dec_ref(v___x_364_);
v___x_366_ = l_Lean_Elab_Command_getRef___redArg(v___y_341_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref(v___x_366_);
v___x_368_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_341_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_quotContext_x3f_369_; lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; 
lean_dec_ref(v___x_368_);
v_quotContext_x3f_369_ = lean_ctor_get(v___y_341_, 5);
v___x_370_ = l_Lean_Name_replacePrefix(v_fst_365_, v_currNamespace_349_, v___y_342_);
lean_dec(v___y_342_);
lean_dec(v_currNamespace_349_);
v___x_371_ = 0;
v___x_372_ = l_Lean_SourceInfo_fromRef(v_a_367_, v___x_371_);
lean_dec(v_a_367_);
if (lean_obj_tag(v_quotContext_x3f_369_) == 0)
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_335_);
lean_dec_ref(v___x_373_);
v___y_312_ = v___y_334_;
v___y_313_ = v___y_333_;
v___y_314_ = v___y_335_;
v___y_315_ = v___y_336_;
v___y_316_ = v___y_337_;
v___y_317_ = v___y_338_;
v___y_318_ = v___x_370_;
v___y_319_ = v___y_339_;
v___y_320_ = v___y_341_;
v___y_321_ = v___y_340_;
v___y_322_ = v___x_372_;
goto v___jp_311_;
}
else
{
v___y_312_ = v___y_334_;
v___y_313_ = v___y_333_;
v___y_314_ = v___y_335_;
v___y_315_ = v___y_336_;
v___y_316_ = v___y_337_;
v___y_317_ = v___y_338_;
v___y_318_ = v___x_370_;
v___y_319_ = v___y_339_;
v___y_320_ = v___y_341_;
v___y_321_ = v___y_340_;
v___y_322_ = v___x_372_;
goto v___jp_311_;
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_a_367_);
lean_dec(v_fst_365_);
lean_dec(v_currNamespace_349_);
lean_dec(v___y_342_);
lean_dec(v___y_340_);
lean_dec(v___y_339_);
lean_dec(v___y_338_);
lean_dec(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_334_);
v_a_374_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_368_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_368_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_fst_365_);
lean_dec(v_currNamespace_349_);
lean_dec(v___y_342_);
lean_dec(v___y_340_);
lean_dec(v___y_339_);
lean_dec(v___y_338_);
lean_dec(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_334_);
v_a_382_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_366_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_366_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v_a_345_);
lean_dec(v___y_343_);
lean_dec(v___y_342_);
lean_dec(v___y_340_);
lean_dec(v___y_339_);
lean_dec(v___y_338_);
lean_dec(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_334_);
v_a_390_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_346_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_346_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
v___jp_398_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v_suggestion_411_; lean_object* v___x_412_; lean_object* v___x_413_; size_t v_sz_414_; size_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_403_ = lean_unsigned_to_nat(2u);
v___x_404_ = l_Lean_Syntax_getArg(v_x_222_, v___x_403_);
v___x_405_ = lean_unsigned_to_nat(4u);
v___x_406_ = l_Lean_Syntax_getArg(v_x_222_, v___x_405_);
v___x_407_ = lean_unsigned_to_nat(6u);
v___x_408_ = l_Lean_Syntax_getArg(v_x_222_, v___x_407_);
v___x_409_ = lean_unsigned_to_nat(8u);
v___x_410_ = l_Lean_Syntax_getArg(v_x_222_, v___x_409_);
lean_dec(v_x_222_);
v_suggestion_411_ = l_Lean_Syntax_getArgs(v___x_406_);
lean_dec(v___x_406_);
v___x_412_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__13));
v___x_413_ = lean_box(0);
v_sz_414_ = lean_array_size(v_suggestion_411_);
v___x_415_ = ((size_t)0ULL);
lean_inc_ref(v_suggestion_411_);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3(v_sz_414_, v___x_415_, v_suggestion_411_);
v___x_417_ = lean_array_get_size(v___x_416_);
v___x_418_ = lean_nat_dec_lt(v___x_289_, v___x_417_);
if (v___x_418_ == 0)
{
lean_dec_ref(v___x_416_);
v___y_333_ = v___x_412_;
v___y_334_ = v_suggestion_411_;
v___y_335_ = v___y_402_;
v___y_336_ = v___x_410_;
v___y_337_ = v___x_404_;
v___y_338_ = v___y_399_;
v___y_339_ = v_attrs_x3f_400_;
v___y_340_ = v___x_408_;
v___y_341_ = v___y_401_;
v___y_342_ = v___x_413_;
v___y_343_ = v___x_413_;
goto v___jp_332_;
}
else
{
uint8_t v___x_419_; 
v___x_419_ = lean_nat_dec_le(v___x_417_, v___x_417_);
if (v___x_419_ == 0)
{
if (v___x_418_ == 0)
{
lean_dec_ref(v___x_416_);
v___y_333_ = v___x_412_;
v___y_334_ = v_suggestion_411_;
v___y_335_ = v___y_402_;
v___y_336_ = v___x_410_;
v___y_337_ = v___x_404_;
v___y_338_ = v___y_399_;
v___y_339_ = v_attrs_x3f_400_;
v___y_340_ = v___x_408_;
v___y_341_ = v___y_401_;
v___y_342_ = v___x_413_;
v___y_343_ = v___x_413_;
goto v___jp_332_;
}
else
{
size_t v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_usize_of_nat(v___x_417_);
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(v___x_416_, v___x_415_, v___x_420_, v___x_413_);
lean_dec_ref(v___x_416_);
v___y_333_ = v___x_412_;
v___y_334_ = v_suggestion_411_;
v___y_335_ = v___y_402_;
v___y_336_ = v___x_410_;
v___y_337_ = v___x_404_;
v___y_338_ = v___y_399_;
v___y_339_ = v_attrs_x3f_400_;
v___y_340_ = v___x_408_;
v___y_341_ = v___y_401_;
v___y_342_ = v___x_413_;
v___y_343_ = v___x_421_;
goto v___jp_332_;
}
}
else
{
size_t v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_usize_of_nat(v___x_417_);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(v___x_416_, v___x_415_, v___x_422_, v___x_413_);
lean_dec_ref(v___x_416_);
v___y_333_ = v___x_412_;
v___y_334_ = v_suggestion_411_;
v___y_335_ = v___y_402_;
v___y_336_ = v___x_410_;
v___y_337_ = v___x_404_;
v___y_338_ = v___y_399_;
v___y_339_ = v_attrs_x3f_400_;
v___y_340_ = v___x_408_;
v___y_341_ = v___y_401_;
v___y_342_ = v___x_413_;
v___y_343_ = v___x_423_;
goto v___jp_332_;
}
}
}
v___jp_424_:
{
lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = l_Lean_Syntax_getArg(v_x_222_, v___x_428_);
v___x_430_ = l_Lean_Syntax_isNone(v___x_429_);
if (v___x_430_ == 0)
{
uint8_t v___x_431_; 
lean_inc(v___x_429_);
v___x_431_ = l_Lean_Syntax_matchesNull(v___x_429_, v___x_428_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_dec(v___x_429_);
lean_dec(v_doc_x3f_425_);
lean_dec(v_x_222_);
v___x_432_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_432_;
}
else
{
lean_object* v_attrs_x3f_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_attrs_x3f_433_ = l_Lean_Syntax_getArg(v___x_429_, v___x_289_);
lean_dec(v___x_429_);
v___x_434_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__16));
lean_inc(v_attrs_x3f_433_);
v___x_435_ = l_Lean_Syntax_isOfKind(v_attrs_x3f_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
lean_dec(v_attrs_x3f_433_);
lean_dec(v_doc_x3f_425_);
lean_dec(v_x_222_);
v___x_436_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
return v___x_436_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v_attrs_x3f_433_);
v___y_399_ = v_doc_x3f_425_;
v_attrs_x3f_400_ = v___x_437_;
v___y_401_ = v___y_426_;
v___y_402_ = v___y_427_;
goto v___jp_398_;
}
}
}
else
{
lean_object* v___x_438_; 
lean_dec(v___x_429_);
v___x_438_ = lean_box(0);
v___y_399_ = v_doc_x3f_425_;
v_attrs_x3f_400_ = v___x_438_;
v___y_401_ = v___y_426_;
v___y_402_ = v___y_427_;
goto v___jp_398_;
}
}
}
v___jp_230_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_inc_ref_n(v___y_238_, 2);
v___x_246_ = l_Array_append___redArg(v___y_238_, v___y_245_);
lean_dec_ref(v___y_245_);
lean_inc_n(v___y_231_, 6);
lean_inc_n(v___y_241_, 17);
v___x_247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_247_, 0, v___y_241_);
lean_ctor_set(v___x_247_, 1, v___y_231_);
lean_ctor_set(v___x_247_, 2, v___x_246_);
v___x_248_ = l_Lean_Syntax_node1(v___y_241_, v___y_231_, v___y_236_);
v___x_249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_249_, 0, v___y_241_);
lean_ctor_set(v___x_249_, 1, v___y_231_);
lean_ctor_set(v___x_249_, 2, v___y_238_);
v___x_250_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__0));
lean_inc_ref_n(v___y_232_, 7);
v___x_251_ = l_Lean_Name_mkStr4(v___x_226_, v___y_232_, v___x_227_, v___x_250_);
v___x_252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_252_, 0, v___y_241_);
lean_ctor_set(v___x_252_, 1, v___x_250_);
v___x_253_ = l_Lean_Syntax_node1(v___y_241_, v___x_251_, v___x_252_);
v___x_254_ = l_Lean_Syntax_node1(v___y_241_, v___y_231_, v___x_253_);
lean_inc_ref_n(v___x_249_, 8);
v___x_255_ = l_Lean_Syntax_node7(v___y_241_, v___y_243_, v___y_235_, v___x_247_, v___x_248_, v___x_249_, v___x_254_, v___x_249_, v___x_249_);
v___x_256_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__1));
v___x_257_ = l_Lean_Name_mkStr4(v___x_226_, v___y_232_, v___x_227_, v___x_256_);
v___x_258_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__2));
v___x_259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_259_, 0, v___y_241_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__3));
v___x_261_ = l_Lean_Name_mkStr4(v___x_226_, v___y_232_, v___x_227_, v___x_260_);
v___x_262_ = lean_box(2);
v___x_263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___y_231_);
lean_ctor_set(v___x_263_, 2, v___y_233_);
v___x_264_ = l_Lean_mkIdentFrom(v___x_263_, v___y_237_, v___x_229_);
lean_dec_ref(v___x_263_);
v___x_265_ = l_Lean_Syntax_node2(v___y_241_, v___x_261_, v___x_264_, v___x_249_);
v___x_266_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__4));
v___x_267_ = l_Lean_Name_mkStr4(v___x_226_, v___y_232_, v___x_227_, v___x_266_);
v___x_268_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__14));
v___x_269_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__5));
v___x_270_ = l_Lean_Name_mkStr4(v___x_226_, v___y_232_, v___x_268_, v___x_269_);
v___x_271_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__33));
v___x_272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_272_, 0, v___y_241_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = l_Lean_Syntax_node2(v___y_241_, v___x_270_, v___x_272_, v___y_239_);
v___x_274_ = l_Lean_Syntax_node1(v___y_241_, v___y_231_, v___x_273_);
v___x_275_ = l_Lean_Syntax_node2(v___y_241_, v___x_267_, v___x_249_, v___x_274_);
v___x_276_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__6));
v___x_277_ = l_Lean_Name_mkStr4(v___x_226_, v___y_232_, v___x_227_, v___x_276_);
v___x_278_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__40));
v___x_279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_279_, 0, v___y_241_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__7));
v___x_281_ = ((lean_object*)(l_Lean_Elab_Command_elabAuxDef___closed__8));
v___x_282_ = l_Lean_Name_mkStr4(v___x_226_, v___y_232_, v___x_280_, v___x_281_);
v___x_283_ = l_Lean_Syntax_node2(v___y_241_, v___x_282_, v___x_249_, v___x_249_);
v___x_284_ = l_Lean_Syntax_node4(v___y_241_, v___x_277_, v___x_279_, v___y_244_, v___x_283_, v___x_249_);
v___x_285_ = l_Lean_Syntax_node5(v___y_241_, v___x_257_, v___x_259_, v___x_265_, v___x_275_, v___x_284_, v___x_249_);
v___x_286_ = l_Lean_Syntax_node2(v___y_241_, v___y_242_, v___x_255_, v___x_285_);
v___x_287_ = l_Lean_Elab_Command_elabCommand(v___x_286_, v___y_240_, v___y_234_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAuxDef___boxed(lean_object* v_x_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Elab_Command_elabAuxDef(v_x_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1(){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_462_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_463_ = ((lean_object*)(l_Lean_Elab_Command_aux__def___closed__4));
v___x_464_ = ((lean_object*)(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1));
v___x_465_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAuxDef___boxed), 4, 0);
v___x_466_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_462_, v___x_463_, v___x_464_, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___boxed(lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1();
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3(){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = ((lean_object*)(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1));
v___x_496_ = ((lean_object*)(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__6));
v___x_497_ = l_Lean_addBuiltinDeclarationRanges(v___x_495_, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___boxed(lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3();
return v_res_499_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
