// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.RegisterCommand
// Imports: public import Lean.Meta.Tactic.Simp.Attr public meta import Lean.Meta.Tactic.Simp.Simproc
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__0 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__1 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__1_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__2 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__2_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__3 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__3_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__4 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__5 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "registerSimpAttr"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__6 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_2),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(121, 136, 119, 43, 233, 213, 214, 52)}};
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_3),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 50, 187, 249, 139, 223, 179, 152)}};
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_4),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(101, 61, 117, 15, 84, 217, 39, 89)}};
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_6 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_5),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(172, 140, 142, 70, 253, 39, 136, 5)}};
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_6),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 241, 12, 130, 190, 87, 222, 88)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__7 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__7_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__8 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__9 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__9_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__10 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__11 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__11_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__12 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__13 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__13_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__14 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__11_value),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__14_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__15 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__15_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "register_simp_attr"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__16 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__16_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__17 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__9_value),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__15_value),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__17_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__18 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__18_value;
static const lean_string_object l_Lean_Parser_Command_registerSimpAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__19 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__19_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__20 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__20_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__21 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__9_value),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__18_value),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__21_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__22 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__22_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSimpAttr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__7_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__22_value)}};
static const lean_object* l_Lean_Parser_Command_registerSimpAttr___closed__23 = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__23_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Command_registerSimpAttr = (const lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__23_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 239, 30, 105, 8, 60, 178, 241)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stx_\?"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(19, 110, 207, 78, 164, 149, 1, 207)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(171, 185, 174, 62, 133, 84, 210, 196)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stx_<|>_"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(198, 97, 122, 56, 37, 186, 212, 102)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cat"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(95, 91, 11, 245, 227, 176, 7, 196)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Parser.Tactic.simpPre"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(46, 201, 23, 171, 41, 77, 220, 95)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(211, 17, 253, 157, 167, 104, 244, 4)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(84, 84, 229, 98, 67, 120, 70, 231)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<|>"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Parser.Tactic.simpPost"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(46, 201, 23, 171, 41, 77, 220, 95)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(211, 17, 253, 157, 167, 104, 244, 4)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(151, 85, 122, 79, 145, 83, 124, 126)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unicodeAtom"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(29, 147, 94, 13, 45, 35, 101, 109)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "unicode("};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = "\"← \""};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\"<- \""};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prio"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(122, 247, 65, 238, 243, 154, 137, 247)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "attr"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(69, 57, 207, 35, 177, 108, 73, 87)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_2),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "/--"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Simplification procedure -/"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extProc"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value),LEAN_SCALAR_PTR_LITERAL(153, 229, 121, 159, 4, 151, 74, 120)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SimprocExtension"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(48, 218, 30, 199, 10, 134, 135, 45)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(65, 33, 38, 245, 236, 63, 101, 240)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "registerSimprocAttr"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63_value),LEAN_SCALAR_PTR_LITERAL(153, 150, 186, 46, 228, 1, 156, 51)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63_value),LEAN_SCALAR_PTR_LITERAL(216, 40, 141, 126, 136, 240, 55, 143)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72_value),LEAN_SCALAR_PTR_LITERAL(124, 247, 59, 43, 44, 177, 111, 66)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "initializeKeyword"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value),LEAN_SCALAR_PTR_LITERAL(113, 140, 114, 135, 71, 133, 96, 5)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(241, 12, 90, 240, 78, 252, 149, 89)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SimpExtension"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83_value),LEAN_SCALAR_PTR_LITERAL(97, 27, 52, 253, 143, 150, 102, 25)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83_value),LEAN_SCALAR_PTR_LITERAL(180, 63, 186, 197, 159, 200, 30, 167)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87_value),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(71, 112, 199, 159, 165, 140, 183, 115)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(122, 223, 126, 22, 173, 44, 201, 149)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_1),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simproc set for "};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialize"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109_value),LEAN_SCALAR_PTR_LITERAL(55, 206, 156, 211, 241, 221, 187, 166)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_2),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value;
static lean_once_cell_t l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113;
static const lean_array_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115_value;
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(46, 201, 23, 171, 41, 77, 220, 95)}};
static const lean_ctor_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116_value_aux_0),((lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115_value),LEAN_SCALAR_PTR_LITERAL(10, 9, 185, 250, 127, 107, 245, 225)}};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116_value;
static const lean_string_object l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simp set for "};
static const lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117 = (const lean_object*)&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0));
v___x_53_ = l_String_toRawSubstring_x27(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25));
v___x_104_ = l_String_toRawSubstring_x27(v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32));
v___x_119_ = l_String_toRawSubstring_x27(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46));
v___x_146_ = l_String_toRawSubstring_x27(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49));
v___x_151_ = l_String_toRawSubstring_x27(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55));
v___x_163_ = l_String_toRawSubstring_x27(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58));
v___x_168_ = l_String_toRawSubstring_x27(v___x_167_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63));
v___x_180_ = l_String_toRawSubstring_x27(v___x_179_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76));
v___x_211_ = l_String_toRawSubstring_x27(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83));
v___x_224_ = l_String_toRawSubstring_x27(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__6));
v___x_268_ = l_String_toRawSubstring_x27(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113(void){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Array_mkArray0(lean_box(0));
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1(lean_object* v_x_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_383_ = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__0));
v___x_384_ = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__4));
v___x_634_ = ((lean_object*)(l_Lean_Parser_Command_registerSimpAttr___closed__7));
lean_inc(v_x_310_);
v___x_635_ = l_Lean_Syntax_isOfKind(v_x_310_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec(v_x_310_);
v___x_636_ = lean_box(1);
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_a_312_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v_id_641_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_675_; lean_object* v___x_686_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = l_Lean_Syntax_getArg(v_x_310_, v___x_638_);
v___x_640_ = lean_unsigned_to_nat(2u);
v_id_641_ = l_Lean_Syntax_getArg(v_x_310_, v___x_640_);
lean_dec(v_x_310_);
v___x_686_ = l_Lean_Syntax_getOptional_x3f(v___x_639_);
lean_dec(v___x_639_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v___x_687_; 
v___x_687_ = lean_box(0);
v___y_675_ = v___x_687_;
goto v___jp_674_;
}
else
{
lean_object* v_val_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
v_val_688_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_686_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_val_688_);
lean_dec(v___x_686_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_val_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
v___y_675_ = v___x_693_;
goto v___jp_674_;
}
}
}
v___jp_642_:
{
lean_object* v_quotContext_650_; lean_object* v_currMacroScope_651_; lean_object* v_ref_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_procId_657_; lean_object* v___x_658_; lean_object* v_procStr_659_; lean_object* v___x_660_; lean_object* v_procIdParser_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_quotContext_650_ = lean_ctor_get(v_a_311_, 1);
v_currMacroScope_651_ = lean_ctor_get(v_a_311_, 2);
v_ref_652_ = lean_ctor_get(v_a_311_, 5);
v___x_653_ = l_String_removeLeadingSpaces(v___y_649_);
v___x_654_ = lean_box(2);
v___x_655_ = l_Lean_Syntax_mkStrLit(v___x_653_, v___x_654_);
lean_inc(v___y_648_);
v___x_656_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v___y_648_);
v_procId_657_ = l_Lean_mkIdentFrom(v_id_641_, v___x_656_, v___y_647_);
lean_dec(v_id_641_);
v___x_658_ = l_Lean_TSyntax_getId(v_procId_657_);
lean_inc_n(v___x_658_, 2);
v_procStr_659_ = l_Lean_Name_toString(v___x_658_, v___x_635_);
v___x_660_ = l_Lean_Name_append(v___y_646_, v___x_658_);
v_procIdParser_661_ = l_Lean_mkIdentFrom(v_procId_657_, v___x_660_, v___y_647_);
lean_dec(v_procId_657_);
v___x_662_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106));
v___x_663_ = lean_string_append(v___x_662_, v_procStr_659_);
v___x_664_ = l_Lean_Syntax_mkStrLit(v___x_663_, v___x_654_);
v___x_665_ = l_Lean_SourceInfo_fromRef(v_ref_652_, v___y_647_);
v___x_666_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108));
v___x_667_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109));
v___x_668_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110));
v___x_669_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112));
v___x_670_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113);
if (lean_obj_tag(v___y_645_) == 1)
{
lean_object* v_val_671_; lean_object* v___x_672_; 
v_val_671_ = lean_ctor_get(v___y_645_, 0);
lean_inc(v_val_671_);
lean_dec_ref(v___y_645_);
v___x_672_ = l_Array_mkArray1___redArg(v_val_671_);
v___y_559_ = v___y_643_;
v___y_560_ = v___x_658_;
v___y_561_ = v___x_669_;
v___y_562_ = v___x_655_;
v___y_563_ = v_currMacroScope_651_;
v___y_564_ = v___x_664_;
v___y_565_ = v___x_666_;
v___y_566_ = v_procStr_659_;
v___y_567_ = v___y_644_;
v___y_568_ = v_quotContext_650_;
v___y_569_ = v___x_667_;
v___y_570_ = v___x_668_;
v___y_571_ = v___x_670_;
v___y_572_ = v___x_665_;
v___y_573_ = v___y_648_;
v___y_574_ = v_procIdParser_661_;
v___y_575_ = v___x_654_;
v___y_576_ = v___x_672_;
goto v___jp_558_;
}
else
{
lean_object* v___x_673_; 
lean_dec(v___y_645_);
v___x_673_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114));
v___y_559_ = v___y_643_;
v___y_560_ = v___x_658_;
v___y_561_ = v___x_669_;
v___y_562_ = v___x_655_;
v___y_563_ = v_currMacroScope_651_;
v___y_564_ = v___x_664_;
v___y_565_ = v___x_666_;
v___y_566_ = v_procStr_659_;
v___y_567_ = v___y_644_;
v___y_568_ = v_quotContext_650_;
v___y_569_ = v___x_667_;
v___y_570_ = v___x_668_;
v___y_571_ = v___x_670_;
v___y_572_ = v___x_665_;
v___y_573_ = v___y_648_;
v___y_574_ = v_procIdParser_661_;
v___y_575_ = v___x_654_;
v___y_576_ = v___x_673_;
goto v___jp_558_;
}
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v_str_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; lean_object* v_idParser_681_; 
v___x_676_ = l_Lean_TSyntax_getId(v_id_641_);
lean_inc_n(v___x_676_, 2);
v_str_677_ = l_Lean_Name_toString(v___x_676_, v___x_635_);
v___x_678_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116));
v___x_679_ = l_Lean_Name_append(v___x_678_, v___x_676_);
v___x_680_ = 0;
v_idParser_681_ = l_Lean_mkIdentFrom(v_id_641_, v___x_679_, v___x_680_);
if (lean_obj_tag(v___y_675_) == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117));
v___x_683_ = lean_string_append(v___x_682_, v_str_677_);
v___y_643_ = v_str_677_;
v___y_644_ = v_idParser_681_;
v___y_645_ = v___y_675_;
v___y_646_ = v___x_678_;
v___y_647_ = v___x_680_;
v___y_648_ = v___x_676_;
v___y_649_ = v___x_683_;
goto v___jp_642_;
}
else
{
lean_object* v_val_684_; lean_object* v___x_685_; 
v_val_684_ = lean_ctor_get(v___y_675_, 0);
v___x_685_ = l_Lean_TSyntax_getDocString(v_val_684_);
v___y_643_ = v_str_677_;
v___y_644_ = v_idParser_681_;
v___y_645_ = v___y_675_;
v___y_646_ = v___x_678_;
v___y_647_ = v___x_680_;
v___y_648_ = v___x_676_;
v___y_649_ = v___x_685_;
goto v___jp_642_;
}
}
}
v___jp_313_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_351_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1);
v___x_352_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2));
lean_inc(v___y_338_);
lean_inc(v___y_326_);
v___x_353_ = l_Lean_addMacroScope(v___y_326_, v___x_352_, v___y_338_);
v___x_354_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4));
v___x_355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___y_317_);
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___y_327_);
lean_inc_n(v___y_329_, 13);
v___x_357_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_357_, 0, v___y_329_);
lean_ctor_set(v___x_357_, 1, v___x_351_);
lean_ctor_set(v___x_357_, 2, v___x_353_);
lean_ctor_set(v___x_357_, 3, v___x_356_);
lean_inc_n(v___y_321_, 5);
v___x_358_ = l_Lean_Syntax_node3(v___y_329_, v___y_321_, v___y_350_, v___y_339_, v___x_357_);
lean_inc(v___y_331_);
v___x_359_ = l_Lean_Syntax_node2(v___y_329_, v___y_331_, v___y_319_, v___x_358_);
lean_inc(v___y_325_);
v___x_360_ = l_Lean_Syntax_node1(v___y_329_, v___y_325_, v___x_359_);
lean_inc_n(v___y_337_, 3);
lean_inc(v___y_336_);
v___x_361_ = l_Lean_Syntax_node2(v___y_329_, v___y_336_, v___x_360_, v___y_337_);
v___x_362_ = l_Lean_Syntax_node1(v___y_329_, v___y_321_, v___x_361_);
lean_inc(v___y_322_);
v___x_363_ = l_Lean_Syntax_node1(v___y_329_, v___y_322_, v___x_362_);
lean_inc(v___y_345_);
v___x_364_ = l_Lean_Syntax_node4(v___y_329_, v___y_345_, v___y_323_, v___y_330_, v___y_314_, v___x_363_);
v___x_365_ = l_Lean_Syntax_node5(v___y_329_, v___y_332_, v___y_349_, v___y_335_, v___y_342_, v___y_348_, v___y_320_);
v___x_366_ = l_Lean_Syntax_node1(v___y_329_, v___y_321_, v___x_365_);
v___x_367_ = l_Lean_Syntax_mkStrLit(v___y_324_, v___y_333_);
v___x_368_ = l_Lean_Syntax_node1(v___y_329_, v___y_315_, v___x_367_);
v___x_369_ = l_Lean_Syntax_node2(v___y_329_, v___y_321_, v___x_368_, v___y_341_);
v___x_370_ = lean_array_push(v___y_328_, v___y_343_);
v___x_371_ = lean_array_push(v___x_370_, v___y_337_);
v___x_372_ = lean_array_push(v___x_371_, v___y_346_);
v___x_373_ = lean_array_push(v___x_372_, v___y_340_);
v___x_374_ = lean_array_push(v___x_373_, v___y_337_);
v___x_375_ = lean_array_push(v___x_374_, v___x_366_);
v___x_376_ = lean_array_push(v___x_375_, v___y_337_);
v___x_377_ = lean_array_push(v___x_376_, v___x_369_);
v___x_378_ = lean_array_push(v___x_377_, v___y_318_);
v___x_379_ = lean_array_push(v___x_378_, v___y_347_);
lean_inc(v___y_334_);
v___x_380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_380_, 0, v___y_329_);
lean_ctor_set(v___x_380_, 1, v___y_334_);
lean_ctor_set(v___x_380_, 2, v___x_379_);
v___x_381_ = l_Lean_Syntax_node4(v___y_329_, v___y_321_, v___y_316_, v___y_344_, v___x_364_, v___x_380_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_a_312_);
return v___x_382_;
}
v___jp_385_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
lean_inc_n(v___y_392_, 8);
lean_inc_n(v___y_399_, 52);
v___x_419_ = l_Lean_Syntax_node2(v___y_399_, v___y_392_, v___y_418_, v___y_408_);
lean_inc(v___y_403_);
v___x_420_ = l_Lean_Syntax_node2(v___y_399_, v___y_403_, v___y_386_, v___x_419_);
lean_inc(v___y_396_);
v___x_421_ = l_Lean_Syntax_node1(v___y_399_, v___y_396_, v___x_420_);
lean_inc_n(v___y_410_, 13);
lean_inc(v___y_409_);
v___x_422_ = l_Lean_Syntax_node2(v___y_399_, v___y_409_, v___x_421_, v___y_410_);
v___x_423_ = l_Lean_Syntax_node1(v___y_399_, v___y_392_, v___x_422_);
lean_inc(v___y_395_);
v___x_424_ = l_Lean_Syntax_node1(v___y_399_, v___y_395_, v___x_423_);
lean_inc(v___y_402_);
lean_inc(v___y_416_);
v___x_425_ = l_Lean_Syntax_node4(v___y_399_, v___y_416_, v___y_400_, v___y_402_, v___y_391_, v___x_424_);
v___x_426_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5));
v___x_427_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6));
v___x_428_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7));
lean_inc_ref(v___y_412_);
v___x_429_ = l_Lean_Name_mkStr4(v___x_383_, v___x_384_, v___y_412_, v___x_428_);
v___x_430_ = l_Lean_Syntax_node1(v___y_399_, v___x_429_, v___y_410_);
v___x_431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_431_, 0, v___y_399_);
lean_ctor_set(v___x_431_, 1, v___x_426_);
v___x_432_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9));
v___x_433_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10));
v___x_434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_434_, 0, v___y_399_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11));
v___x_436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_436_, 0, v___y_399_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12));
v___x_438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_438_, 0, v___y_399_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13));
v___x_440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_440_, 0, v___y_399_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
lean_inc_ref_n(v___x_440_, 4);
lean_inc_ref(v___x_438_);
lean_inc_ref(v___x_436_);
lean_inc_ref_n(v___x_434_, 3);
v___x_441_ = l_Lean_Syntax_node5(v___y_399_, v___x_432_, v___x_434_, v___x_436_, v___x_438_, v___y_415_, v___x_440_);
v___x_442_ = l_Lean_Syntax_node1(v___y_399_, v___y_392_, v___x_441_);
v___x_443_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16));
lean_inc(v___y_404_);
v___x_444_ = l_Lean_Syntax_mkStrLit(v___y_405_, v___y_404_);
v___x_445_ = l_Lean_Syntax_node1(v___y_399_, v___x_443_, v___x_444_);
v___x_446_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18));
v___x_447_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20));
v___x_448_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22));
v___x_449_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24));
v___x_450_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26);
v___x_451_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29));
lean_inc_n(v___y_413_, 7);
lean_inc_n(v___y_397_, 7);
v___x_452_ = l_Lean_addMacroScope(v___y_397_, v___x_451_, v___y_413_);
v___x_453_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30));
lean_inc_n(v___y_389_, 5);
v___x_454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___y_389_);
lean_inc_n(v___y_398_, 7);
v___x_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___y_398_);
v___x_456_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_456_, 0, v___y_399_);
lean_ctor_set(v___x_456_, 1, v___x_450_);
lean_ctor_set(v___x_456_, 2, v___x_452_);
lean_ctor_set(v___x_456_, 3, v___x_455_);
v___x_457_ = l_Lean_Syntax_node2(v___y_399_, v___x_449_, v___x_456_, v___y_410_);
v___x_458_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31));
v___x_459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_459_, 0, v___y_399_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33);
v___x_461_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35));
v___x_462_ = l_Lean_addMacroScope(v___y_397_, v___x_461_, v___y_413_);
v___x_463_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36));
v___x_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___y_389_);
v___x_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___y_398_);
v___x_466_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_466_, 0, v___y_399_);
lean_ctor_set(v___x_466_, 1, v___x_460_);
lean_ctor_set(v___x_466_, 2, v___x_462_);
lean_ctor_set(v___x_466_, 3, v___x_465_);
v___x_467_ = l_Lean_Syntax_node2(v___y_399_, v___x_449_, v___x_466_, v___y_410_);
v___x_468_ = l_Lean_Syntax_node3(v___y_399_, v___x_448_, v___x_457_, v___x_459_, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v___y_399_, v___y_392_, v___x_468_);
v___x_470_ = l_Lean_Syntax_node3(v___y_399_, v___x_447_, v___x_434_, v___x_469_, v___x_440_);
v___x_471_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37));
v___x_472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_472_, 0, v___y_399_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
lean_inc_ref_n(v___x_472_, 2);
v___x_473_ = l_Lean_Syntax_node2(v___y_399_, v___x_446_, v___x_470_, v___x_472_);
v___x_474_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39));
v___x_475_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40));
v___x_476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_476_, 0, v___y_399_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42));
v___x_478_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43));
v___x_479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_479_, 0, v___y_399_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = l_Lean_Syntax_node1(v___y_399_, v___x_477_, v___x_479_);
v___x_481_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44));
v___x_482_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_482_, 0, v___y_399_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45));
v___x_484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_484_, 0, v___y_399_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = l_Lean_Syntax_node1(v___y_399_, v___x_477_, v___x_484_);
v___x_486_ = l_Lean_Syntax_node6(v___y_399_, v___x_474_, v___x_476_, v___x_480_, v___x_482_, v___x_485_, v___y_410_, v___x_440_);
v___x_487_ = l_Lean_Syntax_node2(v___y_399_, v___x_446_, v___x_486_, v___x_472_);
v___x_488_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47);
v___x_489_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48));
v___x_490_ = l_Lean_addMacroScope(v___y_397_, v___x_489_, v___y_413_);
v___x_491_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_491_, 0, v___y_399_);
lean_ctor_set(v___x_491_, 1, v___x_488_);
lean_ctor_set(v___x_491_, 2, v___x_490_);
lean_ctor_set(v___x_491_, 3, v___y_398_);
v___x_492_ = l_Lean_Syntax_node2(v___y_399_, v___x_449_, v___x_491_, v___y_410_);
v___x_493_ = l_Lean_Syntax_node1(v___y_399_, v___y_392_, v___x_492_);
v___x_494_ = l_Lean_Syntax_node3(v___y_399_, v___x_447_, v___x_434_, v___x_493_, v___x_440_);
v___x_495_ = l_Lean_Syntax_node2(v___y_399_, v___x_446_, v___x_494_, v___x_472_);
lean_inc(v___x_473_);
v___x_496_ = l_Lean_Syntax_node4(v___y_399_, v___y_392_, v___x_445_, v___x_473_, v___x_487_, v___x_495_);
v___x_497_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50);
v___x_498_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51));
v___x_499_ = l_Lean_addMacroScope(v___y_397_, v___x_498_, v___y_413_);
v___x_500_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_500_, 0, v___y_399_);
lean_ctor_set(v___x_500_, 1, v___x_497_);
lean_ctor_set(v___x_500_, 2, v___x_499_);
lean_ctor_set(v___x_500_, 3, v___y_398_);
v___x_501_ = lean_unsigned_to_nat(10u);
v___x_502_ = lean_mk_empty_array_with_capacity(v___x_501_);
lean_inc_ref(v___x_502_);
v___x_503_ = lean_array_push(v___x_502_, v___y_406_);
v___x_504_ = lean_array_push(v___x_503_, v___y_410_);
lean_inc(v___x_430_);
v___x_505_ = lean_array_push(v___x_504_, v___x_430_);
lean_inc_ref(v___x_431_);
v___x_506_ = lean_array_push(v___x_505_, v___x_431_);
v___x_507_ = lean_array_push(v___x_506_, v___y_410_);
v___x_508_ = lean_array_push(v___x_507_, v___x_442_);
v___x_509_ = lean_array_push(v___x_508_, v___y_410_);
v___x_510_ = lean_array_push(v___x_509_, v___x_496_);
lean_inc_n(v___y_390_, 2);
v___x_511_ = lean_array_push(v___x_510_, v___y_390_);
lean_inc_ref(v___x_500_);
v___x_512_ = lean_array_push(v___x_511_, v___x_500_);
v___x_513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_513_, 0, v___y_399_);
lean_ctor_set(v___x_513_, 1, v___x_427_);
lean_ctor_set(v___x_513_, 2, v___x_512_);
v___x_514_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52));
v___x_515_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53));
v___x_516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_516_, 0, v___y_399_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54));
v___x_518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_518_, 0, v___y_399_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = l_Lean_Syntax_node2(v___y_399_, v___x_514_, v___x_516_, v___x_518_);
v___x_520_ = l_Lean_Syntax_node1(v___y_399_, v___y_392_, v___x_519_);
lean_inc(v___x_520_);
lean_inc(v___y_387_);
v___x_521_ = l_Lean_Syntax_node7(v___y_399_, v___y_387_, v___x_520_, v___y_410_, v___y_388_, v___y_410_, v___y_411_, v___y_410_, v___y_410_);
v___x_522_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56);
v___x_523_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57));
v___x_524_ = l_Lean_addMacroScope(v___y_397_, v___x_523_, v___y_413_);
v___x_525_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_525_, 0, v___y_399_);
lean_ctor_set(v___x_525_, 1, v___x_522_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
lean_ctor_set(v___x_525_, 3, v___y_398_);
v___x_526_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59);
v___x_527_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60));
v___x_528_ = l_Lean_addMacroScope(v___y_397_, v___x_527_, v___y_413_);
v___x_529_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61));
v___x_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___y_389_);
v___x_531_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62));
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v___y_398_);
v___x_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_530_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_534_, 0, v___y_399_);
lean_ctor_set(v___x_534_, 1, v___x_526_);
lean_ctor_set(v___x_534_, 2, v___x_528_);
lean_ctor_set(v___x_534_, 3, v___x_533_);
v___x_535_ = l_Lean_Syntax_node2(v___y_399_, v___y_401_, v___y_390_, v___x_534_);
v___x_536_ = l_Lean_Syntax_node3(v___y_399_, v___y_392_, v___x_525_, v___x_535_, v___y_394_);
v___x_537_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64);
v___x_538_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65));
v___x_539_ = l_Lean_addMacroScope(v___y_397_, v___x_538_, v___y_413_);
v___x_540_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66));
v___x_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___y_389_);
v___x_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___y_398_);
v___x_543_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_543_, 0, v___y_399_);
lean_ctor_set(v___x_543_, 1, v___x_537_);
lean_ctor_set(v___x_543_, 2, v___x_539_);
lean_ctor_set(v___x_543_, 3, v___x_542_);
lean_inc(v___y_407_);
v___x_544_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___y_389_, v___y_407_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_quoteNameMk(v___y_407_);
v___y_314_ = v___x_536_;
v___y_315_ = v___x_443_;
v___y_316_ = v___x_425_;
v___y_317_ = v___y_389_;
v___y_318_ = v___y_390_;
v___y_319_ = v___x_543_;
v___y_320_ = v___x_440_;
v___y_321_ = v___y_392_;
v___y_322_ = v___y_395_;
v___y_323_ = v___x_521_;
v___y_324_ = v___y_393_;
v___y_325_ = v___y_396_;
v___y_326_ = v___y_397_;
v___y_327_ = v___y_398_;
v___y_328_ = v___x_502_;
v___y_329_ = v___y_399_;
v___y_330_ = v___y_402_;
v___y_331_ = v___y_403_;
v___y_332_ = v___x_432_;
v___y_333_ = v___y_404_;
v___y_334_ = v___x_427_;
v___y_335_ = v___x_436_;
v___y_336_ = v___y_409_;
v___y_337_ = v___y_410_;
v___y_338_ = v___y_413_;
v___y_339_ = v___y_414_;
v___y_340_ = v___x_431_;
v___y_341_ = v___x_473_;
v___y_342_ = v___x_438_;
v___y_343_ = v___x_520_;
v___y_344_ = v___x_513_;
v___y_345_ = v___y_416_;
v___y_346_ = v___x_430_;
v___y_347_ = v___x_500_;
v___y_348_ = v___y_417_;
v___y_349_ = v___x_434_;
v___y_350_ = v___x_545_;
goto v___jp_313_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v___y_407_);
v_val_546_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_val_546_);
lean_dec_ref(v___x_544_);
v___x_547_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67));
lean_inc_ref(v___y_412_);
v___x_548_ = l_Lean_Name_mkStr4(v___x_383_, v___x_384_, v___y_412_, v___x_547_);
v___x_549_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68));
v___x_550_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69));
v___x_551_ = lean_string_intercalate(v___x_550_, v_val_546_);
v___x_552_ = lean_string_append(v___x_549_, v___x_551_);
lean_dec_ref(v___x_551_);
lean_inc_n(v___y_404_, 2);
v___x_553_ = l_Lean_Syntax_mkNameLit(v___x_552_, v___y_404_);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_mk_empty_array_with_capacity(v___x_554_);
v___x_556_ = lean_array_push(v___x_555_, v___x_553_);
v___x_557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_557_, 0, v___y_404_);
lean_ctor_set(v___x_557_, 1, v___x_548_);
lean_ctor_set(v___x_557_, 2, v___x_556_);
v___y_314_ = v___x_536_;
v___y_315_ = v___x_443_;
v___y_316_ = v___x_425_;
v___y_317_ = v___y_389_;
v___y_318_ = v___y_390_;
v___y_319_ = v___x_543_;
v___y_320_ = v___x_440_;
v___y_321_ = v___y_392_;
v___y_322_ = v___y_395_;
v___y_323_ = v___x_521_;
v___y_324_ = v___y_393_;
v___y_325_ = v___y_396_;
v___y_326_ = v___y_397_;
v___y_327_ = v___y_398_;
v___y_328_ = v___x_502_;
v___y_329_ = v___y_399_;
v___y_330_ = v___y_402_;
v___y_331_ = v___y_403_;
v___y_332_ = v___x_432_;
v___y_333_ = v___y_404_;
v___y_334_ = v___x_427_;
v___y_335_ = v___x_436_;
v___y_336_ = v___y_409_;
v___y_337_ = v___y_410_;
v___y_338_ = v___y_413_;
v___y_339_ = v___y_414_;
v___y_340_ = v___x_431_;
v___y_341_ = v___x_473_;
v___y_342_ = v___x_438_;
v___y_343_ = v___x_520_;
v___y_344_ = v___x_513_;
v___y_345_ = v___y_416_;
v___y_346_ = v___x_430_;
v___y_347_ = v___x_500_;
v___y_348_ = v___y_417_;
v___y_349_ = v___x_434_;
v___y_350_ = v___x_557_;
goto v___jp_313_;
}
}
v___jp_558_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_inc_ref_n(v___y_571_, 2);
v___x_577_ = l_Array_append___redArg(v___y_571_, v___y_576_);
lean_dec_ref(v___y_576_);
lean_inc_n(v___y_565_, 5);
lean_inc_n(v___y_572_, 18);
v___x_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_578_, 0, v___y_572_);
lean_ctor_set(v___x_578_, 1, v___y_565_);
lean_ctor_set(v___x_578_, 2, v___x_577_);
v___x_579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_579_, 0, v___y_572_);
lean_ctor_set(v___x_579_, 1, v___y_565_);
lean_ctor_set(v___x_579_, 2, v___y_571_);
v___x_580_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70));
v___x_581_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71));
v___x_582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_582_, 0, v___y_572_);
lean_ctor_set(v___x_582_, 1, v___x_580_);
v___x_583_ = l_Lean_Syntax_node1(v___y_572_, v___x_581_, v___x_582_);
v___x_584_ = l_Lean_Syntax_node1(v___y_572_, v___y_565_, v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72));
v___x_586_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73));
v___x_587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_587_, 0, v___y_572_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
v___x_588_ = l_Lean_Syntax_node1(v___y_572_, v___x_586_, v___x_587_);
v___x_589_ = l_Lean_Syntax_node1(v___y_572_, v___y_565_, v___x_588_);
lean_inc(v___x_589_);
lean_inc(v___x_584_);
lean_inc_ref_n(v___x_579_, 4);
lean_inc_ref(v___x_578_);
lean_inc(v___y_561_);
v___x_590_ = l_Lean_Syntax_node7(v___y_572_, v___y_561_, v___x_578_, v___x_579_, v___x_584_, v___x_579_, v___x_589_, v___x_579_, v___x_579_);
v___x_591_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75));
lean_inc_ref(v___y_569_);
v___x_592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_592_, 0, v___y_572_);
lean_ctor_set(v___x_592_, 1, v___y_569_);
v___x_593_ = l_Lean_Syntax_node1(v___y_572_, v___x_591_, v___x_592_);
v___x_594_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77);
v___x_595_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78));
lean_inc_n(v___y_563_, 3);
lean_inc_n(v___y_568_, 3);
v___x_596_ = l_Lean_addMacroScope(v___y_568_, v___x_595_, v___y_563_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_598_, 0, v___y_572_);
lean_ctor_set(v___x_598_, 1, v___x_594_);
lean_ctor_set(v___x_598_, 2, v___x_596_);
lean_ctor_set(v___x_598_, 3, v___x_597_);
v___x_599_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79));
v___x_600_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81));
v___x_601_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82));
v___x_602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_602_, 0, v___y_572_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84);
v___x_604_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85));
v___x_605_ = l_Lean_addMacroScope(v___y_568_, v___x_604_, v___y_563_);
v___x_606_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90));
v___x_607_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_607_, 0, v___y_572_);
lean_ctor_set(v___x_607_, 1, v___x_603_);
lean_ctor_set(v___x_607_, 2, v___x_605_);
lean_ctor_set(v___x_607_, 3, v___x_606_);
lean_inc_ref(v___x_602_);
v___x_608_ = l_Lean_Syntax_node2(v___y_572_, v___x_600_, v___x_602_, v___x_607_);
v___x_609_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91));
v___x_610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_610_, 0, v___y_572_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
lean_inc_ref(v___x_610_);
v___x_611_ = l_Lean_Syntax_node3(v___y_572_, v___y_565_, v___x_598_, v___x_608_, v___x_610_);
v___x_612_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93));
v___x_613_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95));
v___x_614_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97));
v___x_615_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99));
v___x_616_ = lean_obj_once(&l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100, &l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100_once, _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100);
v___x_617_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101));
v___x_618_ = l_Lean_addMacroScope(v___y_568_, v___x_617_, v___y_563_);
v___x_619_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104));
v___x_620_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_620_, 0, v___y_572_);
lean_ctor_set(v___x_620_, 1, v___x_616_);
lean_ctor_set(v___x_620_, 2, v___x_618_);
lean_ctor_set(v___x_620_, 3, v___x_619_);
lean_inc(v___y_573_);
v___x_621_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_597_, v___y_573_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_quoteNameMk(v___y_573_);
v___y_386_ = v___x_620_;
v___y_387_ = v___y_561_;
v___y_388_ = v___x_584_;
v___y_389_ = v___x_597_;
v___y_390_ = v___x_602_;
v___y_391_ = v___x_611_;
v___y_392_ = v___y_565_;
v___y_393_ = v___y_566_;
v___y_394_ = v___x_610_;
v___y_395_ = v___x_612_;
v___y_396_ = v___x_614_;
v___y_397_ = v___y_568_;
v___y_398_ = v___x_597_;
v___y_399_ = v___y_572_;
v___y_400_ = v___x_590_;
v___y_401_ = v___x_600_;
v___y_402_ = v___x_593_;
v___y_403_ = v___x_615_;
v___y_404_ = v___y_575_;
v___y_405_ = v___y_559_;
v___y_406_ = v___x_578_;
v___y_407_ = v___y_560_;
v___y_408_ = v___y_562_;
v___y_409_ = v___x_613_;
v___y_410_ = v___x_579_;
v___y_411_ = v___x_589_;
v___y_412_ = v___x_599_;
v___y_413_ = v___y_563_;
v___y_414_ = v___y_564_;
v___y_415_ = v___y_567_;
v___y_416_ = v___y_570_;
v___y_417_ = v___y_574_;
v___y_418_ = v___x_622_;
goto v___jp_385_;
}
else
{
lean_object* v_val_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v___y_573_);
v_val_623_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_val_623_);
lean_dec_ref(v___x_621_);
v___x_624_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105));
v___x_625_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68));
v___x_626_ = ((lean_object*)(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69));
v___x_627_ = lean_string_intercalate(v___x_626_, v_val_623_);
v___x_628_ = lean_string_append(v___x_625_, v___x_627_);
lean_dec_ref(v___x_627_);
lean_inc_n(v___y_575_, 2);
v___x_629_ = l_Lean_Syntax_mkNameLit(v___x_628_, v___y_575_);
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_mk_empty_array_with_capacity(v___x_630_);
v___x_632_ = lean_array_push(v___x_631_, v___x_629_);
v___x_633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_633_, 0, v___y_575_);
lean_ctor_set(v___x_633_, 1, v___x_624_);
lean_ctor_set(v___x_633_, 2, v___x_632_);
v___y_386_ = v___x_620_;
v___y_387_ = v___y_561_;
v___y_388_ = v___x_584_;
v___y_389_ = v___x_597_;
v___y_390_ = v___x_602_;
v___y_391_ = v___x_611_;
v___y_392_ = v___y_565_;
v___y_393_ = v___y_566_;
v___y_394_ = v___x_610_;
v___y_395_ = v___x_612_;
v___y_396_ = v___x_614_;
v___y_397_ = v___y_568_;
v___y_398_ = v___x_597_;
v___y_399_ = v___y_572_;
v___y_400_ = v___x_590_;
v___y_401_ = v___x_600_;
v___y_402_ = v___x_593_;
v___y_403_ = v___x_615_;
v___y_404_ = v___y_575_;
v___y_405_ = v___y_559_;
v___y_406_ = v___x_578_;
v___y_407_ = v___y_560_;
v___y_408_ = v___y_562_;
v___y_409_ = v___x_613_;
v___y_410_ = v___x_579_;
v___y_411_ = v___x_589_;
v___y_412_ = v___x_599_;
v___y_413_ = v___y_563_;
v___y_414_ = v___y_564_;
v___y_415_ = v___y_567_;
v___y_416_ = v___y_570_;
v___y_417_ = v___y_574_;
v___y_418_ = v___x_633_;
goto v___jp_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___boxed(lean_object* v_x_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1(v_x_696_, v_a_697_, v_a_698_);
lean_dec_ref(v_a_697_);
return v_res_699_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
}
#ifdef __cplusplus
}
#endif
