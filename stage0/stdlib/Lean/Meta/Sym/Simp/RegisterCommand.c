// Lean compiler output
// Module: Lean.Meta.Sym.Simp.RegisterCommand
// Imports: public import Lean.Meta.Sym.Simp.Attr public import Lean.Meta.Sym.Simp.Variant public meta import Init.Data.ToString.Name public meta import Init.Data.String.Extra
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__0 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__1 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__1_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__2 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__1_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__3 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__3_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__4 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__3_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__5 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__5_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__6 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__5_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__7 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__7_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__8 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__7_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(216, 103, 67, 80, 248, 223, 51, 5)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__9 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__9_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 127, 193, 190, 4, 122, 249, 96)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__10 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__10_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__11 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__10_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(76, 77, 233, 157, 88, 19, 246, 173)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__12 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__12_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__13 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__12_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(249, 230, 147, 137, 253, 214, 10, 230)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__14 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__14_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "registerSymSimpAttr"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__15 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__14_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__15_value),LEAN_SCALAR_PTR_LITERAL(89, 239, 54, 61, 160, 98, 3, 108)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__16 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__16_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__17 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__17_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__18 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__18_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__19 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__19_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__20 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__20_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__21 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__21_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__22 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__22_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__22_value)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__23 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__20_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__23_value)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__24 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__24_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "register_sym_simp_attr"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__25 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__25_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__25_value)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__26 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__26_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__18_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__24_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__26_value)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__27 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__27_value;
static const lean_string_object l_Lean_Parser_Command_registerSymSimpAttr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__28 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__28_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__29 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__29_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__29_value)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__30 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__30_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__18_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__27_value),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__30_value)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__31 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__31_value;
static const lean_ctor_object l_Lean_Parser_Command_registerSymSimpAttr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__16_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__31_value)}};
static const lean_object* l_Lean_Parser_Command_registerSymSimpAttr___closed__32 = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__32_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Command_registerSymSimpAttr = (const lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__32_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__6_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__7_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__8_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__9_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "attr"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(69, 57, 207, 35, 177, 108, 73, 87)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__14 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__14_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(124, 247, 59, 43, 44, 177, 111, 66)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "initializeKeyword"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__19 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(113, 140, 114, 135, 71, 133, 96, 5)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__21_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(241, 12, 90, 240, 78, 252, 149, 89)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__23 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__23_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__25 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__27 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__27_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SymSimpExtension"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(254, 56, 105, 241, 24, 189, 70, 146)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__30 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_2),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(30, 17, 47, 177, 215, 245, 56, 199)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__32 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__33 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__34 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__32_value),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__34_value)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__35 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__35_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__36 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__36_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__37 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__39 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__41 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__41_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__43 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__43_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__15_value),LEAN_SCALAR_PTR_LITERAL(195, 199, 76, 105, 144, 166, 180, 221)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__46 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_2),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_3),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__15_value),LEAN_SCALAR_PTR_LITERAL(163, 250, 23, 41, 78, 64, 76, 96)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__48 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__49 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__49_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__50 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__50_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__52 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__52_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__53 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__53_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__54 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__54_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__55 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__55_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialize"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__56 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__56_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(55, 206, 156, 211, 241, 221, 187, 166)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__58 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__58_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_0),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60;
static const lean_array_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__61 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__61_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__62 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(46, 201, 23, 171, 41, 77, 220, 95)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(10, 9, 185, 250, 127, 107, 245, 225)}};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63_value;
static const lean_string_object l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Sym.simp set for "};
static const lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__64 = (const lean_object*)&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__64_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__12));
v___x_97_ = l_String_toRawSubstring_x27(v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__21));
v___x_120_ = l_String_toRawSubstring_x27(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28));
v___x_133_ = l_String_toRawSubstring_x27(v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lean_Parser_Command_registerSymSimpAttr___closed__15));
v___x_179_ = l_String_toRawSubstring_x27(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Array_mkArray0(lean_box(0));
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1(lean_object* v_x_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_228_ = ((lean_object*)(l_Lean_Parser_Command_registerSymSimpAttr___closed__0));
v___x_229_ = ((lean_object*)(l_Lean_Parser_Command_registerSymSimpAttr___closed__11));
v___x_373_ = ((lean_object*)(l_Lean_Parser_Command_registerSymSimpAttr___closed__16));
lean_inc(v_x_225_);
v___x_374_ = l_Lean_Syntax_isOfKind(v_x_225_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec(v_x_225_);
v___x_375_ = lean_box(1);
v___x_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v_a_227_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; lean_object* v___y_379_; lean_object* v___y_380_; uint8_t v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_id_402_; lean_object* v___y_404_; lean_object* v___x_415_; 
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_400_ = l_Lean_Syntax_getArg(v_x_225_, v___x_377_);
v___x_401_ = lean_unsigned_to_nat(2u);
v_id_402_ = l_Lean_Syntax_getArg(v_x_225_, v___x_401_);
lean_dec(v_x_225_);
v___x_415_ = l_Lean_Syntax_getOptional_x3f(v___x_400_);
lean_dec(v___x_400_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v___x_416_; 
v___x_416_ = lean_box(0);
v___y_404_ = v___x_416_;
goto v___jp_403_;
}
else
{
lean_object* v_val_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
v_val_417_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_415_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_val_417_);
lean_dec(v___x_415_);
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
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_val_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
v___y_404_ = v___x_422_;
goto v___jp_403_;
}
}
}
v___jp_378_:
{
lean_object* v_quotContext_385_; lean_object* v_currMacroScope_386_; lean_object* v_ref_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_quotContext_385_ = lean_ctor_get(v_a_226_, 1);
v_currMacroScope_386_ = lean_ctor_get(v_a_226_, 2);
v_ref_387_ = lean_ctor_get(v_a_226_, 5);
v___x_388_ = l_String_removeLeadingSpaces(v___y_384_);
v___x_389_ = lean_box(2);
v___x_390_ = l_Lean_Syntax_mkStrLit(v___x_388_, v___x_389_);
v___x_391_ = l_Lean_SourceInfo_fromRef(v_ref_387_, v___y_381_);
v___x_392_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__55));
v___x_393_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__56));
v___x_394_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57));
v___x_395_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59));
v___x_396_ = lean_obj_once(&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60, &l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60_once, _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60);
if (lean_obj_tag(v___y_380_) == 1)
{
lean_object* v_val_397_; lean_object* v___x_398_; 
v_val_397_ = lean_ctor_get(v___y_380_, 0);
lean_inc(v_val_397_);
lean_dec_ref(v___y_380_);
v___x_398_ = l_Array_mkArray1___redArg(v_val_397_);
v___y_302_ = v___x_392_;
v___y_303_ = v___x_396_;
v___y_304_ = v___x_390_;
v___y_305_ = v___y_383_;
v___y_306_ = v___y_382_;
v___y_307_ = v___x_389_;
v___y_308_ = v___y_379_;
v___y_309_ = v_quotContext_385_;
v___y_310_ = v___x_394_;
v___y_311_ = v___x_393_;
v___y_312_ = v___x_395_;
v___y_313_ = v___x_391_;
v___y_314_ = v_currMacroScope_386_;
v___y_315_ = v___x_398_;
goto v___jp_301_;
}
else
{
lean_object* v___x_399_; 
lean_dec(v___y_380_);
v___x_399_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__61));
v___y_302_ = v___x_392_;
v___y_303_ = v___x_396_;
v___y_304_ = v___x_390_;
v___y_305_ = v___y_383_;
v___y_306_ = v___y_382_;
v___y_307_ = v___x_389_;
v___y_308_ = v___y_379_;
v___y_309_ = v_quotContext_385_;
v___y_310_ = v___x_394_;
v___y_311_ = v___x_393_;
v___y_312_ = v___x_395_;
v___y_313_ = v___x_391_;
v___y_314_ = v_currMacroScope_386_;
v___y_315_ = v___x_399_;
goto v___jp_301_;
}
}
v___jp_403_:
{
lean_object* v___x_405_; lean_object* v_str_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; lean_object* v_idParser_410_; 
v___x_405_ = l_Lean_TSyntax_getId(v_id_402_);
lean_inc_n(v___x_405_, 2);
v_str_406_ = l_Lean_Name_toString(v___x_405_, v___x_374_);
v___x_407_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63));
v___x_408_ = l_Lean_Name_append(v___x_407_, v___x_405_);
v___x_409_ = 0;
v_idParser_410_ = l_Lean_mkIdentFrom(v_id_402_, v___x_408_, v___x_409_);
lean_dec(v_id_402_);
if (lean_obj_tag(v___y_404_) == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__64));
v___x_412_ = lean_string_append(v___x_411_, v_str_406_);
v___y_379_ = v_idParser_410_;
v___y_380_ = v___y_404_;
v___y_381_ = v___x_409_;
v___y_382_ = v___x_405_;
v___y_383_ = v_str_406_;
v___y_384_ = v___x_412_;
goto v___jp_378_;
}
else
{
lean_object* v_val_413_; lean_object* v___x_414_; 
v_val_413_ = lean_ctor_get(v___y_404_, 0);
v___x_414_ = l_Lean_TSyntax_getDocString(v_val_413_);
v___y_379_ = v_idParser_410_;
v___y_380_ = v___y_404_;
v___y_381_ = v___x_409_;
v___y_382_ = v___x_405_;
v___y_383_ = v_str_406_;
v___y_384_ = v___x_414_;
goto v___jp_378_;
}
}
}
v___jp_230_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
lean_inc_n(v___y_232_, 5);
lean_inc_n(v___y_252_, 19);
v___x_254_ = l_Lean_Syntax_node2(v___y_252_, v___y_232_, v___y_253_, v___y_238_);
lean_inc(v___y_236_);
v___x_255_ = l_Lean_Syntax_node2(v___y_252_, v___y_236_, v___y_241_, v___x_254_);
lean_inc(v___y_239_);
v___x_256_ = l_Lean_Syntax_node1(v___y_252_, v___y_239_, v___x_255_);
lean_inc_n(v___y_247_, 4);
lean_inc(v___y_231_);
v___x_257_ = l_Lean_Syntax_node2(v___y_252_, v___y_231_, v___x_256_, v___y_247_);
v___x_258_ = l_Lean_Syntax_node1(v___y_252_, v___y_232_, v___x_257_);
lean_inc(v___y_235_);
v___x_259_ = l_Lean_Syntax_node1(v___y_252_, v___y_235_, v___x_258_);
lean_inc(v___y_246_);
v___x_260_ = l_Lean_Syntax_node4(v___y_252_, v___y_246_, v___y_237_, v___y_233_, v___y_250_, v___x_259_);
v___x_261_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__0));
v___x_262_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1));
v___x_263_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__2));
lean_inc_ref(v___y_249_);
v___x_264_ = l_Lean_Name_mkStr4(v___x_228_, v___x_229_, v___y_249_, v___x_263_);
v___x_265_ = l_Lean_Syntax_node1(v___y_252_, v___x_264_, v___y_247_);
v___x_266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_266_, 0, v___y_252_);
lean_ctor_set(v___x_266_, 1, v___x_261_);
v___x_267_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4));
v___x_268_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__5));
v___x_269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_269_, 0, v___y_252_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__6));
v___x_271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_271_, 0, v___y_252_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__7));
v___x_273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_273_, 0, v___y_252_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__8));
v___x_275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_275_, 0, v___y_252_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = l_Lean_Syntax_node5(v___y_252_, v___x_267_, v___x_269_, v___x_271_, v___x_273_, v___y_243_, v___x_275_);
v___x_277_ = l_Lean_Syntax_node1(v___y_252_, v___y_232_, v___x_276_);
v___x_278_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11));
v___x_279_ = l_Lean_Syntax_mkStrLit(v___y_240_, v___y_242_);
v___x_280_ = l_Lean_Syntax_node1(v___y_252_, v___x_278_, v___x_279_);
v___x_281_ = l_Lean_Syntax_node1(v___y_252_, v___y_232_, v___x_280_);
v___x_282_ = lean_obj_once(&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13, &l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13_once, _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13);
v___x_283_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__14));
lean_inc(v___y_251_);
lean_inc(v___y_244_);
v___x_284_ = l_Lean_addMacroScope(v___y_244_, v___x_283_, v___y_251_);
v___x_285_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_285_, 0, v___y_252_);
lean_ctor_set(v___x_285_, 1, v___x_282_);
lean_ctor_set(v___x_285_, 2, v___x_284_);
lean_ctor_set(v___x_285_, 3, v___y_245_);
v___x_286_ = lean_unsigned_to_nat(10u);
v___x_287_ = lean_mk_empty_array_with_capacity(v___x_286_);
v___x_288_ = lean_array_push(v___x_287_, v___y_248_);
v___x_289_ = lean_array_push(v___x_288_, v___y_247_);
v___x_290_ = lean_array_push(v___x_289_, v___x_265_);
v___x_291_ = lean_array_push(v___x_290_, v___x_266_);
v___x_292_ = lean_array_push(v___x_291_, v___y_247_);
v___x_293_ = lean_array_push(v___x_292_, v___x_277_);
v___x_294_ = lean_array_push(v___x_293_, v___y_247_);
v___x_295_ = lean_array_push(v___x_294_, v___x_281_);
v___x_296_ = lean_array_push(v___x_295_, v___y_234_);
v___x_297_ = lean_array_push(v___x_296_, v___x_285_);
v___x_298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_298_, 0, v___y_252_);
lean_ctor_set(v___x_298_, 1, v___x_262_);
lean_ctor_set(v___x_298_, 2, v___x_297_);
v___x_299_ = l_Lean_Syntax_node2(v___y_252_, v___y_232_, v___x_260_, v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v_a_227_);
return v___x_300_;
}
v___jp_301_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
lean_inc_ref_n(v___y_303_, 2);
v___x_316_ = l_Array_append___redArg(v___y_303_, v___y_315_);
lean_dec_ref(v___y_315_);
lean_inc_n(v___y_302_, 5);
lean_inc_n(v___y_313_, 18);
v___x_317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_317_, 0, v___y_313_);
lean_ctor_set(v___x_317_, 1, v___y_302_);
lean_ctor_set(v___x_317_, 2, v___x_316_);
v___x_318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_318_, 0, v___y_313_);
lean_ctor_set(v___x_318_, 1, v___y_302_);
lean_ctor_set(v___x_318_, 2, v___y_303_);
v___x_319_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__15));
v___x_320_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16));
v___x_321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_321_, 0, v___y_313_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
v___x_322_ = l_Lean_Syntax_node1(v___y_313_, v___x_320_, v___x_321_);
v___x_323_ = l_Lean_Syntax_node1(v___y_313_, v___y_302_, v___x_322_);
v___x_324_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__17));
v___x_325_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18));
v___x_326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_326_, 0, v___y_313_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
v___x_327_ = l_Lean_Syntax_node1(v___y_313_, v___x_325_, v___x_326_);
v___x_328_ = l_Lean_Syntax_node1(v___y_313_, v___y_302_, v___x_327_);
lean_inc_ref_n(v___x_318_, 4);
lean_inc_ref(v___x_317_);
lean_inc(v___y_312_);
v___x_329_ = l_Lean_Syntax_node7(v___y_313_, v___y_312_, v___x_317_, v___x_318_, v___x_323_, v___x_318_, v___x_328_, v___x_318_, v___x_318_);
v___x_330_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20));
lean_inc_ref(v___y_311_);
v___x_331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_331_, 0, v___y_313_);
lean_ctor_set(v___x_331_, 1, v___y_311_);
v___x_332_ = l_Lean_Syntax_node1(v___y_313_, v___x_330_, v___x_331_);
v___x_333_ = lean_obj_once(&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22, &l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22_once, _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22);
v___x_334_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__23));
lean_inc_n(v___y_314_, 3);
lean_inc_n(v___y_309_, 3);
v___x_335_ = l_Lean_addMacroScope(v___y_309_, v___x_334_, v___y_314_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_337_, 0, v___y_313_);
lean_ctor_set(v___x_337_, 1, v___x_333_);
lean_ctor_set(v___x_337_, 2, v___x_335_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
v___x_338_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24));
v___x_339_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26));
v___x_340_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__27));
v___x_341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_341_, 0, v___y_313_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_obj_once(&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29, &l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29_once, _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29);
v___x_343_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__30));
v___x_344_ = l_Lean_addMacroScope(v___y_309_, v___x_343_, v___y_314_);
v___x_345_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__35));
v___x_346_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_346_, 0, v___y_313_);
lean_ctor_set(v___x_346_, 1, v___x_342_);
lean_ctor_set(v___x_346_, 2, v___x_344_);
lean_ctor_set(v___x_346_, 3, v___x_345_);
lean_inc_ref(v___x_341_);
v___x_347_ = l_Lean_Syntax_node2(v___y_313_, v___x_339_, v___x_341_, v___x_346_);
v___x_348_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__36));
v___x_349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_349_, 0, v___y_313_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = l_Lean_Syntax_node3(v___y_313_, v___y_302_, v___x_337_, v___x_347_, v___x_349_);
v___x_351_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38));
v___x_352_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40));
v___x_353_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42));
v___x_354_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44));
v___x_355_ = lean_obj_once(&l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45, &l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45_once, _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45);
v___x_356_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__46));
v___x_357_ = l_Lean_addMacroScope(v___y_309_, v___x_356_, v___y_314_);
v___x_358_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__49));
v___x_359_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_359_, 0, v___y_313_);
lean_ctor_set(v___x_359_, 1, v___x_355_);
lean_ctor_set(v___x_359_, 2, v___x_357_);
lean_ctor_set(v___x_359_, 3, v___x_358_);
lean_inc(v___y_306_);
v___x_360_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_336_, v___y_306_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_quoteNameMk(v___y_306_);
v___y_231_ = v___x_352_;
v___y_232_ = v___y_302_;
v___y_233_ = v___x_332_;
v___y_234_ = v___x_341_;
v___y_235_ = v___x_351_;
v___y_236_ = v___x_354_;
v___y_237_ = v___x_329_;
v___y_238_ = v___y_304_;
v___y_239_ = v___x_353_;
v___y_240_ = v___y_305_;
v___y_241_ = v___x_359_;
v___y_242_ = v___y_307_;
v___y_243_ = v___y_308_;
v___y_244_ = v___y_309_;
v___y_245_ = v___x_336_;
v___y_246_ = v___y_310_;
v___y_247_ = v___x_318_;
v___y_248_ = v___x_317_;
v___y_249_ = v___x_338_;
v___y_250_ = v___x_350_;
v___y_251_ = v___y_314_;
v___y_252_ = v___y_313_;
v___y_253_ = v___x_361_;
goto v___jp_230_;
}
else
{
lean_object* v_val_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v___y_306_);
v_val_362_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_val_362_);
lean_dec_ref(v___x_360_);
v___x_363_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51));
v___x_364_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__52));
v___x_365_ = ((lean_object*)(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__53));
v___x_366_ = lean_string_intercalate(v___x_365_, v_val_362_);
v___x_367_ = lean_string_append(v___x_364_, v___x_366_);
lean_dec_ref(v___x_366_);
lean_inc_n(v___y_307_, 2);
v___x_368_ = l_Lean_Syntax_mkNameLit(v___x_367_, v___y_307_);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_mk_empty_array_with_capacity(v___x_369_);
v___x_371_ = lean_array_push(v___x_370_, v___x_368_);
v___x_372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_372_, 0, v___y_307_);
lean_ctor_set(v___x_372_, 1, v___x_363_);
lean_ctor_set(v___x_372_, 2, v___x_371_);
v___y_231_ = v___x_352_;
v___y_232_ = v___y_302_;
v___y_233_ = v___x_332_;
v___y_234_ = v___x_341_;
v___y_235_ = v___x_351_;
v___y_236_ = v___x_354_;
v___y_237_ = v___x_329_;
v___y_238_ = v___y_304_;
v___y_239_ = v___x_353_;
v___y_240_ = v___y_305_;
v___y_241_ = v___x_359_;
v___y_242_ = v___y_307_;
v___y_243_ = v___y_308_;
v___y_244_ = v___y_309_;
v___y_245_ = v___x_336_;
v___y_246_ = v___y_310_;
v___y_247_ = v___x_318_;
v___y_248_ = v___x_317_;
v___y_249_ = v___x_338_;
v___y_250_ = v___x_350_;
v___y_251_ = v___y_314_;
v___y_252_ = v___y_313_;
v___y_253_ = v___x_372_;
goto v___jp_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___boxed(lean_object* v_x_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1(v_x_425_, v_a_426_, v_a_427_);
lean_dec_ref(v_a_426_);
return v_res_428_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Variant(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Variant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Extra(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Variant(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Variant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
}
#ifdef __cplusplus
}
#endif
