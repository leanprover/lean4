// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.RCases
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.RCases import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_tuple(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_joinAltPats___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_fill(lean_object*);
lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
static const lean_string_object l_Lean_Fmt_fmtRCasesPatMed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtRCasesPatMed___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtRCasesPatMed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtRCasesPatMed___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRCasesPatMed___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtRCasesPatMed___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtRCasesPatMed___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "rcasesPatMed"};
static const lean_object* l_Lean_Fmt_fmtRCasesPatMed___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatMed___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatMed___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatMed___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatMed___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__3_value),LEAN_SCALAR_PTR_LITERAL(253, 13, 65, 195, 228, 27, 47, 149)}};
static const lean_object* l_Lean_Fmt_fmtRCasesPatMed___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatMed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatMed___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtRCasesPatMed"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(68, 197, 25, 95, 219, 164, 180, 155)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRCasesPatLo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rcasesPatLo"};
static const lean_object* l_Lean_Fmt_fmtRCasesPatLo___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatLo___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatLo___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatLo___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatLo___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatLo___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatLo___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatLo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatLo___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRCasesPatLo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 222, 245, 138, 122, 92, 170, 214)}};
static const lean_object* l_Lean_Fmt_fmtRCasesPatLo___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatLo___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatLo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatLo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtRCasesPatLo"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 48, 212, 24, 147, 251, 172, 255)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRCasesPatOne___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rcasesPat"};
static const lean_object* l_Lean_Fmt_fmtRCasesPatOne___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtRCasesPatOne___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l_Lean_Fmt_fmtRCasesPatOne___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatOne___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatOne___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatOne___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatOne___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatOne___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__2_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 152, 172, 228, 11, 240, 156, 168)}};
static const lean_object* l_Lean_Fmt_fmtRCasesPatOne___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtRCasesPatOne___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtRCasesPatOne___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatOne___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtRCasesPatOne___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatOne(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatOne___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtRCasesPatOne"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(159, 251, 84, 147, 184, 227, 93, 25)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRCasesPatExplicit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_Lean_Fmt_fmtRCasesPatExplicit___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatExplicit___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatExplicit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatExplicit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatExplicit___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatExplicit___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatExplicit___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatExplicit___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatExplicit___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatExplicit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatExplicit___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtRCasesPatExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 12, 240, 143, 52, 56, 179, 56)}};
static const lean_object* l_Lean_Fmt_fmtRCasesPatExplicit___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatExplicit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatExplicit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatExplicit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtRCasesPatExplicit"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 195, 87, 239, 216, 90, 76, 12)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRCasesPatTuple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l_Lean_Fmt_fmtRCasesPatTuple___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatTuple___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatTuple___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatTuple___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatTuple___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatTuple___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatTuple___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatTuple___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatTuple___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatTuple___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatTuple___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtRCasesPatTuple___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 241, 13, 230, 132, 227, 26, 91)}};
static const lean_object* l_Lean_Fmt_fmtRCasesPatTuple___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatTuple___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRCasesPatTuple___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtRCasesPatTuple___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatTuple___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatTuple(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatTuple___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtRCasesPatTuple"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 181, 138, 255, 235, 82, 129, 57)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRCasesPatParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Fmt_fmtRCasesPatParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatParen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatParen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatParen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatParen___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatParen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatParen___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatParen___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatParen___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l_Lean_Fmt_fmtRCasesPatParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRCasesPatParen___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtRCasesPatParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 230, 23, 208, 164, 113, 201, 132)}};
static const lean_object* l_Lean_Fmt_fmtRCasesPatParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRCasesPatParen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtRCasesPatParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 134, 111, 124, 163, 250, 7, 202)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRIntroPatOne___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rintroPat"};
static const lean_object* l_Lean_Fmt_fmtRIntroPatOne___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRIntroPatOne___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRIntroPatOne___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRIntroPatOne___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRIntroPatOne___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRIntroPatOne___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRIntroPatOne___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRIntroPatOne___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRIntroPatOne___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRIntroPatOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 93, 179, 129, 121, 199, 215, 253)}};
static const lean_ctor_object l_Lean_Fmt_fmtRIntroPatOne___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRIntroPatOne___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtRCasesPatOne___closed__1_value),LEAN_SCALAR_PTR_LITERAL(40, 214, 202, 122, 59, 249, 35, 61)}};
static const lean_object* l_Lean_Fmt_fmtRIntroPatOne___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRIntroPatOne___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRIntroPatOne(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRIntroPatOne___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtRIntroPatOne"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 71, 33, 127, 253, 54, 195, 19)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRIntroPatBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binder"};
static const lean_object* l_Lean_Fmt_fmtRIntroPatBinder___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRIntroPatBinder___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRIntroPatBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRIntroPatBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRIntroPatBinder___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRIntroPatBinder___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRIntroPatBinder___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtRIntroPatBinder___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRIntroPatBinder___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRIntroPatOne___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 93, 179, 129, 121, 199, 215, 253)}};
static const lean_ctor_object l_Lean_Fmt_fmtRIntroPatBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRIntroPatBinder___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtRIntroPatBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 86, 105, 110, 83, 1, 132, 81)}};
static const lean_object* l_Lean_Fmt_fmtRIntroPatBinder___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRIntroPatBinder___closed__1_value;
static const lean_array_object l_Lean_Fmt_fmtRIntroPatBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtRIntroPatBinder___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRIntroPatBinder___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRIntroPatBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRIntroPatBinder___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtRIntroPatBinder"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 127, 193, 163, 100, 119, 82, 21)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticRCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rcases"};
static const lean_object* l_Lean_Fmt_fmtTacticRCases___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticRCases___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticRCases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticRCases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticRCases___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticRCases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticRCases___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticRCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticRCases___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticRCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 76, 101, 33, 30, 11, 121, 59)}};
static const lean_object* l_Lean_Fmt_fmtTacticRCases___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticRCases___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticRCases(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticRCases___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtTacticRCases"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 193, 175, 179, 194, 148, 220, 148)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticObtain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "obtain"};
static const lean_object* l_Lean_Fmt_fmtTacticObtain___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticObtain___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticObtain___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticObtain___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticObtain___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticObtain___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticObtain___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticObtain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticObtain___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticObtain___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 177, 143, 165, 56, 37, 104, 113)}};
static const lean_object* l_Lean_Fmt_fmtTacticObtain___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticObtain___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticObtain(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticObtain___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtTacticObtain"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 192, 47, 122, 196, 100, 63, 220)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticRIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rintro"};
static const lean_object* l_Lean_Fmt_fmtTacticRIntro___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticRIntro___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticRIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticRIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticRIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticRIntro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticRIntro___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticRIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticRIntro___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticRIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 254, 242, 235, 94, 162, 254, 146)}};
static const lean_object* l_Lean_Fmt_fmtTacticRIntro___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticRIntro___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticRIntro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticRIntro___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtTacticRIntro"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRCasesPatMed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 155, 40, 92, 200, 165, 28, 183)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatMed(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatMed___closed__4));
lean_inc(v_x_10_);
v___x_14_ = l_Lean_Syntax_isOfKind(v_x_10_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_dec(v_x_10_);
v___x_15_ = l_Lean_Fmt_Error_partialFormatter;
v___x_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v_a_12_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v_pats_19_; lean_object* v___x_20_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = l_Lean_Syntax_getArg(v_x_10_, v___x_17_);
lean_dec(v_x_10_);
v_pats_19_ = l_Lean_Syntax_getArgs(v___x_18_);
lean_dec(v___x_18_);
v___x_20_ = l_Lean_Fmt_fmtTSepArray___redArg(v_pats_19_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_33_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
v_a_22_ = lean_ctor_get(v___x_20_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_33_ == 0)
{
v___x_24_ = v___x_20_;
v_isShared_25_ = v_isSharedCheck_33_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_inc(v_a_21_);
lean_dec(v___x_20_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_33_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
v___x_26_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_27_ = l_Lean_Fmt_joinAltPats___redArg(v___x_26_, v_a_21_);
lean_dec(v_a_21_);
v___x_28_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_27_, v___x_14_);
lean_dec_ref(v___x_27_);
v___x_29_ = l_Lean_Fmt_TaggedDoc_nested(v___x_28_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_29_);
v___x_31_ = v___x_24_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_a_22_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
else
{
lean_object* v_a_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_42_; 
v_a_34_ = lean_ctor_get(v___x_20_, 0);
v_a_35_ = lean_ctor_get(v___x_20_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_42_ == 0)
{
v___x_37_ = v___x_20_;
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_inc(v_a_34_);
lean_dec(v___x_20_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_34_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_a_35_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatMed___boxed(lean_object* v_x_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Fmt_fmtRCasesPatMed(v_x_43_, v_a_44_, v_a_45_);
lean_dec_ref(v_a_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_54_ = l_Lean_Fmt_fmtAttribute;
v___x_55_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatMed___closed__4));
v___x_56_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___closed__2));
v___x_57_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRCasesPatMed___boxed), 3, 0);
v___x_58_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_54_, v___x_55_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1___boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1();
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatLo(lean_object* v_x_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatLo___closed__1));
lean_inc(v_x_67_);
v___x_71_ = l_Lean_Syntax_isOfKind(v_x_67_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_x_67_);
v___x_72_ = l_Lean_Fmt_Error_partialFormatter;
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v_a_69_);
return v___x_73_;
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; lean_object* v___y_79_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___y_83_; lean_object* v_colonTk_x3f_98_; lean_object* v_type_x3f_99_; lean_object* v___y_100_; lean_object* v___y_101_; 
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = l_Lean_Syntax_getArg(v_x_67_, v___x_74_);
v___x_76_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatMed___closed__4));
lean_inc(v___x_75_);
v___x_77_ = l_Lean_Syntax_isOfKind(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec(v___x_75_);
lean_dec(v_x_67_);
v___x_119_ = l_Lean_Fmt_Error_partialFormatter;
v___x_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v_a_69_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = l_Lean_Syntax_getArg(v_x_67_, v___x_121_);
lean_dec(v_x_67_);
v___x_123_ = l_Lean_Syntax_isNone(v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_122_);
v___x_125_ = l_Lean_Syntax_matchesNull(v___x_122_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v___x_122_);
lean_dec(v___x_75_);
v___x_126_ = l_Lean_Fmt_Error_partialFormatter;
v___x_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v_a_69_);
return v___x_127_;
}
else
{
lean_object* v_colonTk_x3f_128_; lean_object* v_type_x3f_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_colonTk_x3f_128_ = l_Lean_Syntax_getArg(v___x_122_, v___x_74_);
v_type_x3f_129_ = l_Lean_Syntax_getArg(v___x_122_, v___x_121_);
lean_dec(v___x_122_);
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v_colonTk_x3f_128_);
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v_type_x3f_129_);
v_colonTk_x3f_98_ = v___x_130_;
v_type_x3f_99_ = v___x_131_;
v___y_100_ = v_a_68_;
v___y_101_ = v_a_69_;
goto v___jp_97_;
}
}
else
{
lean_object* v___x_132_; 
lean_dec(v___x_122_);
v___x_132_ = lean_box(0);
v_colonTk_x3f_98_ = v___x_132_;
v_type_x3f_99_ = v___x_132_;
v___y_100_ = v_a_68_;
v___y_101_ = v_a_69_;
goto v___jp_97_;
}
}
v___jp_78_:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Fmt_fmt_x3f(v___y_83_, v___y_81_, v___y_79_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_96_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_a_86_ = lean_ctor_get(v___x_84_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_96_ == 0)
{
v___x_88_ = v___x_84_;
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_91_, 0, v___x_77_);
lean_ctor_set_uint8(v___x_91_, 1, v___x_90_);
lean_ctor_set_uint8(v___x_91_, 2, v___x_77_);
lean_ctor_set_uint8(v___x_91_, 3, v___x_77_);
v___x_92_ = l_Lean_Fmt_Layouts_typeAscription(v___y_80_, v___y_82_, v_a_85_, v___x_91_);
lean_dec_ref_known(v___x_91_, 0);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_92_);
v___x_94_ = v___x_88_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_a_86_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
else
{
lean_dec_ref(v___y_82_);
lean_dec_ref(v___y_80_);
return v___x_84_;
}
}
v___jp_97_:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Fmt_fmt(v___x_75_, v___y_100_, v___y_101_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v_a_104_; lean_object* v___x_105_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
v_a_104_ = lean_ctor_get(v___x_102_, 1);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_102_, 2);
v___x_105_ = l_Lean_Fmt_fmt_x3f(v_colonTk_x3f_98_, v___y_100_, v_a_104_);
if (lean_obj_tag(v___x_105_) == 0)
{
if (lean_obj_tag(v_type_x3f_99_) == 0)
{
lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v___x_108_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
v_a_107_ = lean_ctor_get(v___x_105_, 1);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_105_, 2);
v___x_108_ = lean_box(0);
v___y_79_ = v_a_107_;
v___y_80_ = v_a_103_;
v___y_81_ = v___y_100_;
v___y_82_ = v_a_106_;
v___y_83_ = v___x_108_;
goto v___jp_78_;
}
else
{
lean_object* v_a_109_; lean_object* v_a_110_; lean_object* v_val_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_a_109_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_109_);
v_a_110_ = lean_ctor_get(v___x_105_, 1);
lean_inc(v_a_110_);
lean_dec_ref_known(v___x_105_, 2);
v_val_111_ = lean_ctor_get(v_type_x3f_99_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_type_x3f_99_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v_type_x3f_99_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_val_111_);
lean_dec(v_type_x3f_99_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_val_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
v___y_79_ = v_a_110_;
v___y_80_ = v_a_103_;
v___y_81_ = v___y_100_;
v___y_82_ = v_a_109_;
v___y_83_ = v___x_116_;
goto v___jp_78_;
}
}
}
}
else
{
lean_dec(v_a_103_);
lean_dec(v_type_x3f_99_);
return v___x_105_;
}
}
else
{
lean_dec(v_type_x3f_99_);
lean_dec(v_colonTk_x3f_98_);
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatLo___boxed(lean_object* v_x_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Fmt_fmtRCasesPatLo(v_x_133_, v_a_134_, v_a_135_);
lean_dec_ref(v_a_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1(){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = l_Lean_Fmt_fmtAttribute;
v___x_144_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatLo___closed__1));
v___x_145_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___closed__1));
v___x_146_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRCasesPatLo___boxed), 3, 0);
v___x_147_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_143_, v___x_144_, v___x_145_, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1___boxed(lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1();
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatOne(lean_object* v_x_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatOne___closed__2));
lean_inc(v_x_161_);
v___x_165_ = l_Lean_Syntax_isOfKind(v_x_161_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_x_161_);
v___x_166_ = l_Lean_Fmt_Error_partialFormatter;
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_163_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = l_Lean_Syntax_getArg(v_x_161_, v___x_168_);
lean_dec(v_x_161_);
v___x_170_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatOne___closed__4));
lean_inc(v___x_169_);
v___x_171_ = l_Lean_Syntax_isOfKind(v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec(v___x_169_);
v___x_172_ = l_Lean_Fmt_Error_partialFormatter;
v___x_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_a_163_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Fmt_fmt(v___x_169_, v_a_162_, v_a_163_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatOne___boxed(lean_object* v_x_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Fmt_fmtRCasesPatOne(v_x_175_, v_a_176_, v_a_177_);
lean_dec_ref(v_a_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1(){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_185_ = l_Lean_Fmt_fmtAttribute;
v___x_186_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatOne___closed__2));
v___x_187_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___closed__1));
v___x_188_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRCasesPatOne___boxed), 3, 0);
v___x_189_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_185_, v___x_186_, v___x_187_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1___boxed(lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1();
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatExplicit(lean_object* v_x_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatExplicit___closed__1));
lean_inc(v_x_199_);
v___x_203_ = l_Lean_Syntax_isOfKind(v_x_199_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v_x_199_);
v___x_204_ = l_Lean_Fmt_Error_partialFormatter;
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v_a_201_);
return v___x_205_;
}
else
{
lean_object* v___x_206_; lean_object* v_atTk_207_; lean_object* v___x_208_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v_atTk_207_ = l_Lean_Syntax_getArg(v_x_199_, v___x_206_);
v___x_208_ = l_Lean_Fmt_fmt(v_atTk_207_, v_a_200_, v_a_201_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v_a_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
v_a_210_ = lean_ctor_get(v___x_208_, 1);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_208_, 2);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = l_Lean_Syntax_getArg(v_x_199_, v___x_211_);
lean_dec(v_x_199_);
v___x_213_ = l_Lean_Fmt_fmt(v___x_212_, v_a_200_, v_a_210_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_224_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_a_215_ = lean_ctor_get(v___x_213_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_224_ == 0)
{
v___x_217_ = v___x_213_;
v_isShared_218_ = v_isSharedCheck_224_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_224_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_219_ = 0;
v___x_220_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_209_, v_a_214_, v___x_219_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_220_);
v___x_222_ = v___x_217_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_a_215_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
else
{
lean_dec(v_a_209_);
return v___x_213_;
}
}
else
{
lean_dec(v_x_199_);
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatExplicit___boxed(lean_object* v_x_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Fmt_fmtRCasesPatExplicit(v_x_225_, v_a_226_, v_a_227_);
lean_dec_ref(v_a_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1(){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_235_ = l_Lean_Fmt_fmtAttribute;
v___x_236_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatExplicit___closed__1));
v___x_237_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___closed__1));
v___x_238_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRCasesPatExplicit___boxed), 3, 0);
v___x_239_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_235_, v___x_236_, v___x_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1___boxed(lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1();
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatTuple(lean_object* v_x_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatTuple___closed__1));
lean_inc(v_x_250_);
v___x_254_ = l_Lean_Syntax_isOfKind(v_x_250_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_x_250_);
v___x_255_ = l_Lean_Fmt_Error_partialFormatter;
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_a_252_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v_lbTk_258_; lean_object* v___x_259_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v_lbTk_258_ = l_Lean_Syntax_getArg(v_x_250_, v___x_257_);
v___x_259_ = l_Lean_Fmt_fmt(v_lbTk_258_, v_a_251_, v_a_252_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_pats_264_; lean_object* v___x_265_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
v_a_261_ = lean_ctor_get(v___x_259_, 1);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_259_, 2);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = l_Lean_Syntax_getArg(v_x_250_, v___x_262_);
v_pats_264_ = l_Lean_Syntax_getArgs(v___x_263_);
lean_dec(v___x_263_);
v___x_265_ = l_Lean_Fmt_fmtTSepArray___redArg(v_pats_264_, v_a_251_, v_a_261_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v___x_268_; lean_object* v_rbTk_269_; lean_object* v___x_270_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
v_a_267_ = lean_ctor_get(v___x_265_, 1);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_265_, 2);
v___x_268_ = lean_unsigned_to_nat(2u);
v_rbTk_269_ = l_Lean_Syntax_getArg(v_x_250_, v___x_268_);
lean_dec(v_x_250_);
v___x_270_ = l_Lean_Fmt_fmt(v_rbTk_269_, v_a_251_, v_a_267_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_281_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_a_272_ = lean_ctor_get(v___x_270_, 1);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_281_ == 0)
{
v___x_274_ = v___x_270_;
v_isShared_275_ = v_isSharedCheck_281_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_281_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatTuple___closed__2));
v___x_277_ = l_Lean_Fmt_Layouts_tuple(v___x_276_, v_a_260_, v_a_266_, v_a_271_);
lean_dec(v_a_266_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_277_);
v___x_279_ = v___x_274_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_a_272_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_dec(v_a_266_);
lean_dec(v_a_260_);
return v___x_270_;
}
}
else
{
lean_object* v_a_282_; lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec(v_a_260_);
lean_dec(v_x_250_);
v_a_282_ = lean_ctor_get(v___x_265_, 0);
v_a_283_ = lean_ctor_get(v___x_265_, 1);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_265_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_inc(v_a_282_);
lean_dec(v___x_265_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_282_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_dec(v_x_250_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatTuple___boxed(lean_object* v_x_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Fmt_fmtRCasesPatTuple(v_x_291_, v_a_292_, v_a_293_);
lean_dec_ref(v_a_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1(){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_301_ = l_Lean_Fmt_fmtAttribute;
v___x_302_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatTuple___closed__1));
v___x_303_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___closed__1));
v___x_304_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRCasesPatTuple___boxed), 3, 0);
v___x_305_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_301_, v___x_302_, v___x_303_, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1___boxed(lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1();
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatParen(lean_object* v_x_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatParen___closed__1));
lean_inc(v_x_315_);
v___x_319_ = l_Lean_Syntax_isOfKind(v_x_315_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec(v_x_315_);
v___x_320_ = l_Lean_Fmt_Error_partialFormatter;
v___x_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_a_317_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = l_Lean_Syntax_getArg(v_x_315_, v___x_322_);
v___x_324_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatLo___closed__1));
lean_inc(v___x_323_);
v___x_325_ = l_Lean_Syntax_isOfKind(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec(v___x_323_);
lean_dec(v_x_315_);
v___x_326_ = l_Lean_Fmt_Error_partialFormatter;
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v_a_317_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; lean_object* v_lbTk_329_; lean_object* v___x_330_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v_lbTk_329_ = l_Lean_Syntax_getArg(v_x_315_, v___x_328_);
v___x_330_ = l_Lean_Fmt_fmt(v_lbTk_329_, v_a_316_, v_a_317_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v_a_332_; lean_object* v___x_333_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
v_a_332_ = lean_ctor_get(v___x_330_, 1);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_330_, 2);
v___x_333_ = l_Lean_Fmt_fmt(v___x_323_, v_a_316_, v_a_332_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v_a_335_; lean_object* v___x_336_; lean_object* v_rbTk_337_; lean_object* v___x_338_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
v_a_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_333_, 2);
v___x_336_ = lean_unsigned_to_nat(2u);
v_rbTk_337_ = l_Lean_Syntax_getArg(v_x_315_, v___x_336_);
lean_dec(v_x_315_);
v___x_338_ = l_Lean_Fmt_fmt(v_rbTk_337_, v_a_316_, v_a_335_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_a_340_ = lean_ctor_get(v___x_338_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v___x_338_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = l_Lean_Fmt_Layouts_parens(v_a_331_, v_a_334_, v_a_339_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_344_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_a_340_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_dec(v_a_334_);
lean_dec(v_a_331_);
return v___x_338_;
}
}
else
{
lean_dec(v_a_331_);
lean_dec(v_x_315_);
return v___x_333_;
}
}
else
{
lean_dec(v___x_323_);
lean_dec(v_x_315_);
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRCasesPatParen___boxed(lean_object* v_x_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Fmt_fmtRCasesPatParen(v_x_349_, v_a_350_, v_a_351_);
lean_dec_ref(v_a_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1(){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_359_ = l_Lean_Fmt_fmtAttribute;
v___x_360_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatParen___closed__1));
v___x_361_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___closed__1));
v___x_362_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRCasesPatParen___boxed), 3, 0);
v___x_363_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_359_, v___x_360_, v___x_361_, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1___boxed(lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1();
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRIntroPatOne(lean_object* v_x_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_Fmt_fmtRIntroPatOne___closed__1));
lean_inc(v_x_373_);
v___x_377_ = l_Lean_Syntax_isOfKind(v_x_373_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_x_373_);
v___x_378_ = l_Lean_Fmt_Error_partialFormatter;
v___x_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v_a_375_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = l_Lean_Syntax_getArg(v_x_373_, v___x_380_);
lean_dec(v_x_373_);
v___x_382_ = l_Lean_Fmt_fmt(v___x_381_, v_a_374_, v_a_375_);
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRIntroPatOne___boxed(lean_object* v_x_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Fmt_fmtRIntroPatOne(v_x_383_, v_a_384_, v_a_385_);
lean_dec_ref(v_a_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1(){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_393_ = l_Lean_Fmt_fmtAttribute;
v___x_394_ = ((lean_object*)(l_Lean_Fmt_fmtRIntroPatOne___closed__1));
v___x_395_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___closed__1));
v___x_396_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRIntroPatOne___boxed), 3, 0);
v___x_397_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_393_, v___x_394_, v___x_395_, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1___boxed(lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1();
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRIntroPatBinder(lean_object* v_x_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Fmt_fmtRIntroPatBinder___closed__1));
lean_inc(v_x_409_);
v___x_413_ = l_Lean_Syntax_isOfKind(v_x_409_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v_x_409_);
v___x_414_ = l_Lean_Fmt_Error_partialFormatter;
v___x_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v_a_411_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v_lbTk_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_typeAscriptionTk_x3f_421_; lean_object* v_type_x3f_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_416_ = lean_unsigned_to_nat(0u);
v_lbTk_417_ = l_Lean_Syntax_getArg(v_x_409_, v___x_416_);
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = l_Lean_Syntax_getArg(v_x_409_, v___x_418_);
v___x_435_ = lean_unsigned_to_nat(2u);
v___x_436_ = l_Lean_Syntax_getArg(v_x_409_, v___x_435_);
v___x_437_ = l_Lean_Syntax_isNone(v___x_436_);
if (v___x_437_ == 0)
{
uint8_t v___x_438_; 
lean_inc(v___x_436_);
v___x_438_ = l_Lean_Syntax_matchesNull(v___x_436_, v___x_435_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec(v___x_436_);
lean_dec(v___x_419_);
lean_dec(v_lbTk_417_);
lean_dec(v_x_409_);
v___x_439_ = l_Lean_Fmt_Error_partialFormatter;
v___x_440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_a_411_);
return v___x_440_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_441_; lean_object* v_type_x3f_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_typeAscriptionTk_x3f_441_ = l_Lean_Syntax_getArg(v___x_436_, v___x_416_);
v_type_x3f_442_ = l_Lean_Syntax_getArg(v___x_436_, v___x_418_);
lean_dec(v___x_436_);
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v_typeAscriptionTk_x3f_441_);
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v_type_x3f_442_);
v_typeAscriptionTk_x3f_421_ = v___x_443_;
v_type_x3f_422_ = v___x_444_;
v___y_423_ = v_a_410_;
v___y_424_ = v_a_411_;
goto v___jp_420_;
}
}
else
{
lean_object* v___x_445_; 
lean_dec(v___x_436_);
v___x_445_ = lean_box(0);
v_typeAscriptionTk_x3f_421_ = v___x_445_;
v_type_x3f_422_ = v___x_445_;
v___y_423_ = v_a_410_;
v___y_424_ = v_a_411_;
goto v___jp_420_;
}
v___jp_420_:
{
lean_object* v___x_425_; lean_object* v_rbTk_426_; lean_object* v_pats_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_425_ = lean_unsigned_to_nat(3u);
v_rbTk_426_ = l_Lean_Syntax_getArg(v_x_409_, v___x_425_);
lean_dec(v_x_409_);
v_pats_427_ = l_Lean_Syntax_getArgs(v___x_419_);
lean_dec(v___x_419_);
v___x_428_ = lean_mk_empty_array_with_capacity(v___x_418_);
lean_inc_ref(v___x_428_);
v___x_429_ = lean_array_push(v___x_428_, v_lbTk_417_);
v___x_430_ = ((lean_object*)(l_Lean_Fmt_fmtRIntroPatBinder___closed__2));
v___x_431_ = lean_box(0);
v___x_432_ = lean_array_push(v___x_428_, v_rbTk_426_);
v___x_433_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_433_, 0, v___x_413_);
v___x_434_ = l_Lean_Fmt_fmtBinder(v___x_429_, v_pats_427_, v___x_430_, v_typeAscriptionTk_x3f_421_, v_type_x3f_422_, v___x_431_, v___x_432_, v___x_433_, v___y_423_, v___y_424_);
lean_dec_ref_known(v___x_433_, 0);
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRIntroPatBinder___boxed(lean_object* v_x_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Fmt_fmtRIntroPatBinder(v_x_446_, v_a_447_, v_a_448_);
lean_dec_ref(v_a_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1(){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_456_ = l_Lean_Fmt_fmtAttribute;
v___x_457_ = ((lean_object*)(l_Lean_Fmt_fmtRIntroPatBinder___closed__1));
v___x_458_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___closed__1));
v___x_459_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRIntroPatBinder___boxed), 3, 0);
v___x_460_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_456_, v___x_457_, v___x_458_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1___boxed(lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1();
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticRCases(lean_object* v_x_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v___x_472_; uint8_t v___x_473_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; 
v___x_472_ = ((lean_object*)(l_Lean_Fmt_fmtTacticRCases___closed__1));
lean_inc(v_x_469_);
v___x_473_ = l_Lean_Syntax_isOfKind(v_x_469_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_x_469_);
v___x_503_ = l_Lean_Fmt_Error_partialFormatter;
v___x_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v_a_471_);
return v___x_504_;
}
else
{
lean_object* v___x_505_; lean_object* v_rcasesTk_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_withTk_x3f_510_; lean_object* v_pat_x3f_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v_rcasesTk_506_ = l_Lean_Syntax_getArg(v_x_469_, v___x_505_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = l_Lean_Syntax_getArg(v_x_469_, v___x_507_);
v___x_543_ = lean_unsigned_to_nat(2u);
v___x_544_ = l_Lean_Syntax_getArg(v_x_469_, v___x_543_);
lean_dec(v_x_469_);
v___x_545_ = l_Lean_Syntax_isNone(v___x_544_);
if (v___x_545_ == 0)
{
uint8_t v___x_546_; 
lean_inc(v___x_544_);
v___x_546_ = l_Lean_Syntax_matchesNull(v___x_544_, v___x_543_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v___x_544_);
lean_dec(v___x_508_);
lean_dec(v_rcasesTk_506_);
v___x_547_ = l_Lean_Fmt_Error_partialFormatter;
v___x_548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_a_471_);
return v___x_548_;
}
else
{
lean_object* v_pat_x3f_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_pat_x3f_549_ = l_Lean_Syntax_getArg(v___x_544_, v___x_507_);
v___x_550_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatLo___closed__1));
lean_inc(v_pat_x3f_549_);
v___x_551_ = l_Lean_Syntax_isOfKind(v_pat_x3f_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v_pat_x3f_549_);
lean_dec(v___x_544_);
lean_dec(v___x_508_);
lean_dec(v_rcasesTk_506_);
v___x_552_ = l_Lean_Fmt_Error_partialFormatter;
v___x_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_a_471_);
return v___x_553_;
}
else
{
lean_object* v_withTk_x3f_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_withTk_x3f_554_ = l_Lean_Syntax_getArg(v___x_544_, v___x_505_);
lean_dec(v___x_544_);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v_withTk_x3f_554_);
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v_pat_x3f_549_);
v_withTk_x3f_510_ = v___x_555_;
v_pat_x3f_511_ = v___x_556_;
v___y_512_ = v_a_470_;
v___y_513_ = v_a_471_;
goto v___jp_509_;
}
}
}
else
{
lean_object* v___x_557_; 
lean_dec(v___x_544_);
v___x_557_ = lean_box(0);
v_withTk_x3f_510_ = v___x_557_;
v_pat_x3f_511_ = v___x_557_;
v___y_512_ = v_a_470_;
v___y_513_ = v_a_471_;
goto v___jp_509_;
}
v___jp_509_:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_Fmt_fmt(v_rcasesTk_506_, v___y_512_, v___y_513_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v_a_516_; lean_object* v_targets_517_; lean_object* v___x_518_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
v_a_516_ = lean_ctor_get(v___x_514_, 1);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_514_, 2);
v_targets_517_ = l_Lean_Syntax_getArgs(v___x_508_);
lean_dec(v___x_508_);
v___x_518_ = l_Lean_Fmt_fmtTSepArray___redArg(v_targets_517_, v___y_512_, v_a_516_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
v_a_520_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_518_, 2);
v___x_521_ = l_Lean_Fmt_fmt_x3f(v_withTk_x3f_510_, v___y_512_, v_a_520_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v_a_523_; lean_object* v___x_524_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
v_a_523_ = lean_ctor_get(v___x_521_, 1);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_521_, 2);
v___x_524_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatTuple___closed__2));
if (lean_obj_tag(v_pat_x3f_511_) == 0)
{
lean_object* v___x_525_; 
v___x_525_ = lean_box(0);
v___y_475_ = v___y_512_;
v___y_476_ = v_a_519_;
v___y_477_ = v_a_522_;
v___y_478_ = v___x_524_;
v___y_479_ = v_a_523_;
v___y_480_ = v_a_515_;
v___y_481_ = v___x_525_;
goto v___jp_474_;
}
else
{
lean_object* v_val_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
v_val_526_ = lean_ctor_get(v_pat_x3f_511_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_pat_x3f_511_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v_pat_x3f_511_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_val_526_);
lean_dec(v_pat_x3f_511_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_val_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
v___y_475_ = v___y_512_;
v___y_476_ = v_a_519_;
v___y_477_ = v_a_522_;
v___y_478_ = v___x_524_;
v___y_479_ = v_a_523_;
v___y_480_ = v_a_515_;
v___y_481_ = v___x_531_;
goto v___jp_474_;
}
}
}
}
else
{
lean_dec(v_a_519_);
lean_dec(v_a_515_);
lean_dec(v_pat_x3f_511_);
return v___x_521_;
}
}
else
{
lean_object* v_a_534_; lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_515_);
lean_dec(v_pat_x3f_511_);
lean_dec(v_withTk_x3f_510_);
v_a_534_ = lean_ctor_get(v___x_518_, 0);
v_a_535_ = lean_ctor_get(v___x_518_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_518_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_inc(v_a_534_);
lean_dec(v___x_518_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_534_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_dec(v_pat_x3f_511_);
lean_dec(v_withTk_x3f_510_);
lean_dec(v___x_508_);
return v___x_514_;
}
}
}
v___jp_474_:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Fmt_fmt_x3f(v___y_481_, v___y_475_, v___y_479_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_502_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_a_484_ = lean_ctor_get(v___x_482_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_502_ == 0)
{
v___x_486_ = v___x_482_;
v_isShared_487_ = v_isSharedCheck_502_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_502_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint8_t v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_488_ = 1;
lean_inc_ref(v___y_478_);
v___x_489_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v___y_478_, v___y_480_, v___y_476_, v___x_488_);
lean_dec_ref(v___y_476_);
v___x_490_ = 0;
v___x_491_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v___y_477_, v_a_483_, v___x_490_);
v___x_492_ = lean_unsigned_to_nat(2u);
v___x_493_ = lean_mk_empty_array_with_capacity(v___x_492_);
v___x_494_ = lean_array_push(v___x_493_, v___x_489_);
v___x_495_ = lean_array_push(v___x_494_, v___x_491_);
v___x_496_ = 0;
v___x_497_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_497_, 0, v___x_473_);
lean_ctor_set_uint8(v___x_497_, 1, v___x_496_);
lean_ctor_set_uint8(v___x_497_, 2, v___x_496_);
lean_ctor_set_uint8(v___x_497_, 3, v___x_496_);
v___x_498_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_495_, v___x_497_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_498_);
v___x_500_ = v___x_486_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_a_484_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
else
{
lean_dec_ref(v___y_480_);
lean_dec_ref(v___y_477_);
lean_dec_ref(v___y_476_);
return v___x_482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticRCases___boxed(lean_object* v_x_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Fmt_fmtTacticRCases(v_x_558_, v_a_559_, v_a_560_);
lean_dec_ref(v_a_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1(){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_568_ = l_Lean_Fmt_fmtAttribute;
v___x_569_ = ((lean_object*)(l_Lean_Fmt_fmtTacticRCases___closed__1));
v___x_570_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___closed__1));
v___x_571_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticRCases___boxed), 3, 0);
v___x_572_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_568_, v___x_569_, v___x_570_, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1___boxed(lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1();
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticObtain(lean_object* v_x_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___y_587_; uint8_t v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; 
v___x_584_ = ((lean_object*)(l_Lean_Fmt_fmtTacticObtain___closed__1));
lean_inc(v_x_581_);
v___x_585_ = l_Lean_Syntax_isOfKind(v_x_581_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v_x_581_);
v___x_615_ = l_Lean_Fmt_Error_partialFormatter;
v___x_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_a_583_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v_obtainTk_672_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v_assignTk_x3f_678_; lean_object* v_vals_x3f_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___x_696_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v_colonTk_x3f_700_; lean_object* v_type_x3f_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v_pat_x3f_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_617_ = lean_unsigned_to_nat(0u);
v_obtainTk_672_ = l_Lean_Syntax_getArg(v_x_581_, v___x_617_);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_731_ = l_Lean_Syntax_getArg(v_x_581_, v___x_696_);
v___x_732_ = l_Lean_Syntax_isNone(v___x_731_);
if (v___x_732_ == 0)
{
uint8_t v___x_733_; 
lean_inc(v___x_731_);
v___x_733_ = l_Lean_Syntax_matchesNull(v___x_731_, v___x_696_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec(v___x_731_);
lean_dec(v_obtainTk_672_);
lean_dec(v_x_581_);
v___x_734_ = l_Lean_Fmt_Error_partialFormatter;
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v_a_583_);
return v___x_735_;
}
else
{
lean_object* v_pat_x3f_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_pat_x3f_736_ = l_Lean_Syntax_getArg(v___x_731_, v___x_617_);
lean_dec(v___x_731_);
v___x_737_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatMed___closed__4));
lean_inc(v_pat_x3f_736_);
v___x_738_ = l_Lean_Syntax_isOfKind(v_pat_x3f_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec(v_pat_x3f_736_);
lean_dec(v_obtainTk_672_);
lean_dec(v_x_581_);
v___x_739_ = l_Lean_Fmt_Error_partialFormatter;
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v_a_583_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; 
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_pat_x3f_736_);
v_pat_x3f_717_ = v___x_741_;
v___y_718_ = v_a_582_;
v___y_719_ = v_a_583_;
goto v___jp_716_;
}
}
}
else
{
lean_object* v___x_742_; 
lean_dec(v___x_731_);
v___x_742_ = lean_box(0);
v_pat_x3f_717_ = v___x_742_;
v___y_718_ = v_a_582_;
v___y_719_ = v_a_583_;
goto v___jp_716_;
}
v___jp_618_:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Fmt_fmt_x3f(v___y_627_, v___y_621_, v___y_620_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v_a_630_; lean_object* v___x_631_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
v_a_630_ = lean_ctor_get(v___x_628_, 1);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_628_, 2);
v___x_631_ = l_Lean_Fmt_fmt_x3f(v___y_624_, v___y_621_, v_a_630_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v_a_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
v_a_633_ = lean_ctor_get(v___x_631_, 1);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_631_, 2);
v___x_634_ = 0;
v___x_635_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_635_, 0, v___x_585_);
lean_ctor_set_uint8(v___x_635_, 1, v___x_634_);
lean_ctor_set_uint8(v___x_635_, 2, v___x_585_);
lean_ctor_set_uint8(v___x_635_, 3, v___x_585_);
v___x_636_ = l_Lean_Fmt_Layouts_typeAscription(v___y_622_, v___y_626_, v_a_629_, v___x_635_);
lean_dec_ref_known(v___x_635_, 0);
v___x_637_ = lean_mk_empty_array_with_capacity(v___y_619_);
v___x_638_ = lean_array_push(v___x_637_, v___y_625_);
v___x_639_ = lean_array_push(v___x_638_, v___x_636_);
v___x_640_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_640_, 0, v___x_585_);
lean_ctor_set_uint8(v___x_640_, 1, v___x_634_);
lean_ctor_set_uint8(v___x_640_, 2, v___x_634_);
lean_ctor_set_uint8(v___x_640_, 3, v___x_634_);
v___x_641_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_639_, v___x_640_);
v___x_642_ = ((lean_object*)(l_Lean_Fmt_fmtRCasesPatTuple___closed__2));
if (lean_obj_tag(v___y_623_) == 0)
{
lean_object* v___x_643_; 
v___x_643_ = ((lean_object*)(l_Lean_Fmt_fmtRIntroPatBinder___closed__2));
v___y_587_ = v_a_632_;
v___y_588_ = v___x_634_;
v___y_589_ = v___y_621_;
v___y_590_ = v___x_641_;
v___y_591_ = v___x_642_;
v___y_592_ = v_a_633_;
v___y_593_ = v___x_643_;
goto v___jp_586_;
}
else
{
lean_object* v_val_644_; 
v_val_644_ = lean_ctor_get(v___y_623_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v___y_623_, 1);
v___y_587_ = v_a_632_;
v___y_588_ = v___x_634_;
v___y_589_ = v___y_621_;
v___y_590_ = v___x_641_;
v___y_591_ = v___x_642_;
v___y_592_ = v_a_633_;
v___y_593_ = v_val_644_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_a_629_);
lean_dec_ref(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v___x_631_;
}
}
else
{
lean_dec_ref(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v___x_628_;
}
}
v___jp_645_:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Fmt_fmt_x3f(v___y_654_, v___y_649_, v___y_648_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v_a_657_; lean_object* v___x_658_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
v_a_657_ = lean_ctor_get(v___x_655_, 1);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_655_, 2);
v___x_658_ = l_Lean_Fmt_fmt_x3f(v___y_647_, v___y_649_, v_a_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
if (lean_obj_tag(v___y_653_) == 0)
{
lean_object* v_a_659_; lean_object* v_a_660_; lean_object* v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
v_a_660_ = lean_ctor_get(v___x_658_, 1);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_658_, 2);
v___x_661_ = lean_box(0);
v___y_619_ = v___y_646_;
v___y_620_ = v_a_660_;
v___y_621_ = v___y_649_;
v___y_622_ = v_a_656_;
v___y_623_ = v___y_650_;
v___y_624_ = v___y_651_;
v___y_625_ = v___y_652_;
v___y_626_ = v_a_659_;
v___y_627_ = v___x_661_;
goto v___jp_618_;
}
else
{
lean_object* v_a_662_; lean_object* v_a_663_; lean_object* v_val_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_a_662_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_662_);
v_a_663_ = lean_ctor_get(v___x_658_, 1);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_658_, 2);
v_val_664_ = lean_ctor_get(v___y_653_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___y_653_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___y_653_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_val_664_);
lean_dec(v___y_653_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_val_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
v___y_619_ = v___y_646_;
v___y_620_ = v_a_663_;
v___y_621_ = v___y_649_;
v___y_622_ = v_a_656_;
v___y_623_ = v___y_650_;
v___y_624_ = v___y_651_;
v___y_625_ = v___y_652_;
v___y_626_ = v_a_662_;
v___y_627_ = v___x_669_;
goto v___jp_618_;
}
}
}
}
else
{
lean_dec(v_a_656_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec(v___y_650_);
return v___x_658_;
}
}
else
{
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec(v___y_650_);
lean_dec(v___y_647_);
return v___x_655_;
}
}
v___jp_673_:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Fmt_fmt(v_obtainTk_672_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_682_) == 0)
{
if (lean_obj_tag(v___y_675_) == 0)
{
lean_object* v_a_683_; lean_object* v_a_684_; lean_object* v___x_685_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
v_a_684_ = lean_ctor_get(v___x_682_, 1);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_682_, 2);
v___x_685_ = lean_box(0);
v___y_646_ = v___y_674_;
v___y_647_ = v___y_676_;
v___y_648_ = v_a_684_;
v___y_649_ = v___y_680_;
v___y_650_ = v_vals_x3f_679_;
v___y_651_ = v_assignTk_x3f_678_;
v___y_652_ = v_a_683_;
v___y_653_ = v___y_677_;
v___y_654_ = v___x_685_;
goto v___jp_645_;
}
else
{
lean_object* v_a_686_; lean_object* v_a_687_; lean_object* v_val_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
v_a_686_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_686_);
v_a_687_ = lean_ctor_get(v___x_682_, 1);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_682_, 2);
v_val_688_ = lean_ctor_get(v___y_675_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___y_675_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___y_675_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_val_688_);
lean_dec(v___y_675_);
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
v___y_646_ = v___y_674_;
v___y_647_ = v___y_676_;
v___y_648_ = v_a_687_;
v___y_649_ = v___y_680_;
v___y_650_ = v_vals_x3f_679_;
v___y_651_ = v_assignTk_x3f_678_;
v___y_652_ = v_a_686_;
v___y_653_ = v___y_677_;
v___y_654_ = v___x_693_;
goto v___jp_645_;
}
}
}
}
else
{
lean_dec(v_vals_x3f_679_);
lean_dec(v_assignTk_x3f_678_);
lean_dec(v___y_677_);
lean_dec(v___y_676_);
lean_dec(v___y_675_);
return v___x_682_;
}
}
v___jp_697_:
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_704_ = lean_unsigned_to_nat(3u);
v___x_705_ = l_Lean_Syntax_getArg(v_x_581_, v___x_704_);
lean_dec(v_x_581_);
v___x_706_ = l_Lean_Syntax_isNone(v___x_705_);
if (v___x_706_ == 0)
{
uint8_t v___x_707_; 
lean_inc(v___x_705_);
v___x_707_ = l_Lean_Syntax_matchesNull(v___x_705_, v___y_698_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v___x_705_);
lean_dec(v_type_x3f_701_);
lean_dec(v_colonTk_x3f_700_);
lean_dec(v___y_699_);
lean_dec(v_obtainTk_672_);
v___x_708_ = l_Lean_Fmt_Error_partialFormatter;
v___x_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___y_703_);
return v___x_709_;
}
else
{
lean_object* v_assignTk_x3f_710_; lean_object* v___x_711_; lean_object* v_vals_x3f_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_assignTk_x3f_710_ = l_Lean_Syntax_getArg(v___x_705_, v___x_617_);
v___x_711_ = l_Lean_Syntax_getArg(v___x_705_, v___x_696_);
lean_dec(v___x_705_);
v_vals_x3f_712_ = l_Lean_Syntax_getArgs(v___x_711_);
lean_dec(v___x_711_);
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v_assignTk_x3f_710_);
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v_vals_x3f_712_);
v___y_674_ = v___y_698_;
v___y_675_ = v___y_699_;
v___y_676_ = v_colonTk_x3f_700_;
v___y_677_ = v_type_x3f_701_;
v_assignTk_x3f_678_ = v___x_713_;
v_vals_x3f_679_ = v___x_714_;
v___y_680_ = v___y_702_;
v___y_681_ = v___y_703_;
goto v___jp_673_;
}
}
else
{
lean_object* v___x_715_; 
lean_dec(v___x_705_);
v___x_715_ = lean_box(0);
v___y_674_ = v___y_698_;
v___y_675_ = v___y_699_;
v___y_676_ = v_colonTk_x3f_700_;
v___y_677_ = v_type_x3f_701_;
v_assignTk_x3f_678_ = v___x_715_;
v_vals_x3f_679_ = v___x_715_;
v___y_680_ = v___y_702_;
v___y_681_ = v___y_703_;
goto v___jp_673_;
}
}
v___jp_716_:
{
lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_720_ = lean_unsigned_to_nat(2u);
v___x_721_ = l_Lean_Syntax_getArg(v_x_581_, v___x_720_);
v___x_722_ = l_Lean_Syntax_isNone(v___x_721_);
if (v___x_722_ == 0)
{
uint8_t v___x_723_; 
lean_inc(v___x_721_);
v___x_723_ = l_Lean_Syntax_matchesNull(v___x_721_, v___x_720_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec(v___x_721_);
lean_dec(v_pat_x3f_717_);
lean_dec(v_obtainTk_672_);
lean_dec(v_x_581_);
v___x_724_ = l_Lean_Fmt_Error_partialFormatter;
v___x_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___y_719_);
return v___x_725_;
}
else
{
lean_object* v_colonTk_x3f_726_; lean_object* v_type_x3f_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_colonTk_x3f_726_ = l_Lean_Syntax_getArg(v___x_721_, v___x_617_);
v_type_x3f_727_ = l_Lean_Syntax_getArg(v___x_721_, v___x_696_);
lean_dec(v___x_721_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_colonTk_x3f_726_);
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v_type_x3f_727_);
v___y_698_ = v___x_720_;
v___y_699_ = v_pat_x3f_717_;
v_colonTk_x3f_700_ = v___x_728_;
v_type_x3f_701_ = v___x_729_;
v___y_702_ = v___y_718_;
v___y_703_ = v___y_719_;
goto v___jp_697_;
}
}
else
{
lean_object* v___x_730_; 
lean_dec(v___x_721_);
v___x_730_ = lean_box(0);
v___y_698_ = v___x_720_;
v___y_699_ = v_pat_x3f_717_;
v_colonTk_x3f_700_ = v___x_730_;
v_type_x3f_701_ = v___x_730_;
v___y_702_ = v___y_718_;
v___y_703_ = v___y_719_;
goto v___jp_697_;
}
}
}
v___jp_586_:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Fmt_fmtTSepArray___redArg(v___y_593_, v___y_589_, v___y_592_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_605_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_a_596_ = lean_ctor_get(v___x_594_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_605_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
lean_inc_ref(v___y_591_);
v___x_600_ = l_Lean_Fmt_Layouts_sepHorizontalOrVertical(v___y_591_, v_a_595_, v___x_585_);
lean_dec(v_a_595_);
v___x_601_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___y_590_, v___y_587_, v___x_600_, v___y_588_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_601_);
v___x_603_ = v___x_598_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_a_596_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v___y_590_);
lean_dec_ref(v___y_587_);
v_a_606_ = lean_ctor_get(v___x_594_, 0);
v_a_607_ = lean_ctor_get(v___x_594_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_594_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_inc(v_a_606_);
lean_dec(v___x_594_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_606_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticObtain___boxed(lean_object* v_x_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Fmt_fmtTacticObtain(v_x_743_, v_a_744_, v_a_745_);
lean_dec_ref(v_a_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1(){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_753_ = l_Lean_Fmt_fmtAttribute;
v___x_754_ = ((lean_object*)(l_Lean_Fmt_fmtTacticObtain___closed__1));
v___x_755_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___closed__1));
v___x_756_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticObtain___boxed), 3, 0);
v___x_757_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_753_, v___x_754_, v___x_755_, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1___boxed(lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1();
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticRIntro(lean_object* v_x_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; 
v___x_769_ = ((lean_object*)(l_Lean_Fmt_fmtTacticRIntro___closed__1));
lean_inc(v_x_766_);
v___x_770_ = l_Lean_Syntax_isOfKind(v_x_766_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec(v_x_766_);
v___x_798_ = l_Lean_Fmt_Error_partialFormatter;
v___x_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v_a_768_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v_rintroTk_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_colonTk_x3f_805_; lean_object* v_type_x3f_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v_rintroTk_801_ = l_Lean_Syntax_getArg(v_x_766_, v___x_800_);
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = l_Lean_Syntax_getArg(v_x_766_, v___x_802_);
v___x_839_ = lean_unsigned_to_nat(2u);
v___x_840_ = l_Lean_Syntax_getArg(v_x_766_, v___x_839_);
lean_dec(v_x_766_);
v___x_841_ = l_Lean_Syntax_isNone(v___x_840_);
if (v___x_841_ == 0)
{
uint8_t v___x_842_; 
lean_inc(v___x_840_);
v___x_842_ = l_Lean_Syntax_matchesNull(v___x_840_, v___x_839_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec(v___x_840_);
lean_dec(v___x_803_);
lean_dec(v_rintroTk_801_);
v___x_843_ = l_Lean_Fmt_Error_partialFormatter;
v___x_844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v_a_768_);
return v___x_844_;
}
else
{
lean_object* v_colonTk_x3f_845_; lean_object* v_type_x3f_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_colonTk_x3f_845_ = l_Lean_Syntax_getArg(v___x_840_, v___x_800_);
v_type_x3f_846_ = l_Lean_Syntax_getArg(v___x_840_, v___x_802_);
lean_dec(v___x_840_);
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v_colonTk_x3f_845_);
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v_type_x3f_846_);
v_colonTk_x3f_805_ = v___x_847_;
v_type_x3f_806_ = v___x_848_;
v___y_807_ = v_a_767_;
v___y_808_ = v_a_768_;
goto v___jp_804_;
}
}
else
{
lean_object* v___x_849_; 
lean_dec(v___x_840_);
v___x_849_ = lean_box(0);
v_colonTk_x3f_805_ = v___x_849_;
v_type_x3f_806_ = v___x_849_;
v___y_807_ = v_a_767_;
v___y_808_ = v_a_768_;
goto v___jp_804_;
}
v___jp_804_:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Fmt_fmt(v_rintroTk_801_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v_a_811_; lean_object* v_pats_812_; lean_object* v___x_813_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
v_a_811_ = lean_ctor_get(v___x_809_, 1);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_809_, 2);
v_pats_812_ = l_Lean_Syntax_getArgs(v___x_803_);
lean_dec(v___x_803_);
v___x_813_ = l_Lean_Fmt_fmtArray___redArg(v_pats_812_, v___y_807_, v_a_811_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v_a_815_; lean_object* v___x_816_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
v_a_815_ = lean_ctor_get(v___x_813_, 1);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_813_, 2);
v___x_816_ = l_Lean_Fmt_fmt_x3f(v_colonTk_x3f_805_, v___y_807_, v_a_815_);
if (lean_obj_tag(v___x_816_) == 0)
{
if (lean_obj_tag(v_type_x3f_806_) == 0)
{
lean_object* v_a_817_; lean_object* v_a_818_; lean_object* v___x_819_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
v_a_818_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_816_, 2);
v___x_819_ = lean_box(0);
v___y_772_ = v_a_814_;
v___y_773_ = v_a_818_;
v___y_774_ = v___y_807_;
v___y_775_ = v_a_817_;
v___y_776_ = v_a_810_;
v___y_777_ = v___x_819_;
goto v___jp_771_;
}
else
{
lean_object* v_a_820_; lean_object* v_a_821_; lean_object* v_val_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_a_820_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_820_);
v_a_821_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_816_, 2);
v_val_822_ = lean_ctor_get(v_type_x3f_806_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v_type_x3f_806_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v_type_x3f_806_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_val_822_);
lean_dec(v_type_x3f_806_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_val_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
v___y_772_ = v_a_814_;
v___y_773_ = v_a_821_;
v___y_774_ = v___y_807_;
v___y_775_ = v_a_820_;
v___y_776_ = v_a_810_;
v___y_777_ = v___x_827_;
goto v___jp_771_;
}
}
}
}
else
{
lean_dec(v_a_814_);
lean_dec(v_a_810_);
lean_dec(v_type_x3f_806_);
return v___x_816_;
}
}
else
{
lean_object* v_a_830_; lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_a_810_);
lean_dec(v_type_x3f_806_);
lean_dec(v_colonTk_x3f_805_);
v_a_830_ = lean_ctor_get(v___x_813_, 0);
v_a_831_ = lean_ctor_get(v___x_813_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_813_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_inc(v_a_830_);
lean_dec(v___x_813_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_830_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_dec(v_type_x3f_806_);
lean_dec(v_colonTk_x3f_805_);
lean_dec(v___x_803_);
return v___x_809_;
}
}
}
v___jp_771_:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Fmt_fmt_x3f(v___y_777_, v___y_774_, v___y_773_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_797_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_a_780_ = lean_ctor_get(v___x_778_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_797_ == 0)
{
v___x_782_ = v___x_778_;
v_isShared_783_ = v_isSharedCheck_797_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_797_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_784_ = l_Lean_Fmt_Layouts_fill(v___y_772_);
lean_dec_ref(v___y_772_);
v___x_785_ = 0;
v___x_786_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_786_, 0, v___x_770_);
lean_ctor_set_uint8(v___x_786_, 1, v___x_785_);
lean_ctor_set_uint8(v___x_786_, 2, v___x_770_);
lean_ctor_set_uint8(v___x_786_, 3, v___x_770_);
v___x_787_ = l_Lean_Fmt_Layouts_typeAscription(v___x_784_, v___y_775_, v_a_779_, v___x_786_);
lean_dec_ref_known(v___x_786_, 0);
v___x_788_ = lean_unsigned_to_nat(2u);
v___x_789_ = lean_mk_empty_array_with_capacity(v___x_788_);
v___x_790_ = lean_array_push(v___x_789_, v___y_776_);
v___x_791_ = lean_array_push(v___x_790_, v___x_787_);
v___x_792_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_792_, 0, v___x_770_);
lean_ctor_set_uint8(v___x_792_, 1, v___x_785_);
lean_ctor_set_uint8(v___x_792_, 2, v___x_785_);
lean_ctor_set_uint8(v___x_792_, 3, v___x_785_);
v___x_793_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_791_, v___x_792_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_793_);
v___x_795_ = v___x_782_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_a_780_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_dec_ref(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec_ref(v___y_772_);
return v___x_778_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticRIntro___boxed(lean_object* v_x_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Fmt_fmtTacticRIntro(v_x_850_, v_a_851_, v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1(){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_860_ = l_Lean_Fmt_fmtAttribute;
v___x_861_ = ((lean_object*)(l_Lean_Fmt_fmtTacticRIntro___closed__1));
v___x_862_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___closed__1));
v___x_863_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticRIntro___boxed), 3, 0);
v___x_864_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_860_, v___x_861_, v___x_862_, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1___boxed(lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1();
return v_res_866_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_RCases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatMed___regBuiltin_Lean_Fmt_fmtRCasesPatMed__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatLo___regBuiltin_Lean_Fmt_fmtRCasesPatLo__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatOne___regBuiltin_Lean_Fmt_fmtRCasesPatOne__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatExplicit___regBuiltin_Lean_Fmt_fmtRCasesPatExplicit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatTuple___regBuiltin_Lean_Fmt_fmtRCasesPatTuple__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRCasesPatParen___regBuiltin_Lean_Fmt_fmtRCasesPatParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatOne___regBuiltin_Lean_Fmt_fmtRIntroPatOne__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtRIntroPatBinder___regBuiltin_Lean_Fmt_fmtRIntroPatBinder__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRCases___regBuiltin_Lean_Fmt_fmtTacticRCases__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticObtain___regBuiltin_Lean_Fmt_fmtTacticObtain__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_RCases_0__Lean_Fmt_fmtTacticRIntro___regBuiltin_Lean_Fmt_fmtTacticRIntro__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_RCases(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_RCases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_RCases(builtin);
}
#ifdef __cplusplus
}
#endif
