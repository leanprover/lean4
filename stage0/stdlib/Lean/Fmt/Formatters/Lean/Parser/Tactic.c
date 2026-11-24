// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Parser.Tactic
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Lean.Parser.Term.Basic meta import Lean.Parser.Tactic import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnknownTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnknownTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unknown"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 186, 215, 255, 42, 124, 128, 137)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__4_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__5 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__5_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtUnknownTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__6 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(115, 107, 85, 51, 88, 178, 24, 153)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__7 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Fmt_fmtTacticMatch___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 240, 216, 203, 28, 130, 220)}};
static const lean_object* l_Lean_Fmt_fmtTacticMatch___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtTacticMatch___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtTacticMatch___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtTacticMatch___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtTacticMatch___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Fmt_fmtTacticMatch___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__4_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Fmt_fmtTacticMatch___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtTacticMatch___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtTacticMatch___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtTacticMatch___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l_Lean_Fmt_fmtTacticMatch___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__8_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__8_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__7_value),LEAN_SCALAR_PTR_LITERAL(81, 58, 182, 248, 224, 44, 170, 90)}};
static const lean_object* l_Lean_Fmt_fmtTacticMatch___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__8_value;
static const lean_string_object l_Lean_Fmt_fmtTacticMatch___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Fmt_fmtTacticMatch___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__9_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__10_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticMatch___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__10_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__9_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Fmt_fmtTacticMatch___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtTacticMatch___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticMatch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticMatch___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtTacticMatch"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 138, 214, 111, 200, 217, 115, 35)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtIntroMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "introMatch"};
static const lean_object* l_Lean_Fmt_fmtIntroMatch___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtIntroMatch___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtIntroMatch___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtIntroMatch___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIntroMatch___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtIntroMatch___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIntroMatch___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtIntroMatch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIntroMatch___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtIntroMatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 42, 46, 143, 104, 41, 172, 166)}};
static const lean_object* l_Lean_Fmt_fmtIntroMatch___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtIntroMatch___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIntroMatch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIntroMatch___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtIntroMatch"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 73, 87, 37, 132, 116, 70, 157)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnknownTactic(lean_object* v_stx_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_1_, v___x_4_, v_a_3_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v_a_6_; lean_object* v_a_7_; lean_object* v___x_8_; 
v_a_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_a_6_);
v_a_7_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_a_7_);
lean_dec_ref_known(v___x_5_, 2);
v___x_8_ = l_Lean_Fmt_fmt(v_a_6_, v_a_2_, v_a_7_);
return v___x_8_;
}
else
{
lean_object* v_a_9_; lean_object* v_a_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_17_; 
v_a_9_ = lean_ctor_get(v___x_5_, 0);
v_a_10_ = lean_ctor_get(v___x_5_, 1);
v_isSharedCheck_17_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_17_ == 0)
{
v___x_12_ = v___x_5_;
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_a_10_);
lean_inc(v_a_9_);
lean_dec(v___x_5_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_15_; 
if (v_isShared_13_ == 0)
{
v___x_15_ = v___x_12_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_a_9_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_a_10_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnknownTactic___boxed(lean_object* v_stx_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Fmt_fmtUnknownTactic(v_stx_18_, v_a_19_, v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_stx_18_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1(){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_38_ = l_Lean_Fmt_fmtAttribute;
v___x_39_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__4));
v___x_40_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___closed__7));
v___x_41_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtUnknownTactic___boxed), 3, 0);
v___x_42_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_38_, v___x_39_, v___x_40_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1___boxed(lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1();
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticMatch(lean_object* v_x_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; lean_object* v___y_79_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___y_83_; lean_object* v___y_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v___y_132_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___y_136_; lean_object* v___y_137_; lean_object* v___y_138_; 
v___x_76_ = ((lean_object*)(l_Lean_Fmt_fmtTacticMatch___closed__1));
lean_inc(v_x_73_);
v___x_77_ = l_Lean_Syntax_isOfKind(v_x_73_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_x_73_);
v___x_153_ = l_Lean_Fmt_Error_partialFormatter;
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_a_75_);
return v___x_154_;
}
else
{
lean_object* v___x_155_; lean_object* v_matchTk_156_; lean_object* v___y_158_; lean_object* v_motive_x3f_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___x_186_; lean_object* v_generalizingParam_x3f_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v_matchTk_156_ = l_Lean_Syntax_getArg(v_x_73_, v___x_155_);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_204_ = l_Lean_Syntax_getArg(v_x_73_, v___x_186_);
v___x_205_ = l_Lean_Syntax_isNone(v___x_204_);
if (v___x_205_ == 0)
{
uint8_t v___x_206_; 
lean_inc(v___x_204_);
v___x_206_ = l_Lean_Syntax_matchesNull(v___x_204_, v___x_186_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v___x_204_);
lean_dec(v_matchTk_156_);
lean_dec(v_x_73_);
v___x_207_ = l_Lean_Fmt_Error_partialFormatter;
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_a_75_);
return v___x_208_;
}
else
{
lean_object* v_generalizingParam_x3f_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_generalizingParam_x3f_209_ = l_Lean_Syntax_getArg(v___x_204_, v___x_155_);
lean_dec(v___x_204_);
v___x_210_ = ((lean_object*)(l_Lean_Fmt_fmtTacticMatch___closed__10));
lean_inc(v_generalizingParam_x3f_209_);
v___x_211_ = l_Lean_Syntax_isOfKind(v_generalizingParam_x3f_209_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_generalizingParam_x3f_209_);
lean_dec(v_matchTk_156_);
lean_dec(v_x_73_);
v___x_212_ = l_Lean_Fmt_Error_partialFormatter;
v___x_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_a_75_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v_generalizingParam_x3f_209_);
v_generalizingParam_x3f_188_ = v___x_214_;
v___y_189_ = v_a_74_;
v___y_190_ = v_a_75_;
goto v___jp_187_;
}
}
}
else
{
lean_object* v___x_215_; 
lean_dec(v___x_204_);
v___x_215_ = lean_box(0);
v_generalizingParam_x3f_188_ = v___x_215_;
v___y_189_ = v_a_74_;
v___y_190_ = v_a_75_;
goto v___jp_187_;
}
v___jp_157_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_162_ = lean_unsigned_to_nat(5u);
v___x_163_ = l_Lean_Syntax_getArg(v_x_73_, v___x_162_);
v___x_164_ = ((lean_object*)(l_Lean_Fmt_fmtTacticMatch___closed__5));
lean_inc(v___x_163_);
v___x_165_ = l_Lean_Syntax_isOfKind(v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v___x_163_);
lean_dec(v_motive_x3f_159_);
lean_dec(v___y_158_);
lean_dec(v_matchTk_156_);
lean_dec(v_x_73_);
v___x_166_ = l_Lean_Fmt_Error_partialFormatter;
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___y_161_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Fmt_fmt(v_matchTk_156_, v___y_160_, v___y_161_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v_a_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_withTk_174_; lean_object* v___x_175_; lean_object* v_matchDiscrs_176_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
v_a_170_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_a_170_);
lean_dec_ref_known(v___x_168_, 2);
v___x_171_ = lean_unsigned_to_nat(3u);
v___x_172_ = l_Lean_Syntax_getArg(v_x_73_, v___x_171_);
v___x_173_ = lean_unsigned_to_nat(4u);
v_withTk_174_ = l_Lean_Syntax_getArg(v_x_73_, v___x_173_);
lean_dec(v_x_73_);
v___x_175_ = ((lean_object*)(l_Lean_Fmt_fmtTacticMatch___closed__6));
v_matchDiscrs_176_ = l_Lean_Syntax_getArgs(v___x_172_);
lean_dec(v___x_172_);
if (lean_obj_tag(v___y_158_) == 0)
{
lean_object* v___x_177_; 
v___x_177_ = lean_box(0);
v___y_129_ = v___x_171_;
v___y_130_ = v___x_175_;
v___y_131_ = v___y_160_;
v___y_132_ = v_matchDiscrs_176_;
v___y_133_ = v_motive_x3f_159_;
v___y_134_ = v_withTk_174_;
v___y_135_ = v_a_170_;
v___y_136_ = v_a_169_;
v___y_137_ = v___x_163_;
v___y_138_ = v___x_177_;
goto v___jp_128_;
}
else
{
lean_object* v_val_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
v_val_178_ = lean_ctor_get(v___y_158_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___y_158_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___y_158_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_val_178_);
lean_dec(v___y_158_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_val_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
v___y_129_ = v___x_171_;
v___y_130_ = v___x_175_;
v___y_131_ = v___y_160_;
v___y_132_ = v_matchDiscrs_176_;
v___y_133_ = v_motive_x3f_159_;
v___y_134_ = v_withTk_174_;
v___y_135_ = v_a_170_;
v___y_136_ = v_a_169_;
v___y_137_ = v___x_163_;
v___y_138_ = v___x_183_;
goto v___jp_128_;
}
}
}
}
else
{
lean_dec(v___x_163_);
lean_dec(v_motive_x3f_159_);
lean_dec(v___y_158_);
lean_dec(v_x_73_);
return v___x_168_;
}
}
}
v___jp_187_:
{
lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_191_ = lean_unsigned_to_nat(2u);
v___x_192_ = l_Lean_Syntax_getArg(v_x_73_, v___x_191_);
v___x_193_ = l_Lean_Syntax_isNone(v___x_192_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; 
lean_inc(v___x_192_);
v___x_194_ = l_Lean_Syntax_matchesNull(v___x_192_, v___x_186_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v___x_192_);
lean_dec(v_generalizingParam_x3f_188_);
lean_dec(v_matchTk_156_);
lean_dec(v_x_73_);
v___x_195_ = l_Lean_Fmt_Error_partialFormatter;
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___y_190_);
return v___x_196_;
}
else
{
lean_object* v_motive_x3f_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_motive_x3f_197_ = l_Lean_Syntax_getArg(v___x_192_, v___x_155_);
lean_dec(v___x_192_);
v___x_198_ = ((lean_object*)(l_Lean_Fmt_fmtTacticMatch___closed__8));
lean_inc(v_motive_x3f_197_);
v___x_199_ = l_Lean_Syntax_isOfKind(v_motive_x3f_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v_motive_x3f_197_);
lean_dec(v_generalizingParam_x3f_188_);
lean_dec(v_matchTk_156_);
lean_dec(v_x_73_);
v___x_200_ = l_Lean_Fmt_Error_partialFormatter;
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___y_190_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_202_, 0, v_motive_x3f_197_);
v___y_158_ = v_generalizingParam_x3f_188_;
v_motive_x3f_159_ = v___x_202_;
v___y_160_ = v___y_189_;
v___y_161_ = v___y_190_;
goto v___jp_157_;
}
}
}
else
{
lean_object* v___x_203_; 
lean_dec(v___x_192_);
v___x_203_ = lean_box(0);
v___y_158_ = v_generalizingParam_x3f_188_;
v_motive_x3f_159_ = v___x_203_;
v___y_160_ = v___y_189_;
v___y_161_ = v___y_190_;
goto v___jp_157_;
}
}
}
v___jp_78_:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Fmt_fmt_x3f(v___y_88_, v___y_82_, v___y_86_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v_a_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_a_90_);
v_a_91_ = lean_ctor_get(v___x_89_, 1);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_89_, 2);
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_93_, 0, v___x_77_);
lean_ctor_set_uint8(v___x_93_, 1, v___x_92_);
lean_ctor_set_uint8(v___x_93_, 2, v___x_92_);
lean_ctor_set_uint8(v___x_93_, 3, v___x_92_);
v___x_94_ = l_Lean_Fmt_fmtTSepArray___redArg(v___y_83_, v___y_82_, v_a_91_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_97_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_95_);
v_a_96_ = lean_ctor_get(v___x_94_, 1);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_94_, 2);
v___x_97_ = l_Lean_Fmt_fmt(v___y_84_, v___y_82_, v_a_96_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v_a_99_; lean_object* v___x_100_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
v_a_99_ = lean_ctor_get(v___x_97_, 1);
lean_inc(v_a_99_);
lean_dec_ref_known(v___x_97_, 2);
v___x_100_ = l_Lean_Fmt_fmt(v___y_87_, v___y_82_, v_a_99_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_118_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_a_102_ = lean_ctor_get(v___x_100_, 1);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_118_ == 0)
{
v___x_104_ = v___x_100_;
v_isShared_105_ = v_isSharedCheck_118_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_118_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_106_ = lean_mk_empty_array_with_capacity(v___y_80_);
v___x_107_ = lean_array_push(v___x_106_, v___y_85_);
v___x_108_ = lean_array_push(v___x_107_, v___y_79_);
v___x_109_ = lean_array_push(v___x_108_, v_a_90_);
v___x_110_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_109_, v___x_93_);
v___x_111_ = 1;
lean_inc_ref(v___y_81_);
v___x_112_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v___y_81_, v___x_110_, v_a_95_, v___x_111_);
lean_dec(v_a_95_);
v___x_113_ = ((lean_object*)(l_Lean_Fmt_fmtTacticMatch___closed__2));
v___x_114_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_112_, v_a_98_, v_a_101_, v___x_113_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_114_);
v___x_116_ = v___x_104_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_a_102_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
else
{
lean_dec(v_a_98_);
lean_dec(v_a_95_);
lean_dec_ref_known(v___x_93_, 0);
lean_dec(v_a_90_);
lean_dec_ref(v___y_85_);
lean_dec_ref(v___y_79_);
return v___x_100_;
}
}
else
{
lean_dec(v_a_95_);
lean_dec_ref_known(v___x_93_, 0);
lean_dec(v_a_90_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_85_);
lean_dec_ref(v___y_79_);
return v___x_97_;
}
}
else
{
lean_object* v_a_119_; lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec_ref_known(v___x_93_, 0);
lean_dec(v_a_90_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_79_);
v_a_119_ = lean_ctor_get(v___x_94_, 0);
v_a_120_ = lean_ctor_get(v___x_94_, 1);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_94_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_inc(v_a_119_);
lean_dec(v___x_94_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_119_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
else
{
lean_dec(v___y_87_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec_ref(v___y_79_);
return v___x_89_;
}
}
v___jp_128_:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Fmt_fmt_x3f(v___y_138_, v___y_131_, v___y_135_);
if (lean_obj_tag(v___x_139_) == 0)
{
if (lean_obj_tag(v___y_133_) == 0)
{
lean_object* v_a_140_; lean_object* v_a_141_; lean_object* v___x_142_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
v_a_141_ = lean_ctor_get(v___x_139_, 1);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_139_, 2);
v___x_142_ = lean_box(0);
v___y_79_ = v_a_140_;
v___y_80_ = v___y_129_;
v___y_81_ = v___y_130_;
v___y_82_ = v___y_131_;
v___y_83_ = v___y_132_;
v___y_84_ = v___y_134_;
v___y_85_ = v___y_136_;
v___y_86_ = v_a_141_;
v___y_87_ = v___y_137_;
v___y_88_ = v___x_142_;
goto v___jp_78_;
}
else
{
lean_object* v_a_143_; lean_object* v_a_144_; lean_object* v_val_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_a_143_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_143_);
v_a_144_ = lean_ctor_get(v___x_139_, 1);
lean_inc(v_a_144_);
lean_dec_ref_known(v___x_139_, 2);
v_val_145_ = lean_ctor_get(v___y_133_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___y_133_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___y_133_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_val_145_);
lean_dec(v___y_133_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_val_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
v___y_79_ = v_a_143_;
v___y_80_ = v___y_129_;
v___y_81_ = v___y_130_;
v___y_82_ = v___y_131_;
v___y_83_ = v___y_132_;
v___y_84_ = v___y_134_;
v___y_85_ = v___y_136_;
v___y_86_ = v_a_144_;
v___y_87_ = v___y_137_;
v___y_88_ = v___x_150_;
goto v___jp_78_;
}
}
}
}
else
{
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticMatch___boxed(lean_object* v_x_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Fmt_fmtTacticMatch(v_x_216_, v_a_217_, v_a_218_);
lean_dec_ref(v_a_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1(){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_226_ = l_Lean_Fmt_fmtAttribute;
v___x_227_ = ((lean_object*)(l_Lean_Fmt_fmtTacticMatch___closed__1));
v___x_228_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___closed__1));
v___x_229_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticMatch___boxed), 3, 0);
v___x_230_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_226_, v___x_227_, v___x_228_, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1___boxed(lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1();
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIntroMatch(lean_object* v_x_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Fmt_fmtIntroMatch___closed__1));
lean_inc(v_x_239_);
v___x_243_ = l_Lean_Syntax_isOfKind(v_x_239_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_x_239_);
v___x_244_ = l_Lean_Fmt_Error_partialFormatter;
v___x_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v_a_241_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = l_Lean_Syntax_getArg(v_x_239_, v___x_246_);
v___x_248_ = ((lean_object*)(l_Lean_Fmt_fmtTacticMatch___closed__5));
lean_inc(v___x_247_);
v___x_249_ = l_Lean_Syntax_isOfKind(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec(v___x_247_);
lean_dec(v_x_239_);
v___x_250_ = l_Lean_Fmt_Error_partialFormatter;
v___x_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v_a_241_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v_introTk_253_; lean_object* v___x_254_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v_introTk_253_ = l_Lean_Syntax_getArg(v_x_239_, v___x_252_);
lean_dec(v_x_239_);
v___x_254_ = l_Lean_Fmt_fmt(v_introTk_253_, v_a_240_, v_a_241_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v_a_256_; lean_object* v___x_257_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
v_a_256_ = lean_ctor_get(v___x_254_, 1);
lean_inc(v_a_256_);
lean_dec_ref_known(v___x_254_, 2);
v___x_257_ = l_Lean_Fmt_fmt(v___x_247_, v_a_240_, v_a_256_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_271_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_a_259_ = lean_ctor_get(v___x_257_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_271_ == 0)
{
v___x_261_ = v___x_257_;
v_isShared_262_ = v_isSharedCheck_271_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_271_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_263_ = lean_unsigned_to_nat(2u);
v___x_264_ = lean_mk_empty_array_with_capacity(v___x_263_);
v___x_265_ = lean_array_push(v___x_264_, v_a_255_);
v___x_266_ = lean_array_push(v___x_265_, v_a_258_);
v___x_267_ = l_Lean_Fmt_Layouts_lines(v___x_266_);
lean_dec_ref(v___x_266_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_267_);
v___x_269_ = v___x_261_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_a_259_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
else
{
lean_dec(v_a_255_);
return v___x_257_;
}
}
else
{
lean_dec(v___x_247_);
return v___x_254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIntroMatch___boxed(lean_object* v_x_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Fmt_fmtIntroMatch(v_x_272_, v_a_273_, v_a_274_);
lean_dec_ref(v_a_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1(){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_282_ = l_Lean_Fmt_fmtAttribute;
v___x_283_ = ((lean_object*)(l_Lean_Fmt_fmtIntroMatch___closed__1));
v___x_284_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___closed__1));
v___x_285_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtIntroMatch___boxed), 3, 0);
v___x_286_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_282_, v___x_283_, v___x_284_, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1___boxed(lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1();
return v_res_288_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtUnknownTactic___regBuiltin_Lean_Fmt_fmtUnknownTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtTacticMatch___regBuiltin_Lean_Fmt_fmtTacticMatch__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Tactic_0__Lean_Fmt_fmtIntroMatch___regBuiltin_Lean_Fmt_fmtIntroMatch__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Tactic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Tactic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Parser_Tactic(builtin);
}
#ifdef __cplusplus
}
#endif
