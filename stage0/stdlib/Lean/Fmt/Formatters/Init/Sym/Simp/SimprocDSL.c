// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Sym.Simp.SimprocDSL
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Sym.Simp.SimprocDSL import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_collection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_infixFmtAttribute;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtSymSimprocAndThen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1)),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtSymSimprocAndThen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymSimprocAndThen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimprocAndThen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimprocAndThen___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtSymSimprocAndThen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymSimprocAndThen___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtSymSimprocAndThen___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSymSimprocAndThen___closed__2;
static lean_once_cell_t l_Lean_Fmt_fmtSymSimprocAndThen___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSymSimprocAndThen___closed__3;
static lean_once_cell_t l_Lean_Fmt_fmtSymSimprocAndThen___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSymSimprocAndThen___closed__4;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimprocAndThen;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andThen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(46, 183, 106, 149, 74, 106, 130, 246)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(231, 0, 84, 101, 13, 130, 212, 7)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtSymSimprocAndThen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__7 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(169, 119, 168, 215, 224, 241, 118, 236)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__8 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtSymSimprocOrElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtSymSimprocOrElse___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymSimprocOrElse___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimprocOrElse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimprocOrElse___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtSymSimprocOrElse___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymSimprocOrElse___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtSymSimprocOrElse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSymSimprocOrElse___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimprocOrElse;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orElse"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(46, 183, 106, 149, 74, 106, 130, 246)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 15, 104, 108, 253, 175, 57, 154)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtSymSimprocOrElse"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(213, 249, 127, 174, 140, 218, 38, 1)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymSimpRewriteSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rewriteSet"};
static const lean_object* l_Lean_Fmt_fmtSymSimpRewriteSet___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteSet___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(46, 183, 106, 149, 74, 106, 130, 246)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteSet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 237, 151, 14, 163, 181, 113, 140)}};
static const lean_object* l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSymSimpRewriteSet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtSymSimpRewriteSet___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteSet___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpRewriteSet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteSet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtSymSimpRewriteSet___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteSet___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpRewriteSet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpRewriteSet___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtSymSimpRewriteSet"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 152, 66, 20, 208, 173, 182, 7)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymSimpRewriteInline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "rewriteInline"};
static const lean_object* l_Lean_Fmt_fmtSymSimpRewriteInline___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteInline___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(46, 183, 106, 149, 74, 106, 130, 246)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteInline___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 37, 144, 204, 240, 250, 222, 75)}};
static const lean_object* l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSymSimpRewriteInline___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtSymSimpRewriteInline___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpRewriteInline___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpRewriteInline(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpRewriteInline___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtSymSimpRewriteInline"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 175, 195, 50, 17, 243, 184, 8)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymSimpArith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arith"};
static const lean_object* l_Lean_Fmt_fmtSymSimpArith___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpArith___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpArith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpArith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpArith___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpArith___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpArith___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpArith___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpArith___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(46, 183, 106, 149, 74, 106, 130, 246)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpArith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpArith___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtSymSimpArith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 150, 20, 176, 103, 123, 10, 91)}};
static const lean_object* l_Lean_Fmt_fmtSymSimpArith___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpArith___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpArith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpArith___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtSymSimpArith"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 30, 23, 2, 232, 126, 48, 153)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymSimprocParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simprocParen"};
static const lean_object* l_Lean_Fmt_fmtSymSimprocParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymSimprocParen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimprocParen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimprocParen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimprocParen___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimprocParen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimprocParen___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimprocParen___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimprocParen___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(46, 183, 106, 149, 74, 106, 130, 246)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimprocParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimprocParen___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtSymSimprocParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 24, 83, 62, 216, 237, 199, 219)}};
static const lean_object* l_Lean_Fmt_fmtSymSimprocParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymSimprocParen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimprocParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimprocParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtSymSimprocParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 107, 105, 80, 14, 92, 241, 203)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymDischargerParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dischParen"};
static const lean_object* l_Lean_Fmt_fmtSymDischargerParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymDischargerParen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymDischargerParen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDischargerParen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDischargerParen___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDischargerParen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDischargerParen___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDischargerParen___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDischargerParen___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(46, 183, 106, 149, 74, 106, 130, 246)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDischargerParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDischargerParen___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtSymDischargerParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 60, 196, 44, 146, 171, 74, 5)}};
static const lean_object* l_Lean_Fmt_fmtSymDischargerParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymDischargerParen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDischargerParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDischargerParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtSymDischargerParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 121, 161, 55, 48, 219, 66, 43)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymSimpFieldPre___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldPre___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSymSimpFieldPre___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "symSimpFieldPre"};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldPre___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldPre___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldPre___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldPre___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldPre___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__1_value),LEAN_SCALAR_PTR_LITERAL(55, 39, 173, 182, 117, 84, 135, 127)}};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldPre___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldPre(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldPre___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtSymSimpFieldPre"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 13, 11, 150, 81, 88, 210, 36)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymSimpFieldPost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "symSimpFieldPost"};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldPost___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPost___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldPost___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldPost___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPost___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldPost___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPost___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldPost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPost___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 158, 112, 0, 222, 65, 195, 224)}};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldPost___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPost___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldPost(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldPost___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtSymSimpFieldPost"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 223, 208, 198, 222, 145, 53, 150)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "symSimpFieldDischarger"};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 167, 59, 102, 151, 253, 11, 252)}};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldDischarger(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldDischarger___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "fmtSymSimpFieldDischarger"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 209, 176, 155, 28, 243, 247, 253)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "symSimpFieldMaxSteps"};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 59, 159, 191, 234, 244, 46, 27)}};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxSteps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxSteps___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtSymSimpFieldMaxSteps"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 133, 215, 249, 246, 192, 21, 249)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "symSimpFieldMaxDischargeDepth"};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 101, 101, 105, 195, 9, 110, 88)}};
static const lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "fmtSymSimpFieldMaxDischargeDepth"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 17, 204, 30, 51, 97, 182, 68)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRegisterSymSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "registerSymSimp"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimp___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimp___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSymSimpFieldPre___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterSymSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 45, 50, 162, 52, 223, 148, 3)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymSimp___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymSimp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymSimp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymSimp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtRegisterSymSimp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 41, 251, 49, 92, 199, 57, 52)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Fmt_fmtSymSimprocAndThen___closed__2(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_box(0);
v___x_7_ = lean_unsigned_to_nat(16u);
v___x_8_ = lean_mk_array(v___x_7_, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSymSimprocAndThen___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&l_Lean_Fmt_fmtSymSimprocAndThen___closed__2, &l_Lean_Fmt_fmtSymSimprocAndThen___closed__2_once, _init_l_Lean_Fmt_fmtSymSimprocAndThen___closed__2);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSymSimprocAndThen___closed__4(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_obj_once(&l_Lean_Fmt_fmtSymSimprocAndThen___closed__3, &l_Lean_Fmt_fmtSymSimprocAndThen___closed__3_once, _init_l_Lean_Fmt_fmtSymSimprocAndThen___closed__3);
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimprocAndThen___closed__1));
v___x_14_ = 0;
v___x_15_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_15_, 0, v___x_13_);
lean_ctor_set(v___x_15_, 1, v___x_12_);
lean_ctor_set_uint8(v___x_15_, sizeof(void*)*2, v___x_14_);
lean_ctor_set_uint8(v___x_15_, sizeof(void*)*2 + 1, v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSymSimprocAndThen(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&l_Lean_Fmt_fmtSymSimprocAndThen___closed__4, &l_Lean_Fmt_fmtSymSimprocAndThen___closed__4_once, _init_l_Lean_Fmt_fmtSymSimprocAndThen___closed__4);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1(){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_35_ = l_Lean_Fmt_infixFmtAttribute;
v___x_36_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__5));
v___x_37_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___closed__8));
v___x_38_ = l_Lean_Fmt_fmtSymSimprocAndThen;
v___x_39_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_35_, v___x_36_, v___x_37_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1___boxed(lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1();
return v_res_41_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSymSimprocOrElse___closed__2(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Lean_Fmt_fmtSymSimprocAndThen___closed__3, &l_Lean_Fmt_fmtSymSimprocAndThen___closed__3_once, _init_l_Lean_Fmt_fmtSymSimprocAndThen___closed__3);
v___x_48_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimprocOrElse___closed__1));
v___x_49_ = 0;
v___x_50_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_50_, 0, v___x_48_);
lean_ctor_set(v___x_50_, 1, v___x_47_);
lean_ctor_set_uint8(v___x_50_, sizeof(void*)*2, v___x_49_);
lean_ctor_set_uint8(v___x_50_, sizeof(void*)*2 + 1, v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSymSimprocOrElse(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_obj_once(&l_Lean_Fmt_fmtSymSimprocOrElse___closed__2, &l_Lean_Fmt_fmtSymSimprocOrElse___closed__2_once, _init_l_Lean_Fmt_fmtSymSimprocOrElse___closed__2);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_65_ = l_Lean_Fmt_infixFmtAttribute;
v___x_66_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__1));
v___x_67_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___closed__3));
v___x_68_ = l_Lean_Fmt_fmtSymSimprocOrElse;
v___x_69_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_65_, v___x_66_, v___x_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1___boxed(lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1();
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpRewriteSet(lean_object* v_x_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1));
lean_inc(v_x_82_);
v___x_86_ = l_Lean_Syntax_isOfKind(v_x_82_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_x_82_);
v___x_87_ = l_Lean_Fmt_Error_partialFormatter;
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_a_84_);
return v___x_88_;
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_97_; lean_object* v___y_98_; lean_object* v___y_99_; 
v___x_89_ = lean_unsigned_to_nat(1u);
v___x_90_ = l_Lean_Syntax_getArg(v_x_82_, v___x_89_);
v___x_91_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpRewriteSet___closed__3));
lean_inc(v___x_90_);
v___x_92_ = l_Lean_Syntax_isOfKind(v___x_90_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v___x_90_);
lean_dec(v_x_82_);
v___x_124_ = l_Lean_Fmt_Error_partialFormatter;
v___x_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_a_84_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v_rewriteTk_127_; lean_object* v_withTk_x3f_129_; lean_object* v_discharger_x3f_130_; lean_object* v___y_131_; lean_object* v___y_132_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v_rewriteTk_127_ = l_Lean_Syntax_getArg(v_x_82_, v___x_126_);
v___x_153_ = lean_unsigned_to_nat(2u);
v___x_154_ = l_Lean_Syntax_getArg(v_x_82_, v___x_153_);
lean_dec(v_x_82_);
v___x_155_ = l_Lean_Syntax_isNone(v___x_154_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
lean_inc(v___x_154_);
v___x_156_ = l_Lean_Syntax_matchesNull(v___x_154_, v___x_153_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v___x_154_);
lean_dec(v_rewriteTk_127_);
lean_dec(v___x_90_);
v___x_157_ = l_Lean_Fmt_Error_partialFormatter;
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v_a_84_);
return v___x_158_;
}
else
{
lean_object* v_withTk_x3f_159_; lean_object* v_discharger_x3f_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_withTk_x3f_159_ = l_Lean_Syntax_getArg(v___x_154_, v___x_126_);
v_discharger_x3f_160_ = l_Lean_Syntax_getArg(v___x_154_, v___x_89_);
lean_dec(v___x_154_);
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v_withTk_x3f_159_);
v___x_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_162_, 0, v_discharger_x3f_160_);
v_withTk_x3f_129_ = v___x_161_;
v_discharger_x3f_130_ = v___x_162_;
v___y_131_ = v_a_83_;
v___y_132_ = v_a_84_;
goto v___jp_128_;
}
}
else
{
lean_object* v___x_163_; 
lean_dec(v___x_154_);
v___x_163_ = lean_box(0);
v_withTk_x3f_129_ = v___x_163_;
v_discharger_x3f_130_ = v___x_163_;
v___y_131_ = v_a_83_;
v___y_132_ = v_a_84_;
goto v___jp_128_;
}
v___jp_128_:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Fmt_fmt(v_rewriteTk_127_, v___y_131_, v___y_132_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v_a_135_; lean_object* v___x_136_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
v_a_135_ = lean_ctor_get(v___x_133_, 1);
lean_inc(v_a_135_);
lean_dec_ref_known(v___x_133_, 2);
v___x_136_ = l_Lean_Fmt_fmt(v___x_90_, v___y_131_, v_a_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v_a_138_; lean_object* v___x_139_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
v_a_138_ = lean_ctor_get(v___x_136_, 1);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_136_, 2);
v___x_139_ = l_Lean_Fmt_fmt_x3f(v_withTk_x3f_129_, v___y_131_, v_a_138_);
if (lean_obj_tag(v___x_139_) == 0)
{
if (lean_obj_tag(v_discharger_x3f_130_) == 0)
{
lean_object* v_a_140_; lean_object* v_a_141_; lean_object* v___x_142_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
v_a_141_ = lean_ctor_get(v___x_139_, 1);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_139_, 2);
v___x_142_ = lean_box(0);
v___y_94_ = v_a_137_;
v___y_95_ = v___y_131_;
v___y_96_ = v_a_134_;
v___y_97_ = v_a_140_;
v___y_98_ = v_a_141_;
v___y_99_ = v___x_142_;
goto v___jp_93_;
}
else
{
lean_object* v_a_143_; lean_object* v_a_144_; lean_object* v_val_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_a_143_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_143_);
v_a_144_ = lean_ctor_get(v___x_139_, 1);
lean_inc(v_a_144_);
lean_dec_ref_known(v___x_139_, 2);
v_val_145_ = lean_ctor_get(v_discharger_x3f_130_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v_discharger_x3f_130_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v_discharger_x3f_130_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_val_145_);
lean_dec(v_discharger_x3f_130_);
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
v___y_94_ = v_a_137_;
v___y_95_ = v___y_131_;
v___y_96_ = v_a_134_;
v___y_97_ = v_a_143_;
v___y_98_ = v_a_144_;
v___y_99_ = v___x_150_;
goto v___jp_93_;
}
}
}
}
else
{
lean_dec(v_a_137_);
lean_dec(v_a_134_);
lean_dec(v_discharger_x3f_130_);
return v___x_139_;
}
}
else
{
lean_dec(v_a_134_);
lean_dec(v_discharger_x3f_130_);
lean_dec(v_withTk_x3f_129_);
return v___x_136_;
}
}
else
{
lean_dec(v_discharger_x3f_130_);
lean_dec(v_withTk_x3f_129_);
lean_dec(v___x_90_);
return v___x_133_;
}
}
}
v___jp_93_:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Fmt_fmt_x3f(v___y_99_, v___y_95_, v___y_98_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_123_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_a_102_ = lean_ctor_get(v___x_100_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_123_ == 0)
{
v___x_104_ = v___x_100_;
v_isShared_105_ = v_isSharedCheck_123_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_123_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_106_ = lean_unsigned_to_nat(2u);
v___x_107_ = lean_mk_empty_array_with_capacity(v___x_106_);
lean_inc_ref(v___x_107_);
v___x_108_ = lean_array_push(v___x_107_, v___y_96_);
v___x_109_ = lean_array_push(v___x_108_, v___y_94_);
v___x_110_ = 0;
v___x_111_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_111_, 0, v___x_92_);
lean_ctor_set_uint8(v___x_111_, 1, v___x_110_);
lean_ctor_set_uint8(v___x_111_, 2, v___x_110_);
lean_ctor_set_uint8(v___x_111_, 3, v___x_110_);
v___x_112_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_109_, v___x_111_);
v___x_113_ = 0;
v___x_114_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v___y_97_, v_a_101_, v___x_113_);
v___x_115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_115_, 0, v___x_112_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_92_);
v___x_116_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*1, v___x_92_);
v___x_117_ = lean_array_push(v___x_107_, v___x_115_);
v___x_118_ = lean_array_push(v___x_117_, v___x_116_);
v___x_119_ = l_Lean_Fmt_Layouts_blocks(v___x_118_, v___x_92_);
lean_dec_ref(v___x_118_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_119_);
v___x_121_ = v___x_104_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_a_102_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
else
{
lean_dec_ref(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec_ref(v___y_94_);
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpRewriteSet___boxed(lean_object* v_x_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Fmt_fmtSymSimpRewriteSet(v_x_164_, v_a_165_, v_a_166_);
lean_dec_ref(v_a_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1(){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_174_ = l_Lean_Fmt_fmtAttribute;
v___x_175_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpRewriteSet___closed__1));
v___x_176_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___closed__1));
v___x_177_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymSimpRewriteSet___boxed), 3, 0);
v___x_178_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_174_, v___x_175_, v___x_176_, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1___boxed(lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1();
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpRewriteInline(lean_object* v_x_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1));
lean_inc(v_x_189_);
v___x_193_ = l_Lean_Syntax_isOfKind(v_x_189_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v_x_189_);
v___x_194_ = l_Lean_Fmt_Error_partialFormatter;
v___x_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_a_191_);
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v_rewriteTk_197_; lean_object* v___x_198_; lean_object* v_lbTk_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v_rbTk_236_; lean_object* v_withTk_x3f_238_; lean_object* v_discharger_x3f_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v_rewriteTk_197_ = l_Lean_Syntax_getArg(v_x_189_, v___x_196_);
v___x_198_ = lean_unsigned_to_nat(1u);
v_lbTk_199_ = l_Lean_Syntax_getArg(v_x_189_, v___x_198_);
v___x_200_ = lean_unsigned_to_nat(2u);
v___x_201_ = l_Lean_Syntax_getArg(v_x_189_, v___x_200_);
v___x_202_ = lean_unsigned_to_nat(3u);
v_rbTk_236_ = l_Lean_Syntax_getArg(v_x_189_, v___x_202_);
v___x_277_ = lean_unsigned_to_nat(4u);
v___x_278_ = l_Lean_Syntax_getArg(v_x_189_, v___x_277_);
lean_dec(v_x_189_);
v___x_279_ = l_Lean_Syntax_isNone(v___x_278_);
if (v___x_279_ == 0)
{
uint8_t v___x_280_; 
lean_inc(v___x_278_);
v___x_280_ = l_Lean_Syntax_matchesNull(v___x_278_, v___x_200_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v___x_278_);
lean_dec(v_rbTk_236_);
lean_dec(v___x_201_);
lean_dec(v_lbTk_199_);
lean_dec(v_rewriteTk_197_);
v___x_281_ = l_Lean_Fmt_Error_partialFormatter;
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v_a_191_);
return v___x_282_;
}
else
{
lean_object* v_withTk_x3f_283_; lean_object* v_discharger_x3f_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_withTk_x3f_283_ = l_Lean_Syntax_getArg(v___x_278_, v___x_196_);
v_discharger_x3f_284_ = l_Lean_Syntax_getArg(v___x_278_, v___x_198_);
lean_dec(v___x_278_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v_withTk_x3f_283_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v_discharger_x3f_284_);
v_withTk_x3f_238_ = v___x_285_;
v_discharger_x3f_239_ = v___x_286_;
v___y_240_ = v_a_190_;
v___y_241_ = v_a_191_;
goto v___jp_237_;
}
}
else
{
lean_object* v___x_287_; 
lean_dec(v___x_278_);
v___x_287_ = lean_box(0);
v_withTk_x3f_238_ = v___x_287_;
v_discharger_x3f_239_ = v___x_287_;
v___y_240_ = v_a_190_;
v___y_241_ = v_a_191_;
goto v___jp_237_;
}
v___jp_203_:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Fmt_fmt_x3f(v___y_212_, v___y_205_, v___y_208_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_235_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_a_215_ = lean_ctor_get(v___x_213_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_235_ == 0)
{
v___x_217_ = v___x_213_;
v_isShared_218_ = v_isSharedCheck_235_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_235_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_219_ = 0;
v___x_220_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_220_, 0, v___x_219_);
lean_ctor_set_uint8(v___x_220_, 1, v___x_193_);
lean_inc_ref(v___y_211_);
v___x_221_ = l_Lean_Fmt_Layouts_collection(v___y_211_, v___y_210_, v___y_206_, v___y_209_, v___x_220_);
lean_dec_ref(v___y_206_);
v___x_222_ = 0;
v___x_223_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v___y_204_, v_a_214_, v___x_222_);
v___x_224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_224_, 0, v___y_207_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1, v___x_193_);
v___x_225_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_221_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_193_);
v___x_226_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_226_, 0, v___x_223_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v___x_193_);
v___x_227_ = lean_mk_empty_array_with_capacity(v___x_202_);
v___x_228_ = lean_array_push(v___x_227_, v___x_224_);
v___x_229_ = lean_array_push(v___x_228_, v___x_225_);
v___x_230_ = lean_array_push(v___x_229_, v___x_226_);
v___x_231_ = l_Lean_Fmt_Layouts_blocks(v___x_230_, v___x_193_);
lean_dec_ref(v___x_230_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_231_);
v___x_233_ = v___x_217_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_a_215_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
else
{
lean_dec_ref(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec_ref(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec_ref(v___y_204_);
return v___x_213_;
}
}
v___jp_237_:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Fmt_fmt(v_rewriteTk_197_, v___y_240_, v___y_241_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v_a_244_; lean_object* v___x_245_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
v_a_244_ = lean_ctor_get(v___x_242_, 1);
lean_inc(v_a_244_);
lean_dec_ref_known(v___x_242_, 2);
v___x_245_ = l_Lean_Fmt_fmt(v_lbTk_199_, v___y_240_, v_a_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v_a_247_; lean_object* v_thms_248_; lean_object* v___x_249_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
v_a_247_ = lean_ctor_get(v___x_245_, 1);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_245_, 2);
v_thms_248_ = l_Lean_Syntax_getArgs(v___x_201_);
lean_dec(v___x_201_);
v___x_249_ = l_Lean_Fmt_fmtTSepArray___redArg(v_thms_248_, v___y_240_, v_a_247_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
v_a_251_ = lean_ctor_get(v___x_249_, 1);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_249_, 2);
v___x_252_ = l_Lean_Fmt_fmt(v_rbTk_236_, v___y_240_, v_a_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_a_254_; lean_object* v___x_255_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
v_a_254_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_252_, 2);
v___x_255_ = l_Lean_Fmt_fmt_x3f(v_withTk_x3f_238_, v___y_240_, v_a_254_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v_a_257_; lean_object* v___x_258_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
v_a_257_ = lean_ctor_get(v___x_255_, 1);
lean_inc(v_a_257_);
lean_dec_ref_known(v___x_255_, 2);
v___x_258_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpRewriteInline___closed__2));
if (lean_obj_tag(v_discharger_x3f_239_) == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_box(0);
v___y_204_ = v_a_256_;
v___y_205_ = v___y_240_;
v___y_206_ = v_a_250_;
v___y_207_ = v_a_243_;
v___y_208_ = v_a_257_;
v___y_209_ = v_a_253_;
v___y_210_ = v_a_246_;
v___y_211_ = v___x_258_;
v___y_212_ = v___x_259_;
goto v___jp_203_;
}
else
{
lean_object* v_val_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
v_val_260_ = lean_ctor_get(v_discharger_x3f_239_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v_discharger_x3f_239_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v_discharger_x3f_239_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_val_260_);
lean_dec(v_discharger_x3f_239_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_val_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
v___y_204_ = v_a_256_;
v___y_205_ = v___y_240_;
v___y_206_ = v_a_250_;
v___y_207_ = v_a_243_;
v___y_208_ = v_a_257_;
v___y_209_ = v_a_253_;
v___y_210_ = v_a_246_;
v___y_211_ = v___x_258_;
v___y_212_ = v___x_265_;
goto v___jp_203_;
}
}
}
}
else
{
lean_dec(v_a_253_);
lean_dec(v_a_250_);
lean_dec(v_a_246_);
lean_dec(v_a_243_);
lean_dec(v_discharger_x3f_239_);
return v___x_255_;
}
}
else
{
lean_dec(v_a_250_);
lean_dec(v_a_246_);
lean_dec(v_a_243_);
lean_dec(v_discharger_x3f_239_);
lean_dec(v_withTk_x3f_238_);
return v___x_252_;
}
}
else
{
lean_object* v_a_268_; lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_246_);
lean_dec(v_a_243_);
lean_dec(v_discharger_x3f_239_);
lean_dec(v_withTk_x3f_238_);
lean_dec(v_rbTk_236_);
v_a_268_ = lean_ctor_get(v___x_249_, 0);
v_a_269_ = lean_ctor_get(v___x_249_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_249_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_inc(v_a_268_);
lean_dec(v___x_249_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_268_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_dec(v_a_243_);
lean_dec(v_discharger_x3f_239_);
lean_dec(v_withTk_x3f_238_);
lean_dec(v_rbTk_236_);
lean_dec(v___x_201_);
return v___x_245_;
}
}
else
{
lean_dec(v_discharger_x3f_239_);
lean_dec(v_withTk_x3f_238_);
lean_dec(v_rbTk_236_);
lean_dec(v___x_201_);
lean_dec(v_lbTk_199_);
return v___x_242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpRewriteInline___boxed(lean_object* v_x_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Fmt_fmtSymSimpRewriteInline(v_x_288_, v_a_289_, v_a_290_);
lean_dec_ref(v_a_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1(){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_298_ = l_Lean_Fmt_fmtAttribute;
v___x_299_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpRewriteInline___closed__1));
v___x_300_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___closed__1));
v___x_301_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymSimpRewriteInline___boxed), 3, 0);
v___x_302_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_298_, v___x_299_, v___x_300_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1___boxed(lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1();
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpArith(lean_object* v_x_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; 
v___x_315_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpArith___closed__1));
lean_inc(v_x_312_);
v___x_316_ = l_Lean_Syntax_isOfKind(v_x_312_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_x_312_);
v___x_342_ = l_Lean_Fmt_Error_partialFormatter;
v___x_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_a_314_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v_arithTk_345_; lean_object* v_withTk_x3f_347_; lean_object* v_discharger_x3f_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v_arithTk_345_ = l_Lean_Syntax_getArg(v_x_312_, v___x_344_);
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = l_Lean_Syntax_getArg(v_x_312_, v___x_368_);
lean_dec(v_x_312_);
v___x_370_ = l_Lean_Syntax_isNone(v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_369_);
v___x_372_ = l_Lean_Syntax_matchesNull(v___x_369_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v___x_369_);
lean_dec(v_arithTk_345_);
v___x_373_ = l_Lean_Fmt_Error_partialFormatter;
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v_a_314_);
return v___x_374_;
}
else
{
lean_object* v_withTk_x3f_375_; lean_object* v_discharger_x3f_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_withTk_x3f_375_ = l_Lean_Syntax_getArg(v___x_369_, v___x_344_);
v_discharger_x3f_376_ = l_Lean_Syntax_getArg(v___x_369_, v___x_368_);
lean_dec(v___x_369_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v_withTk_x3f_375_);
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v_discharger_x3f_376_);
v_withTk_x3f_347_ = v___x_377_;
v_discharger_x3f_348_ = v___x_378_;
v___y_349_ = v_a_313_;
v___y_350_ = v_a_314_;
goto v___jp_346_;
}
}
else
{
lean_object* v___x_379_; 
lean_dec(v___x_369_);
v___x_379_ = lean_box(0);
v_withTk_x3f_347_ = v___x_379_;
v_discharger_x3f_348_ = v___x_379_;
v___y_349_ = v_a_313_;
v___y_350_ = v_a_314_;
goto v___jp_346_;
}
v___jp_346_:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Fmt_fmt(v_arithTk_345_, v___y_349_, v___y_350_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v_a_353_; lean_object* v___x_354_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
v_a_353_ = lean_ctor_get(v___x_351_, 1);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_351_, 2);
v___x_354_ = l_Lean_Fmt_fmt_x3f(v_withTk_x3f_347_, v___y_349_, v_a_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
if (lean_obj_tag(v_discharger_x3f_348_) == 0)
{
lean_object* v_a_355_; lean_object* v_a_356_; lean_object* v___x_357_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
v_a_356_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_354_, 2);
v___x_357_ = lean_box(0);
v___y_318_ = v_a_352_;
v___y_319_ = v_a_356_;
v___y_320_ = v___y_349_;
v___y_321_ = v_a_355_;
v___y_322_ = v___x_357_;
goto v___jp_317_;
}
else
{
lean_object* v_a_358_; lean_object* v_a_359_; lean_object* v_val_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_358_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_358_);
v_a_359_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_354_, 2);
v_val_360_ = lean_ctor_get(v_discharger_x3f_348_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_discharger_x3f_348_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v_discharger_x3f_348_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_val_360_);
lean_dec(v_discharger_x3f_348_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_val_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
v___y_318_ = v_a_352_;
v___y_319_ = v_a_359_;
v___y_320_ = v___y_349_;
v___y_321_ = v_a_358_;
v___y_322_ = v___x_365_;
goto v___jp_317_;
}
}
}
}
else
{
lean_dec(v_a_352_);
lean_dec(v_discharger_x3f_348_);
return v___x_354_;
}
}
else
{
lean_dec(v_discharger_x3f_348_);
lean_dec(v_withTk_x3f_347_);
return v___x_351_;
}
}
}
v___jp_317_:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Fmt_fmt_x3f(v___y_322_, v___y_320_, v___y_319_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_341_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_a_325_ = lean_ctor_get(v___x_323_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_341_ == 0)
{
v___x_327_ = v___x_323_;
v_isShared_328_ = v_isSharedCheck_341_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_341_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_329_ = 0;
v___x_330_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v___y_321_, v_a_324_, v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_331_, 0, v___y_318_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*1, v___x_316_);
v___x_332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*1, v___x_316_);
v___x_333_ = lean_unsigned_to_nat(2u);
v___x_334_ = lean_mk_empty_array_with_capacity(v___x_333_);
v___x_335_ = lean_array_push(v___x_334_, v___x_331_);
v___x_336_ = lean_array_push(v___x_335_, v___x_332_);
v___x_337_ = l_Lean_Fmt_Layouts_blocks(v___x_336_, v___x_316_);
lean_dec_ref(v___x_336_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_337_);
v___x_339_ = v___x_327_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_a_325_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
else
{
lean_dec_ref(v___y_321_);
lean_dec_ref(v___y_318_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpArith___boxed(lean_object* v_x_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Fmt_fmtSymSimpArith(v_x_380_, v_a_381_, v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1(){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_390_ = l_Lean_Fmt_fmtAttribute;
v___x_391_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpArith___closed__1));
v___x_392_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___closed__1));
v___x_393_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymSimpArith___boxed), 3, 0);
v___x_394_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_390_, v___x_391_, v___x_392_, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1___boxed(lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1();
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimprocParen(lean_object* v_x_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimprocParen___closed__1));
lean_inc(v_x_404_);
v___x_408_ = l_Lean_Syntax_isOfKind(v_x_404_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v_x_404_);
v___x_409_ = l_Lean_Fmt_Error_partialFormatter;
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_a_406_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v_lbTk_412_; lean_object* v___x_413_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v_lbTk_412_ = l_Lean_Syntax_getArg(v_x_404_, v___x_411_);
v___x_413_ = l_Lean_Fmt_fmt(v_lbTk_412_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v_a_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
v_a_415_ = lean_ctor_get(v___x_413_, 1);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_413_, 2);
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = l_Lean_Syntax_getArg(v_x_404_, v___x_416_);
v___x_418_ = l_Lean_Fmt_fmt(v___x_417_, v_a_405_, v_a_415_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v_rbTk_422_; lean_object* v___x_423_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
v_a_420_ = lean_ctor_get(v___x_418_, 1);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_418_, 2);
v___x_421_ = lean_unsigned_to_nat(2u);
v_rbTk_422_ = l_Lean_Syntax_getArg(v_x_404_, v___x_421_);
lean_dec(v_x_404_);
v___x_423_ = l_Lean_Fmt_fmt(v_rbTk_422_, v_a_405_, v_a_420_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_433_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_a_425_ = lean_ctor_get(v___x_423_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_433_ == 0)
{
v___x_427_ = v___x_423_;
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = l_Lean_Fmt_Layouts_parens(v_a_414_, v_a_419_, v_a_424_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_a_425_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
else
{
lean_dec(v_a_419_);
lean_dec(v_a_414_);
return v___x_423_;
}
}
else
{
lean_dec(v_a_414_);
lean_dec(v_x_404_);
return v___x_418_;
}
}
else
{
lean_dec(v_x_404_);
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimprocParen___boxed(lean_object* v_x_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Fmt_fmtSymSimprocParen(v_x_434_, v_a_435_, v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1(){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_444_ = l_Lean_Fmt_fmtAttribute;
v___x_445_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimprocParen___closed__1));
v___x_446_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___closed__1));
v___x_447_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymSimprocParen___boxed), 3, 0);
v___x_448_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_444_, v___x_445_, v___x_446_, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1___boxed(lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1();
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDischargerParen(lean_object* v_x_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Fmt_fmtSymDischargerParen___closed__1));
lean_inc(v_x_458_);
v___x_462_ = l_Lean_Syntax_isOfKind(v_x_458_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v_x_458_);
v___x_463_ = l_Lean_Fmt_Error_partialFormatter;
v___x_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v_a_460_);
return v___x_464_;
}
else
{
lean_object* v___x_465_; lean_object* v_lbTk_466_; lean_object* v___x_467_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v_lbTk_466_ = l_Lean_Syntax_getArg(v_x_458_, v___x_465_);
v___x_467_ = l_Lean_Fmt_fmt(v_lbTk_466_, v_a_459_, v_a_460_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v_a_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
v_a_469_ = lean_ctor_get(v___x_467_, 1);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_467_, 2);
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = l_Lean_Syntax_getArg(v_x_458_, v___x_470_);
v___x_472_ = l_Lean_Fmt_fmt(v___x_471_, v_a_459_, v_a_469_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v_a_474_; lean_object* v___x_475_; lean_object* v_rbTk_476_; lean_object* v___x_477_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
v_a_474_ = lean_ctor_get(v___x_472_, 1);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_472_, 2);
v___x_475_ = lean_unsigned_to_nat(2u);
v_rbTk_476_ = l_Lean_Syntax_getArg(v_x_458_, v___x_475_);
lean_dec(v_x_458_);
v___x_477_ = l_Lean_Fmt_fmt(v_rbTk_476_, v_a_459_, v_a_474_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_a_479_ = lean_ctor_get(v___x_477_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_487_ == 0)
{
v___x_481_ = v___x_477_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = l_Lean_Fmt_Layouts_parens(v_a_468_, v_a_473_, v_a_478_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_a_479_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
else
{
lean_dec(v_a_473_);
lean_dec(v_a_468_);
return v___x_477_;
}
}
else
{
lean_dec(v_a_468_);
lean_dec(v_x_458_);
return v___x_472_;
}
}
else
{
lean_dec(v_x_458_);
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDischargerParen___boxed(lean_object* v_x_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Fmt_fmtSymDischargerParen(v_x_488_, v_a_489_, v_a_490_);
lean_dec_ref(v_a_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1(){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_498_ = l_Lean_Fmt_fmtAttribute;
v___x_499_ = ((lean_object*)(l_Lean_Fmt_fmtSymDischargerParen___closed__1));
v___x_500_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___closed__1));
v___x_501_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymDischargerParen___boxed), 3, 0);
v___x_502_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_498_, v___x_499_, v___x_500_, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1___boxed(lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1();
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldPre(lean_object* v_x_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldPre___closed__2));
lean_inc(v_x_512_);
v___x_516_ = l_Lean_Syntax_isOfKind(v_x_512_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v_x_512_);
v___x_517_ = l_Lean_Fmt_Error_partialFormatter;
v___x_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v_a_514_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v_preTk_520_; lean_object* v___x_521_; 
v___x_519_ = lean_unsigned_to_nat(0u);
v_preTk_520_ = l_Lean_Syntax_getArg(v_x_512_, v___x_519_);
v___x_521_ = l_Lean_Fmt_fmt(v_preTk_520_, v_a_513_, v_a_514_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v_a_523_; lean_object* v___x_524_; lean_object* v_colonEqTk_525_; lean_object* v___x_526_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
v_a_523_ = lean_ctor_get(v___x_521_, 1);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_521_, 2);
v___x_524_ = lean_unsigned_to_nat(1u);
v_colonEqTk_525_ = l_Lean_Syntax_getArg(v_x_512_, v___x_524_);
v___x_526_ = l_Lean_Fmt_fmt(v_colonEqTk_525_, v_a_513_, v_a_523_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v_a_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
v_a_528_ = lean_ctor_get(v___x_526_, 1);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_526_, 2);
v___x_529_ = lean_unsigned_to_nat(2u);
v___x_530_ = l_Lean_Syntax_getArg(v_x_512_, v___x_529_);
lean_dec(v_x_512_);
v___x_531_ = l_Lean_Fmt_fmt(v___x_530_, v_a_513_, v_a_528_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_542_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_a_533_ = lean_ctor_get(v___x_531_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_542_ == 0)
{
v___x_535_ = v___x_531_;
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_537_ = 0;
v___x_538_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_522_, v_a_527_, v_a_532_, v___x_537_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_538_);
v___x_540_ = v___x_535_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_a_533_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
lean_dec(v_a_527_);
lean_dec(v_a_522_);
return v___x_531_;
}
}
else
{
lean_dec(v_a_522_);
lean_dec(v_x_512_);
return v___x_526_;
}
}
else
{
lean_dec(v_x_512_);
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldPre___boxed(lean_object* v_x_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Fmt_fmtSymSimpFieldPre(v_x_543_, v_a_544_, v_a_545_);
lean_dec_ref(v_a_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1(){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_553_ = l_Lean_Fmt_fmtAttribute;
v___x_554_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldPre___closed__2));
v___x_555_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___closed__1));
v___x_556_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymSimpFieldPre___boxed), 3, 0);
v___x_557_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_553_, v___x_554_, v___x_555_, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1___boxed(lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1();
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldPost(lean_object* v_x_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldPost___closed__1));
lean_inc(v_x_566_);
v___x_570_ = l_Lean_Syntax_isOfKind(v_x_566_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v_x_566_);
v___x_571_ = l_Lean_Fmt_Error_partialFormatter;
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_a_568_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v_postTk_574_; lean_object* v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v_postTk_574_ = l_Lean_Syntax_getArg(v_x_566_, v___x_573_);
v___x_575_ = l_Lean_Fmt_fmt(v_postTk_574_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v_a_577_; lean_object* v___x_578_; lean_object* v_colonEqTk_579_; lean_object* v___x_580_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
v_a_577_ = lean_ctor_get(v___x_575_, 1);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_575_, 2);
v___x_578_ = lean_unsigned_to_nat(1u);
v_colonEqTk_579_ = l_Lean_Syntax_getArg(v_x_566_, v___x_578_);
v___x_580_ = l_Lean_Fmt_fmt(v_colonEqTk_579_, v_a_567_, v_a_577_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
v_a_582_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_580_, 2);
v___x_583_ = lean_unsigned_to_nat(2u);
v___x_584_ = l_Lean_Syntax_getArg(v_x_566_, v___x_583_);
lean_dec(v_x_566_);
v___x_585_ = l_Lean_Fmt_fmt(v___x_584_, v_a_567_, v_a_582_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_596_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_a_587_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_596_ == 0)
{
v___x_589_ = v___x_585_;
v_isShared_590_ = v_isSharedCheck_596_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_596_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_591_ = 0;
v___x_592_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_576_, v_a_581_, v_a_586_, v___x_591_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_592_);
v___x_594_ = v___x_589_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_a_587_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
lean_dec(v_a_581_);
lean_dec(v_a_576_);
return v___x_585_;
}
}
else
{
lean_dec(v_a_576_);
lean_dec(v_x_566_);
return v___x_580_;
}
}
else
{
lean_dec(v_x_566_);
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldPost___boxed(lean_object* v_x_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Fmt_fmtSymSimpFieldPost(v_x_597_, v_a_598_, v_a_599_);
lean_dec_ref(v_a_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1(){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_607_ = l_Lean_Fmt_fmtAttribute;
v___x_608_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldPost___closed__1));
v___x_609_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___closed__1));
v___x_610_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymSimpFieldPost___boxed), 3, 0);
v___x_611_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_607_, v___x_608_, v___x_609_, v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1___boxed(lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1();
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldDischarger(lean_object* v_x_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__1));
lean_inc(v_x_620_);
v___x_624_ = l_Lean_Syntax_isOfKind(v_x_620_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v_x_620_);
v___x_625_ = l_Lean_Fmt_Error_partialFormatter;
v___x_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v_a_622_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v_dischargerTk_628_; lean_object* v___x_629_; 
v___x_627_ = lean_unsigned_to_nat(0u);
v_dischargerTk_628_ = l_Lean_Syntax_getArg(v_x_620_, v___x_627_);
v___x_629_ = l_Lean_Fmt_fmt(v_dischargerTk_628_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v_a_631_; lean_object* v___x_632_; lean_object* v_colonEqTk_633_; lean_object* v___x_634_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
v_a_631_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_629_, 2);
v___x_632_ = lean_unsigned_to_nat(1u);
v_colonEqTk_633_ = l_Lean_Syntax_getArg(v_x_620_, v___x_632_);
v___x_634_ = l_Lean_Fmt_fmt(v_colonEqTk_633_, v_a_621_, v_a_631_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v_a_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
v_a_636_ = lean_ctor_get(v___x_634_, 1);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_634_, 2);
v___x_637_ = lean_unsigned_to_nat(2u);
v___x_638_ = l_Lean_Syntax_getArg(v_x_620_, v___x_637_);
lean_dec(v_x_620_);
v___x_639_ = l_Lean_Fmt_fmt(v___x_638_, v_a_621_, v_a_636_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_650_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_a_641_ = lean_ctor_get(v___x_639_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_650_ == 0)
{
v___x_643_ = v___x_639_;
v_isShared_644_ = v_isSharedCheck_650_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_650_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_645_ = 0;
v___x_646_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_630_, v_a_635_, v_a_640_, v___x_645_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_646_);
v___x_648_ = v___x_643_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_a_641_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
else
{
lean_dec(v_a_635_);
lean_dec(v_a_630_);
return v___x_639_;
}
}
else
{
lean_dec(v_a_630_);
lean_dec(v_x_620_);
return v___x_634_;
}
}
else
{
lean_dec(v_x_620_);
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldDischarger___boxed(lean_object* v_x_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Fmt_fmtSymSimpFieldDischarger(v_x_651_, v_a_652_, v_a_653_);
lean_dec_ref(v_a_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1(){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_661_ = l_Lean_Fmt_fmtAttribute;
v___x_662_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldDischarger___closed__1));
v___x_663_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___closed__1));
v___x_664_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymSimpFieldDischarger___boxed), 3, 0);
v___x_665_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_661_, v___x_662_, v___x_663_, v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1___boxed(lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1();
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxSteps(lean_object* v_x_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__1));
lean_inc(v_x_677_);
v___x_681_ = l_Lean_Syntax_isOfKind(v_x_677_, v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v_x_677_);
v___x_682_ = l_Lean_Fmt_Error_partialFormatter;
v___x_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v_a_679_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_684_ = lean_unsigned_to_nat(2u);
v___x_685_ = l_Lean_Syntax_getArg(v_x_677_, v___x_684_);
v___x_686_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__3));
lean_inc(v___x_685_);
v___x_687_ = l_Lean_Syntax_isOfKind(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec(v___x_685_);
lean_dec(v_x_677_);
v___x_688_ = l_Lean_Fmt_Error_partialFormatter;
v___x_689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v_a_679_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v_maxStepsTk_691_; lean_object* v___x_692_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v_maxStepsTk_691_ = l_Lean_Syntax_getArg(v_x_677_, v___x_690_);
v___x_692_ = l_Lean_Fmt_fmt(v_maxStepsTk_691_, v_a_678_, v_a_679_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v_colonEqTk_696_; lean_object* v___x_697_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
v_a_694_ = lean_ctor_get(v___x_692_, 1);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_692_, 2);
v___x_695_ = lean_unsigned_to_nat(1u);
v_colonEqTk_696_ = l_Lean_Syntax_getArg(v_x_677_, v___x_695_);
lean_dec(v_x_677_);
v___x_697_ = l_Lean_Fmt_fmt(v_colonEqTk_696_, v_a_678_, v_a_694_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v_a_699_; lean_object* v___x_700_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
v_a_699_ = lean_ctor_get(v___x_697_, 1);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_697_, 2);
v___x_700_ = l_Lean_Fmt_fmt(v___x_685_, v_a_678_, v_a_699_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_711_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_a_702_ = lean_ctor_get(v___x_700_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_711_ == 0)
{
v___x_704_ = v___x_700_;
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_711_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_706_ = 0;
v___x_707_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_693_, v_a_698_, v_a_701_, v___x_706_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_707_);
v___x_709_ = v___x_704_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_a_702_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_dec(v_a_698_);
lean_dec(v_a_693_);
return v___x_700_;
}
}
else
{
lean_dec(v_a_693_);
lean_dec(v___x_685_);
return v___x_697_;
}
}
else
{
lean_dec(v___x_685_);
lean_dec(v_x_677_);
return v___x_692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxSteps___boxed(lean_object* v_x_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Fmt_fmtSymSimpFieldMaxSteps(v_x_712_, v_a_713_, v_a_714_);
lean_dec_ref(v_a_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1(){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_722_ = l_Lean_Fmt_fmtAttribute;
v___x_723_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__1));
v___x_724_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___closed__1));
v___x_725_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymSimpFieldMaxSteps___boxed), 3, 0);
v___x_726_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_722_, v___x_723_, v___x_724_, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1___boxed(lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1();
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth(lean_object* v_x_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__1));
lean_inc(v_x_735_);
v___x_739_ = l_Lean_Syntax_isOfKind(v_x_735_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v_x_735_);
v___x_740_ = l_Lean_Fmt_Error_partialFormatter;
v___x_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_a_737_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_742_ = lean_unsigned_to_nat(2u);
v___x_743_ = l_Lean_Syntax_getArg(v_x_735_, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldMaxSteps___closed__3));
lean_inc(v___x_743_);
v___x_745_ = l_Lean_Syntax_isOfKind(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v___x_743_);
lean_dec(v_x_735_);
v___x_746_ = l_Lean_Fmt_Error_partialFormatter;
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v_a_737_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; lean_object* v_maxDischargeDepthTk_749_; lean_object* v___x_750_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v_maxDischargeDepthTk_749_ = l_Lean_Syntax_getArg(v_x_735_, v___x_748_);
v___x_750_ = l_Lean_Fmt_fmt(v_maxDischargeDepthTk_749_, v_a_736_, v_a_737_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v_a_752_; lean_object* v___x_753_; lean_object* v_colonEqTk_754_; lean_object* v___x_755_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
v_a_752_ = lean_ctor_get(v___x_750_, 1);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_750_, 2);
v___x_753_ = lean_unsigned_to_nat(1u);
v_colonEqTk_754_ = l_Lean_Syntax_getArg(v_x_735_, v___x_753_);
lean_dec(v_x_735_);
v___x_755_ = l_Lean_Fmt_fmt(v_colonEqTk_754_, v_a_736_, v_a_752_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v_a_757_; lean_object* v___x_758_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
v_a_757_ = lean_ctor_get(v___x_755_, 1);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_755_, 2);
v___x_758_ = l_Lean_Fmt_fmt(v___x_743_, v_a_736_, v_a_757_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_769_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_a_760_ = lean_ctor_get(v___x_758_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_769_ == 0)
{
v___x_762_ = v___x_758_;
v_isShared_763_ = v_isSharedCheck_769_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_769_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_764_ = 0;
v___x_765_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_751_, v_a_756_, v_a_759_, v___x_764_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_765_);
v___x_767_ = v___x_762_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_a_760_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
else
{
lean_dec(v_a_756_);
lean_dec(v_a_751_);
return v___x_758_;
}
}
else
{
lean_dec(v_a_751_);
lean_dec(v___x_743_);
return v___x_755_;
}
}
else
{
lean_dec(v___x_743_);
lean_dec(v_x_735_);
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___boxed(lean_object* v_x_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth(v_x_770_, v_a_771_, v_a_772_);
lean_dec_ref(v_a_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1(){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_780_ = l_Lean_Fmt_fmtAttribute;
v___x_781_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___closed__1));
v___x_782_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___closed__1));
v___x_783_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___boxed), 3, 0);
v___x_784_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_780_, v___x_781_, v___x_782_, v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1___boxed(lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1();
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymSimp(lean_object* v_x_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSymSimp___closed__1));
lean_inc(v_x_793_);
v___x_797_ = l_Lean_Syntax_isOfKind(v_x_793_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec(v_x_793_);
v___x_798_ = l_Lean_Fmt_Error_partialFormatter;
v___x_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v_a_795_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = l_Lean_Syntax_getArg(v_x_793_, v___x_800_);
v___x_802_ = ((lean_object*)(l_Lean_Fmt_fmtSymSimpRewriteSet___closed__3));
lean_inc(v___x_801_);
v___x_803_ = l_Lean_Syntax_isOfKind(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec(v___x_801_);
lean_dec(v_x_793_);
v___x_804_ = l_Lean_Fmt_Error_partialFormatter;
v___x_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v_a_795_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v_registerSymSimpTk_807_; lean_object* v___x_808_; 
v___x_806_ = lean_unsigned_to_nat(0u);
v_registerSymSimpTk_807_ = l_Lean_Syntax_getArg(v_x_793_, v___x_806_);
v___x_808_ = l_Lean_Fmt_fmt(v_registerSymSimpTk_807_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v_a_810_; lean_object* v___x_811_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
v_a_810_ = lean_ctor_get(v___x_808_, 1);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_808_, 2);
v___x_811_ = l_Lean_Fmt_fmt(v___x_801_, v_a_794_, v_a_810_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v_whereTk_815_; lean_object* v___x_816_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
v_a_813_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_811_, 2);
v___x_814_ = lean_unsigned_to_nat(2u);
v_whereTk_815_ = l_Lean_Syntax_getArg(v_x_793_, v___x_814_);
v___x_816_ = l_Lean_Fmt_fmt(v_whereTk_815_, v_a_794_, v_a_813_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v_a_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_fields_821_; lean_object* v___x_822_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
v_a_818_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_816_, 2);
v___x_819_ = lean_unsigned_to_nat(3u);
v___x_820_ = l_Lean_Syntax_getArg(v_x_793_, v___x_819_);
lean_dec(v_x_793_);
v_fields_821_ = l_Lean_Syntax_getArgs(v___x_820_);
lean_dec(v___x_820_);
v___x_822_ = l_Lean_Fmt_fmtArray___redArg(v_fields_821_, v_a_794_, v_a_818_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_840_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_a_824_ = lean_ctor_get(v___x_822_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_840_ == 0)
{
v___x_826_ = v___x_822_;
v_isShared_827_ = v_isSharedCheck_840_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_840_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_828_ = lean_mk_empty_array_with_capacity(v___x_814_);
v___x_829_ = lean_array_push(v___x_828_, v_a_809_);
v___x_830_ = lean_array_push(v___x_829_, v_a_812_);
v___x_831_ = 0;
v___x_832_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_832_, 0, v___x_803_);
lean_ctor_set_uint8(v___x_832_, 1, v___x_831_);
lean_ctor_set_uint8(v___x_832_, 2, v___x_831_);
lean_ctor_set_uint8(v___x_832_, 3, v___x_831_);
v___x_833_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_830_, v___x_832_);
v___x_834_ = l_Lean_Fmt_Layouts_lines(v_a_823_);
lean_dec(v_a_823_);
v___x_835_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_835_, 0, v___x_831_);
lean_ctor_set_uint8(v___x_835_, 1, v___x_803_);
v___x_836_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_833_, v_a_817_, v___x_834_, v___x_835_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_836_);
v___x_838_ = v___x_826_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_a_824_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
else
{
lean_object* v_a_841_; lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_a_817_);
lean_dec(v_a_812_);
lean_dec(v_a_809_);
v_a_841_ = lean_ctor_get(v___x_822_, 0);
v_a_842_ = lean_ctor_get(v___x_822_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_822_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_inc(v_a_841_);
lean_dec(v___x_822_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_841_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_dec(v_a_812_);
lean_dec(v_a_809_);
lean_dec(v_x_793_);
return v___x_816_;
}
}
else
{
lean_dec(v_a_809_);
lean_dec(v_x_793_);
return v___x_811_;
}
}
else
{
lean_dec(v___x_801_);
lean_dec(v_x_793_);
return v___x_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymSimp___boxed(lean_object* v_x_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Fmt_fmtRegisterSymSimp(v_x_850_, v_a_851_, v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1(){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_860_ = l_Lean_Fmt_fmtAttribute;
v___x_861_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSymSimp___closed__1));
v___x_862_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___closed__1));
v___x_863_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRegisterSymSimp___boxed), 3, 0);
v___x_864_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_860_, v___x_861_, v___x_862_, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1___boxed(lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1();
return v_res_866_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL(uint8_t builtin) {
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
l_Lean_Fmt_fmtSymSimprocAndThen = _init_l_Lean_Fmt_fmtSymSimprocAndThen();
lean_mark_persistent(l_Lean_Fmt_fmtSymSimprocAndThen);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymSimprocAndThen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtSymSimprocOrElse = _init_l_Lean_Fmt_fmtSymSimprocOrElse();
lean_mark_persistent(l_Lean_Fmt_fmtSymSimprocOrElse);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymSimprocOrElse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteSet___regBuiltin_Lean_Fmt_fmtSymSimpRewriteSet__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymSimpRewriteInline__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpArith___regBuiltin_Lean_Fmt_fmtSymSimpArith__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimprocParen___regBuiltin_Lean_Fmt_fmtSymSimprocParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymDischargerParen___regBuiltin_Lean_Fmt_fmtSymDischargerParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymSimpFieldPre__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymSimpFieldPost__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldDischarger___regBuiltin_Lean_Fmt_fmtSymSimpFieldDischarger__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxSteps__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth___regBuiltin_Lean_Fmt_fmtSymSimpFieldMaxDischargeDepth__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL_0__Lean_Fmt_fmtRegisterSymSimp___regBuiltin_Lean_Fmt_fmtRegisterSymSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Sym_Simp_SimprocDSL(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Sym_Simp_SimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Sym_Simp_SimprocDSL(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_Simp_SimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Sym_Simp_SimprocDSL(builtin);
}
#ifdef __cplusplus
}
#endif
