// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Sym.DSimp.DSimprocDSL
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Sym.DSimp.DSimprocDSL import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Fmt_infixFmtAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_collection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimprocAndThen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1)),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtSymDSimprocAndThen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimprocAndThen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimprocAndThen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimprocAndThen___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtSymDSimprocAndThen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimprocAndThen___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtSymDSimprocAndThen___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSymDSimprocAndThen___closed__2;
static lean_once_cell_t l_Lean_Fmt_fmtSymDSimprocAndThen___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSymDSimprocAndThen___closed__3;
static lean_once_cell_t l_Lean_Fmt_fmtSymDSimprocAndThen___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSymDSimprocAndThen___closed__4;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimprocAndThen;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "DSimp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andThen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 19, 66, 194, 48, 33, 24, 203)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(98, 127, 28, 43, 8, 10, 206, 209)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__6 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__6_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtSymDSimprocAndThen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__7 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(12, 127, 234, 178, 186, 203, 17, 45)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__8 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimprocOrElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtSymDSimprocOrElse___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimprocOrElse___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimprocOrElse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimprocOrElse___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtSymDSimprocOrElse___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimprocOrElse___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtSymDSimprocOrElse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtSymDSimprocOrElse___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimprocOrElse;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orElse"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 19, 66, 194, 48, 33, 24, 203)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 38, 83, 219, 45, 100, 192, 172)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtSymDSimprocOrElse"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 223, 37, 255, 101, 133, 161, 56)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "rewriteInline"};
static const lean_object* l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 19, 66, 194, 48, 33, 24, 203)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 166, 225, 126, 93, 224, 221, 229)}};
static const lean_object* l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpRewriteInline(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpRewriteInline___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtSymDSimpRewriteInline"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 71, 178, 69, 12, 114, 177, 201)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymDSimprocParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "dsimprocParen"};
static const lean_object* l_Lean_Fmt_fmtSymDSimprocParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimprocParen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimprocParen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimprocParen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimprocParen___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimprocParen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimprocParen___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimprocParen___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimprocParen___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 19, 66, 194, 48, 33, 24, 203)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimprocParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimprocParen___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtSymDSimprocParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 214, 0, 33, 63, 91, 131, 171)}};
static const lean_object* l_Lean_Fmt_fmtSymDSimprocParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimprocParen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimprocParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimprocParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtSymDSimprocParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 122, 191, 71, 70, 100, 27, 171)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymDSimpFieldPre___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtSymDSimpFieldPre___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPre___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSymDSimpFieldPre___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "symDSimpFieldPre"};
static const lean_object* l_Lean_Fmt_fmtSymDSimpFieldPre___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPre___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldPre___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldPre___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPre___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldPre___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPre___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPre___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldPre___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPre___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPre___closed__1_value),LEAN_SCALAR_PTR_LITERAL(208, 114, 136, 35, 117, 78, 189, 21)}};
static const lean_object* l_Lean_Fmt_fmtSymDSimpFieldPre___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPre___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldPre(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldPre___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtSymDSimpFieldPre"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 2, 148, 55, 153, 251, 28, 11)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymDSimpFieldPost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "symDSimpFieldPost"};
static const lean_object* l_Lean_Fmt_fmtSymDSimpFieldPost___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPost___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldPost___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldPost___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPost___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldPost___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPost___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPre___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldPost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPost___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 214, 53, 10, 203, 191, 152, 98)}};
static const lean_object* l_Lean_Fmt_fmtSymDSimpFieldPost___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPost___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldPost(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldPost___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtSymDSimpFieldPost"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 32, 14, 166, 207, 243, 180, 55)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "symDSimpFieldMaxSteps"};
static const lean_object* l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPre___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 215, 8, 180, 95, 67, 128, 125)}};
static const lean_object* l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldMaxSteps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtSymDSimpFieldMaxSteps"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 71, 236, 147, 41, 41, 97, 20)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRegisterSymDSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "registerSymDSimp"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymDSimp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymDSimp___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymDSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymDSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymDSimp___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymDSimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymDSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSymDSimpFieldPre___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymDSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSymDSimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterSymDSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 34, 78, 198, 88, 88, 53, 165)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymDSimp___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymDSimp___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSymDSimp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtRegisterSymDSimp___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymDSimp___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSymDSimp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterSymDSimp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSymDSimp___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSymDSimp___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymDSimp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymDSimp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtRegisterSymDSimp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 165, 23, 30, 62, 252, 93, 117)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Fmt_fmtSymDSimprocAndThen___closed__2(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_box(0);
v___x_7_ = lean_unsigned_to_nat(16u);
v___x_8_ = lean_mk_array(v___x_7_, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSymDSimprocAndThen___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&l_Lean_Fmt_fmtSymDSimprocAndThen___closed__2, &l_Lean_Fmt_fmtSymDSimprocAndThen___closed__2_once, _init_l_Lean_Fmt_fmtSymDSimprocAndThen___closed__2);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSymDSimprocAndThen___closed__4(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_obj_once(&l_Lean_Fmt_fmtSymDSimprocAndThen___closed__3, &l_Lean_Fmt_fmtSymDSimprocAndThen___closed__3_once, _init_l_Lean_Fmt_fmtSymDSimprocAndThen___closed__3);
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimprocAndThen___closed__1));
v___x_14_ = 0;
v___x_15_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_15_, 0, v___x_13_);
lean_ctor_set(v___x_15_, 1, v___x_12_);
lean_ctor_set_uint8(v___x_15_, sizeof(void*)*2, v___x_14_);
lean_ctor_set_uint8(v___x_15_, sizeof(void*)*2 + 1, v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSymDSimprocAndThen(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&l_Lean_Fmt_fmtSymDSimprocAndThen___closed__4, &l_Lean_Fmt_fmtSymDSimprocAndThen___closed__4_once, _init_l_Lean_Fmt_fmtSymDSimprocAndThen___closed__4);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1(){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_35_ = l_Lean_Fmt_infixFmtAttribute;
v___x_36_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__5));
v___x_37_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___closed__8));
v___x_38_ = l_Lean_Fmt_fmtSymDSimprocAndThen;
v___x_39_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_35_, v___x_36_, v___x_37_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1___boxed(lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1();
return v_res_41_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSymDSimprocOrElse___closed__2(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Lean_Fmt_fmtSymDSimprocAndThen___closed__3, &l_Lean_Fmt_fmtSymDSimprocAndThen___closed__3_once, _init_l_Lean_Fmt_fmtSymDSimprocAndThen___closed__3);
v___x_48_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimprocOrElse___closed__1));
v___x_49_ = 0;
v___x_50_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_50_, 0, v___x_48_);
lean_ctor_set(v___x_50_, 1, v___x_47_);
lean_ctor_set_uint8(v___x_50_, sizeof(void*)*2, v___x_49_);
lean_ctor_set_uint8(v___x_50_, sizeof(void*)*2 + 1, v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSymDSimprocOrElse(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_obj_once(&l_Lean_Fmt_fmtSymDSimprocOrElse___closed__2, &l_Lean_Fmt_fmtSymDSimprocOrElse___closed__2_once, _init_l_Lean_Fmt_fmtSymDSimprocOrElse___closed__2);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_65_ = l_Lean_Fmt_infixFmtAttribute;
v___x_66_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__1));
v___x_67_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___closed__3));
v___x_68_ = l_Lean_Fmt_fmtSymDSimprocOrElse;
v___x_69_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_65_, v___x_66_, v___x_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1___boxed(lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1();
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpRewriteInline(lean_object* v_x_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1));
lean_inc(v_x_80_);
v___x_84_ = l_Lean_Syntax_isOfKind(v_x_80_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_x_80_);
v___x_85_ = l_Lean_Fmt_Error_partialFormatter;
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v_a_82_);
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v_rewriteTk_88_; lean_object* v___x_89_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v_rewriteTk_88_ = l_Lean_Syntax_getArg(v_x_80_, v___x_87_);
v___x_89_ = l_Lean_Fmt_fmt(v_rewriteTk_88_, v_a_81_, v_a_82_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v_a_91_; lean_object* v___x_92_; lean_object* v_lbTk_93_; lean_object* v___x_94_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_a_90_);
v_a_91_ = lean_ctor_get(v___x_89_, 1);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_89_, 2);
v___x_92_ = lean_unsigned_to_nat(1u);
v_lbTk_93_ = l_Lean_Syntax_getArg(v_x_80_, v___x_92_);
v___x_94_ = l_Lean_Fmt_fmt(v_lbTk_93_, v_a_81_, v_a_91_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v_thms_99_; lean_object* v___x_100_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_95_);
v_a_96_ = lean_ctor_get(v___x_94_, 1);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_94_, 2);
v___x_97_ = lean_unsigned_to_nat(2u);
v___x_98_ = l_Lean_Syntax_getArg(v_x_80_, v___x_97_);
v_thms_99_ = l_Lean_Syntax_getArgs(v___x_98_);
lean_dec(v___x_98_);
v___x_100_ = l_Lean_Fmt_fmtTSepArray___redArg(v_thms_99_, v_a_81_, v_a_96_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v_a_102_; lean_object* v___x_103_; lean_object* v_rbTk_104_; lean_object* v___x_105_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
v_a_102_ = lean_ctor_get(v___x_100_, 1);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_100_, 2);
v___x_103_ = lean_unsigned_to_nat(3u);
v_rbTk_104_ = l_Lean_Syntax_getArg(v_x_80_, v___x_103_);
lean_dec(v_x_80_);
v___x_105_ = l_Lean_Fmt_fmt(v_rbTk_104_, v_a_81_, v_a_102_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_124_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_a_107_ = lean_ctor_get(v___x_105_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_124_ == 0)
{
v___x_109_ = v___x_105_;
v_isShared_110_ = v_isSharedCheck_124_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_124_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_111_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__2));
v___x_112_ = 0;
v___x_113_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_113_, 0, v___x_112_);
lean_ctor_set_uint8(v___x_113_, 1, v___x_84_);
v___x_114_ = l_Lean_Fmt_Layouts_collection(v___x_111_, v_a_95_, v_a_101_, v_a_106_, v___x_113_);
lean_dec(v_a_101_);
v___x_115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_115_, 0, v_a_90_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_84_);
v___x_116_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*1, v___x_84_);
v___x_117_ = lean_mk_empty_array_with_capacity(v___x_97_);
v___x_118_ = lean_array_push(v___x_117_, v___x_115_);
v___x_119_ = lean_array_push(v___x_118_, v___x_116_);
v___x_120_ = l_Lean_Fmt_Layouts_blocks(v___x_119_, v___x_84_);
lean_dec_ref(v___x_119_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_120_);
v___x_122_ = v___x_109_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_a_107_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
else
{
lean_dec(v_a_101_);
lean_dec(v_a_95_);
lean_dec(v_a_90_);
return v___x_105_;
}
}
else
{
lean_object* v_a_125_; lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
lean_dec(v_a_95_);
lean_dec(v_a_90_);
lean_dec(v_x_80_);
v_a_125_ = lean_ctor_get(v___x_100_, 0);
v_a_126_ = lean_ctor_get(v___x_100_, 1);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___x_100_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_inc(v_a_125_);
lean_dec(v___x_100_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_125_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_a_126_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
else
{
lean_dec(v_a_90_);
lean_dec(v_x_80_);
return v___x_94_;
}
}
else
{
lean_dec(v_x_80_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpRewriteInline___boxed(lean_object* v_x_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Fmt_fmtSymDSimpRewriteInline(v_x_134_, v_a_135_, v_a_136_);
lean_dec_ref(v_a_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_144_ = l_Lean_Fmt_fmtAttribute;
v___x_145_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimpRewriteInline___closed__1));
v___x_146_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___closed__1));
v___x_147_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymDSimpRewriteInline___boxed), 3, 0);
v___x_148_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_144_, v___x_145_, v___x_146_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1___boxed(lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1();
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimprocParen(lean_object* v_x_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimprocParen___closed__1));
lean_inc(v_x_158_);
v___x_162_ = l_Lean_Syntax_isOfKind(v_x_158_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_x_158_);
v___x_163_ = l_Lean_Fmt_Error_partialFormatter;
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_a_160_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v_lbTk_166_; lean_object* v___x_167_; 
v___x_165_ = lean_unsigned_to_nat(0u);
v_lbTk_166_ = l_Lean_Syntax_getArg(v_x_158_, v___x_165_);
v___x_167_ = l_Lean_Fmt_fmt(v_lbTk_166_, v_a_159_, v_a_160_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v_a_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
v_a_169_ = lean_ctor_get(v___x_167_, 1);
lean_inc(v_a_169_);
lean_dec_ref_known(v___x_167_, 2);
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = l_Lean_Syntax_getArg(v_x_158_, v___x_170_);
v___x_172_ = l_Lean_Fmt_fmt(v___x_171_, v_a_159_, v_a_169_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v_a_174_; lean_object* v___x_175_; lean_object* v_rbTk_176_; lean_object* v___x_177_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
v_a_174_ = lean_ctor_get(v___x_172_, 1);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_172_, 2);
v___x_175_ = lean_unsigned_to_nat(2u);
v_rbTk_176_ = l_Lean_Syntax_getArg(v_x_158_, v___x_175_);
lean_dec(v_x_158_);
v___x_177_ = l_Lean_Fmt_fmt(v_rbTk_176_, v_a_159_, v_a_174_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_a_179_ = lean_ctor_get(v___x_177_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_187_ == 0)
{
v___x_181_ = v___x_177_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = l_Lean_Fmt_Layouts_parens(v_a_168_, v_a_173_, v_a_178_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_183_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_a_179_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
else
{
lean_dec(v_a_173_);
lean_dec(v_a_168_);
return v___x_177_;
}
}
else
{
lean_dec(v_a_168_);
lean_dec(v_x_158_);
return v___x_172_;
}
}
else
{
lean_dec(v_x_158_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimprocParen___boxed(lean_object* v_x_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Fmt_fmtSymDSimprocParen(v_x_188_, v_a_189_, v_a_190_);
lean_dec_ref(v_a_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1(){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_198_ = l_Lean_Fmt_fmtAttribute;
v___x_199_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimprocParen___closed__1));
v___x_200_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___closed__1));
v___x_201_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymDSimprocParen___boxed), 3, 0);
v___x_202_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_198_, v___x_199_, v___x_200_, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1___boxed(lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1();
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldPre(lean_object* v_x_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimpFieldPre___closed__2));
lean_inc(v_x_212_);
v___x_216_ = l_Lean_Syntax_isOfKind(v_x_212_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec(v_x_212_);
v___x_217_ = l_Lean_Fmt_Error_partialFormatter;
v___x_218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_a_214_);
return v___x_218_;
}
else
{
lean_object* v___x_219_; lean_object* v_preTk_220_; lean_object* v___x_221_; 
v___x_219_ = lean_unsigned_to_nat(0u);
v_preTk_220_ = l_Lean_Syntax_getArg(v_x_212_, v___x_219_);
v___x_221_ = l_Lean_Fmt_fmt(v_preTk_220_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v_a_223_; lean_object* v___x_224_; lean_object* v_colonEqTk_225_; lean_object* v___x_226_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
v_a_223_ = lean_ctor_get(v___x_221_, 1);
lean_inc(v_a_223_);
lean_dec_ref_known(v___x_221_, 2);
v___x_224_ = lean_unsigned_to_nat(1u);
v_colonEqTk_225_ = l_Lean_Syntax_getArg(v_x_212_, v___x_224_);
v___x_226_ = l_Lean_Fmt_fmt(v_colonEqTk_225_, v_a_213_, v_a_223_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v_a_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
v_a_228_ = lean_ctor_get(v___x_226_, 1);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_226_, 2);
v___x_229_ = lean_unsigned_to_nat(2u);
v___x_230_ = l_Lean_Syntax_getArg(v_x_212_, v___x_229_);
lean_dec(v_x_212_);
v___x_231_ = l_Lean_Fmt_fmt(v___x_230_, v_a_213_, v_a_228_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_242_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_a_233_ = lean_ctor_get(v___x_231_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_242_ == 0)
{
v___x_235_ = v___x_231_;
v_isShared_236_ = v_isSharedCheck_242_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_242_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_237_ = 0;
v___x_238_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_222_, v_a_227_, v_a_232_, v___x_237_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_238_);
v___x_240_ = v___x_235_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_a_233_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
else
{
lean_dec(v_a_227_);
lean_dec(v_a_222_);
return v___x_231_;
}
}
else
{
lean_dec(v_a_222_);
lean_dec(v_x_212_);
return v___x_226_;
}
}
else
{
lean_dec(v_x_212_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldPre___boxed(lean_object* v_x_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Fmt_fmtSymDSimpFieldPre(v_x_243_, v_a_244_, v_a_245_);
lean_dec_ref(v_a_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1(){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_253_ = l_Lean_Fmt_fmtAttribute;
v___x_254_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimpFieldPre___closed__2));
v___x_255_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___closed__1));
v___x_256_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymDSimpFieldPre___boxed), 3, 0);
v___x_257_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_253_, v___x_254_, v___x_255_, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1___boxed(lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1();
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldPost(lean_object* v_x_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimpFieldPost___closed__1));
lean_inc(v_x_266_);
v___x_270_ = l_Lean_Syntax_isOfKind(v_x_266_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v_x_266_);
v___x_271_ = l_Lean_Fmt_Error_partialFormatter;
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_a_268_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v_postTk_274_; lean_object* v___x_275_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v_postTk_274_ = l_Lean_Syntax_getArg(v_x_266_, v___x_273_);
v___x_275_ = l_Lean_Fmt_fmt(v_postTk_274_, v_a_267_, v_a_268_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v_a_277_; lean_object* v___x_278_; lean_object* v_colonEqTk_279_; lean_object* v___x_280_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
v_a_277_ = lean_ctor_get(v___x_275_, 1);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_275_, 2);
v___x_278_ = lean_unsigned_to_nat(1u);
v_colonEqTk_279_ = l_Lean_Syntax_getArg(v_x_266_, v___x_278_);
v___x_280_ = l_Lean_Fmt_fmt(v_colonEqTk_279_, v_a_267_, v_a_277_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v_a_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
v_a_282_ = lean_ctor_get(v___x_280_, 1);
lean_inc(v_a_282_);
lean_dec_ref_known(v___x_280_, 2);
v___x_283_ = lean_unsigned_to_nat(2u);
v___x_284_ = l_Lean_Syntax_getArg(v_x_266_, v___x_283_);
lean_dec(v_x_266_);
v___x_285_ = l_Lean_Fmt_fmt(v___x_284_, v_a_267_, v_a_282_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_296_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_a_287_ = lean_ctor_get(v___x_285_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_296_ == 0)
{
v___x_289_ = v___x_285_;
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_291_ = 0;
v___x_292_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_276_, v_a_281_, v_a_286_, v___x_291_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_a_287_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_dec(v_a_281_);
lean_dec(v_a_276_);
return v___x_285_;
}
}
else
{
lean_dec(v_a_276_);
lean_dec(v_x_266_);
return v___x_280_;
}
}
else
{
lean_dec(v_x_266_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldPost___boxed(lean_object* v_x_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Fmt_fmtSymDSimpFieldPost(v_x_297_, v_a_298_, v_a_299_);
lean_dec_ref(v_a_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1(){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_307_ = l_Lean_Fmt_fmtAttribute;
v___x_308_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimpFieldPost___closed__1));
v___x_309_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___closed__1));
v___x_310_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymDSimpFieldPost___boxed), 3, 0);
v___x_311_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_307_, v___x_308_, v___x_309_, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1___boxed(lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1();
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldMaxSteps(lean_object* v_x_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__1));
lean_inc(v_x_323_);
v___x_327_ = l_Lean_Syntax_isOfKind(v_x_323_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_x_323_);
v___x_328_ = l_Lean_Fmt_Error_partialFormatter;
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_a_325_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_330_ = lean_unsigned_to_nat(2u);
v___x_331_ = l_Lean_Syntax_getArg(v_x_323_, v___x_330_);
v___x_332_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__3));
lean_inc(v___x_331_);
v___x_333_ = l_Lean_Syntax_isOfKind(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec(v___x_331_);
lean_dec(v_x_323_);
v___x_334_ = l_Lean_Fmt_Error_partialFormatter;
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_a_325_);
return v___x_335_;
}
else
{
lean_object* v___x_336_; lean_object* v_maxStepsTk_337_; lean_object* v___x_338_; 
v___x_336_ = lean_unsigned_to_nat(0u);
v_maxStepsTk_337_ = l_Lean_Syntax_getArg(v_x_323_, v___x_336_);
v___x_338_ = l_Lean_Fmt_fmt(v_maxStepsTk_337_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v_colonEqTk_342_; lean_object* v___x_343_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
v_a_340_ = lean_ctor_get(v___x_338_, 1);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_338_, 2);
v___x_341_ = lean_unsigned_to_nat(1u);
v_colonEqTk_342_ = l_Lean_Syntax_getArg(v_x_323_, v___x_341_);
lean_dec(v_x_323_);
v___x_343_ = l_Lean_Fmt_fmt(v_colonEqTk_342_, v_a_324_, v_a_340_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v_a_345_; lean_object* v___x_346_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
v_a_345_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_343_, 2);
v___x_346_ = l_Lean_Fmt_fmt(v___x_331_, v_a_324_, v_a_345_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_357_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_a_348_ = lean_ctor_get(v___x_346_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_357_ == 0)
{
v___x_350_ = v___x_346_;
v_isShared_351_ = v_isSharedCheck_357_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_357_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_352_ = 0;
v___x_353_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_339_, v_a_344_, v_a_347_, v___x_352_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_353_);
v___x_355_ = v___x_350_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_a_348_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
else
{
lean_dec(v_a_344_);
lean_dec(v_a_339_);
return v___x_346_;
}
}
else
{
lean_dec(v_a_339_);
lean_dec(v___x_331_);
return v___x_343_;
}
}
else
{
lean_dec(v___x_331_);
lean_dec(v_x_323_);
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___boxed(lean_object* v_x_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Fmt_fmtSymDSimpFieldMaxSteps(v_x_358_, v_a_359_, v_a_360_);
lean_dec_ref(v_a_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1(){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_368_ = l_Lean_Fmt_fmtAttribute;
v___x_369_ = ((lean_object*)(l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___closed__1));
v___x_370_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___closed__1));
v___x_371_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSymDSimpFieldMaxSteps___boxed), 3, 0);
v___x_372_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_368_, v___x_369_, v___x_370_, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1___boxed(lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1();
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymDSimp(lean_object* v_x_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSymDSimp___closed__1));
lean_inc(v_x_384_);
v___x_388_ = l_Lean_Syntax_isOfKind(v_x_384_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_x_384_);
v___x_389_ = l_Lean_Fmt_Error_partialFormatter;
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v_a_386_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_391_ = lean_unsigned_to_nat(1u);
v___x_392_ = l_Lean_Syntax_getArg(v_x_384_, v___x_391_);
v___x_393_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSymDSimp___closed__3));
lean_inc(v___x_392_);
v___x_394_ = l_Lean_Syntax_isOfKind(v___x_392_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec(v___x_392_);
lean_dec(v_x_384_);
v___x_395_ = l_Lean_Fmt_Error_partialFormatter;
v___x_396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_a_386_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; lean_object* v_registerSymDSimpTk_398_; lean_object* v___x_399_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v_registerSymDSimpTk_398_ = l_Lean_Syntax_getArg(v_x_384_, v___x_397_);
v___x_399_ = l_Lean_Fmt_fmt(v_registerSymDSimpTk_398_, v_a_385_, v_a_386_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v_a_401_; lean_object* v___x_402_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
v_a_401_ = lean_ctor_get(v___x_399_, 1);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_399_, 2);
v___x_402_ = l_Lean_Fmt_fmt(v___x_392_, v_a_385_, v_a_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v_a_404_; lean_object* v___x_405_; lean_object* v_whereTk_406_; lean_object* v___x_407_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
v_a_404_ = lean_ctor_get(v___x_402_, 1);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_402_, 2);
v___x_405_ = lean_unsigned_to_nat(2u);
v_whereTk_406_ = l_Lean_Syntax_getArg(v_x_384_, v___x_405_);
v___x_407_ = l_Lean_Fmt_fmt(v_whereTk_406_, v_a_385_, v_a_404_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v_a_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_fields_412_; lean_object* v___x_413_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
v_a_409_ = lean_ctor_get(v___x_407_, 1);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_407_, 2);
v___x_410_ = lean_unsigned_to_nat(3u);
v___x_411_ = l_Lean_Syntax_getArg(v_x_384_, v___x_410_);
lean_dec(v_x_384_);
v_fields_412_ = l_Lean_Syntax_getArgs(v___x_411_);
lean_dec(v___x_411_);
v___x_413_ = l_Lean_Fmt_fmtArray___redArg(v_fields_412_, v_a_385_, v_a_409_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_431_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_a_415_ = lean_ctor_get(v___x_413_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_431_ == 0)
{
v___x_417_ = v___x_413_;
v_isShared_418_ = v_isSharedCheck_431_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_431_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_419_ = lean_mk_empty_array_with_capacity(v___x_405_);
v___x_420_ = lean_array_push(v___x_419_, v_a_400_);
v___x_421_ = lean_array_push(v___x_420_, v_a_403_);
v___x_422_ = 0;
v___x_423_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_423_, 0, v___x_394_);
lean_ctor_set_uint8(v___x_423_, 1, v___x_422_);
lean_ctor_set_uint8(v___x_423_, 2, v___x_422_);
lean_ctor_set_uint8(v___x_423_, 3, v___x_422_);
v___x_424_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_421_, v___x_423_);
v___x_425_ = l_Lean_Fmt_Layouts_lines(v_a_414_);
lean_dec(v_a_414_);
v___x_426_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_426_, 0, v___x_422_);
lean_ctor_set_uint8(v___x_426_, 1, v___x_394_);
v___x_427_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_424_, v_a_408_, v___x_425_, v___x_426_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_427_);
v___x_429_ = v___x_417_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_a_415_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_object* v_a_432_; lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec(v_a_408_);
lean_dec(v_a_403_);
lean_dec(v_a_400_);
v_a_432_ = lean_ctor_get(v___x_413_, 0);
v_a_433_ = lean_ctor_get(v___x_413_, 1);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_413_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_inc(v_a_432_);
lean_dec(v___x_413_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_432_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_dec(v_a_403_);
lean_dec(v_a_400_);
lean_dec(v_x_384_);
return v___x_407_;
}
}
else
{
lean_dec(v_a_400_);
lean_dec(v_x_384_);
return v___x_402_;
}
}
else
{
lean_dec(v___x_392_);
lean_dec(v_x_384_);
return v___x_399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSymDSimp___boxed(lean_object* v_x_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Fmt_fmtRegisterSymDSimp(v_x_441_, v_a_442_, v_a_443_);
lean_dec_ref(v_a_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1(){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_451_ = l_Lean_Fmt_fmtAttribute;
v___x_452_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSymDSimp___closed__1));
v___x_453_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___closed__1));
v___x_454_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRegisterSymDSimp___boxed), 3, 0);
v___x_455_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_451_, v___x_452_, v___x_453_, v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1___boxed(lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1();
return v_res_457_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL(uint8_t builtin) {
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
l_Lean_Fmt_fmtSymDSimprocAndThen = _init_l_Lean_Fmt_fmtSymDSimprocAndThen();
lean_mark_persistent(l_Lean_Fmt_fmtSymDSimprocAndThen);
res = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocAndThen___regBuiltin_Lean_Fmt_fmtSymDSimprocAndThen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtSymDSimprocOrElse = _init_l_Lean_Fmt_fmtSymDSimprocOrElse();
lean_mark_persistent(l_Lean_Fmt_fmtSymDSimprocOrElse);
res = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocOrElse___regBuiltin_Lean_Fmt_fmtSymDSimprocOrElse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpRewriteInline___regBuiltin_Lean_Fmt_fmtSymDSimpRewriteInline__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimprocParen___regBuiltin_Lean_Fmt_fmtSymDSimprocParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPre___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPre__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldPost___regBuiltin_Lean_Fmt_fmtSymDSimpFieldPost__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtSymDSimpFieldMaxSteps___regBuiltin_Lean_Fmt_fmtSymDSimpFieldMaxSteps__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL_0__Lean_Fmt_fmtRegisterSymDSimp___regBuiltin_Lean_Fmt_fmtRegisterSymDSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Sym_DSimp_DSimprocDSL(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Sym_DSimp_DSimprocDSL(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Sym_DSimp_DSimprocDSL(builtin);
}
#ifdef __cplusplus
}
#endif
