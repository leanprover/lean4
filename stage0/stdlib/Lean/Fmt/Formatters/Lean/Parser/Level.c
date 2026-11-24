// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Parser.Level
// Imports: public import Lean.Fmt.Formatters.Lean.Parser.Term.Basic public import Lean.Fmt.FmtM.Basic meta import Lean.Parser.Level import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAppLike(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_infixFmtAttribute;
static const lean_string_object l_Lean_Fmt_fmtLevelParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtLevelParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtLevelParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtLevelParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtLevelParen___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Level"};
static const lean_object* l_Lean_Fmt_fmtLevelParen___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtLevelParen___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Fmt_fmtLevelParen___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtLevelParen___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtLevelParen___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtLevelParen___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Fmt_fmtLevelParen___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__3_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 57, 231, 14, 244, 115, 229)}};
static const lean_object* l_Lean_Fmt_fmtLevelParen___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtLevelParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(122, 125, 237, 251, 231, 187, 184, 6)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLevelMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "max"};
static const lean_object* l_Lean_Fmt_fmtLevelMax___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLevelMax___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLevelMax___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtLevelMax___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLevelMax___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtLevelMax___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLevelMax___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Fmt_fmtLevelMax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLevelMax___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLevelMax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 181, 1, 145, 170, 142, 100, 97)}};
static const lean_object* l_Lean_Fmt_fmtLevelMax___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLevelMax___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelMax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelMax___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtLevelMax"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 249, 118, 73, 204, 113, 22, 87)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLevelIMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "imax"};
static const lean_object* l_Lean_Fmt_fmtLevelIMax___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLevelIMax___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtLevelIMax___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtLevelIMax___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLevelIMax___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtLevelIMax___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLevelIMax___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Fmt_fmtLevelIMax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtLevelIMax___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtLevelIMax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 169, 176, 27, 219, 169, 119, 28)}};
static const lean_object* l_Lean_Fmt_fmtLevelIMax___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLevelIMax___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelIMax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelIMax___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtLevelIMax"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 206, 213, 38, 250, 235, 150, 161)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelHole(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelHole___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtAtomic___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(144, 86, 172, 30, 114, 81, 66, 18)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtLevelHole"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 52, 214, 195, 122, 139, 78, 218)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_fmtAddLit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtAddLit___closed__0;
static lean_once_cell_t l_Lean_Fmt_fmtAddLit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtAddLit___closed__1;
static lean_once_cell_t l_Lean_Fmt_fmtAddLit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtAddLit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAddLit;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "addLit"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 243, 225, 2, 30, 243, 80, 174)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtAddLit"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtLevelParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(68, 226, 92, 123, 181, 205, 184, 43)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelParen(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtLevelParen___closed__4));
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
lean_object* v___x_17_; lean_object* v_lbTk_18_; lean_object* v___x_19_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v_lbTk_18_ = l_Lean_Syntax_getArg(v_x_10_, v___x_17_);
v___x_19_ = l_Lean_Fmt_fmt(v_lbTk_18_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v_a_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_a_20_);
v_a_21_ = lean_ctor_get(v___x_19_, 1);
lean_inc(v_a_21_);
lean_dec_ref_known(v___x_19_, 2);
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = l_Lean_Syntax_getArg(v_x_10_, v___x_22_);
v___x_24_ = l_Lean_Fmt_fmt(v___x_23_, v_a_11_, v_a_21_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v_a_26_; lean_object* v___x_27_; lean_object* v_rbTk_28_; lean_object* v___x_29_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_a_25_);
v_a_26_ = lean_ctor_get(v___x_24_, 1);
lean_inc(v_a_26_);
lean_dec_ref_known(v___x_24_, 2);
v___x_27_ = lean_unsigned_to_nat(2u);
v_rbTk_28_ = l_Lean_Syntax_getArg(v_x_10_, v___x_27_);
lean_dec(v_x_10_);
v___x_29_ = l_Lean_Fmt_fmt(v_rbTk_28_, v_a_11_, v_a_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_a_31_ = lean_ctor_get(v___x_29_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_29_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_35_ = l_Lean_Fmt_Layouts_parens(v_a_20_, v_a_25_, v_a_30_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_a_31_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_dec(v_a_25_);
lean_dec(v_a_20_);
return v___x_29_;
}
}
else
{
lean_dec(v_a_20_);
lean_dec(v_x_10_);
return v___x_24_;
}
}
else
{
lean_dec(v_x_10_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelParen___boxed(lean_object* v_x_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Fmt_fmtLevelParen(v_x_40_, v_a_41_, v_a_42_);
lean_dec_ref(v_a_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1(){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_51_ = l_Lean_Fmt_fmtAttribute;
v___x_52_ = ((lean_object*)(l_Lean_Fmt_fmtLevelParen___closed__4));
v___x_53_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___closed__2));
v___x_54_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLevelParen___boxed), 3, 0);
v___x_55_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_51_, v___x_52_, v___x_53_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1___boxed(lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1();
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelMax(lean_object* v_x_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = ((lean_object*)(l_Lean_Fmt_fmtLevelMax___closed__1));
lean_inc(v_x_64_);
v___x_68_ = l_Lean_Syntax_isOfKind(v_x_64_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_x_64_);
v___x_69_ = l_Lean_Fmt_Error_partialFormatter;
v___x_70_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v_a_66_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; lean_object* v_maxTk_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v_levels_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_71_ = lean_unsigned_to_nat(0u);
v_maxTk_72_ = l_Lean_Syntax_getArg(v_x_64_, v___x_71_);
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = l_Lean_Syntax_getArg(v_x_64_, v___x_73_);
lean_dec(v_x_64_);
v_levels_75_ = l_Lean_Syntax_getArgs(v___x_74_);
lean_dec(v___x_74_);
v___x_76_ = lean_mk_empty_array_with_capacity(v___x_73_);
v___x_77_ = lean_array_push(v___x_76_, v_maxTk_72_);
v___x_78_ = l_Array_append___redArg(v___x_77_, v_levels_75_);
lean_dec_ref(v_levels_75_);
v___x_79_ = l_Lean_Fmt_fmtAppLike(v___x_78_, v_a_65_, v_a_66_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelMax___boxed(lean_object* v_x_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Fmt_fmtLevelMax(v_x_80_, v_a_81_, v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1(){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_90_ = l_Lean_Fmt_fmtAttribute;
v___x_91_ = ((lean_object*)(l_Lean_Fmt_fmtLevelMax___closed__1));
v___x_92_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___closed__1));
v___x_93_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLevelMax___boxed), 3, 0);
v___x_94_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_90_, v___x_91_, v___x_92_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1___boxed(lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1();
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelIMax(lean_object* v_x_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = ((lean_object*)(l_Lean_Fmt_fmtLevelIMax___closed__1));
lean_inc(v_x_103_);
v___x_107_ = l_Lean_Syntax_isOfKind(v_x_103_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_x_103_);
v___x_108_ = l_Lean_Fmt_Error_partialFormatter;
v___x_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v_a_105_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v_imaxTk_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_levels_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_110_ = lean_unsigned_to_nat(0u);
v_imaxTk_111_ = l_Lean_Syntax_getArg(v_x_103_, v___x_110_);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = l_Lean_Syntax_getArg(v_x_103_, v___x_112_);
lean_dec(v_x_103_);
v_levels_114_ = l_Lean_Syntax_getArgs(v___x_113_);
lean_dec(v___x_113_);
v___x_115_ = lean_mk_empty_array_with_capacity(v___x_112_);
v___x_116_ = lean_array_push(v___x_115_, v_imaxTk_111_);
v___x_117_ = l_Array_append___redArg(v___x_116_, v_levels_114_);
lean_dec_ref(v_levels_114_);
v___x_118_ = l_Lean_Fmt_fmtAppLike(v___x_117_, v_a_104_, v_a_105_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelIMax___boxed(lean_object* v_x_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Fmt_fmtLevelIMax(v_x_119_, v_a_120_, v_a_121_);
lean_dec_ref(v_a_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1(){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_129_ = l_Lean_Fmt_fmtAttribute;
v___x_130_ = ((lean_object*)(l_Lean_Fmt_fmtLevelIMax___closed__1));
v___x_131_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___closed__1));
v___x_132_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLevelIMax___boxed), 3, 0);
v___x_133_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_129_, v___x_130_, v___x_131_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1___boxed(lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1();
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelHole(lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Fmt_fmtAtomic(v_a_136_, v_a_137_, v_a_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLevelHole___boxed(lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Fmt_fmtLevelHole(v_a_140_, v_a_141_, v_a_142_);
lean_dec_ref(v_a_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1(){
_start:
{
lean_object* v___f_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___f_157_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__0));
v___x_158_ = l_Lean_Fmt_fmtAttribute;
v___x_159_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__2));
v___x_160_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___closed__4));
v___x_161_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_158_, v___x_159_, v___x_160_, v___f_157_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1___boxed(lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1();
return v_res_163_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtAddLit___closed__0(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_box(0);
v___x_165_ = lean_unsigned_to_nat(16u);
v___x_166_ = lean_mk_array(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtAddLit___closed__1(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_obj_once(&l_Lean_Fmt_fmtAddLit___closed__0, &l_Lean_Fmt_fmtAddLit___closed__0_once, _init_l_Lean_Fmt_fmtAddLit___closed__0);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtAddLit___closed__2(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_obj_once(&l_Lean_Fmt_fmtAddLit___closed__1, &l_Lean_Fmt_fmtAddLit___closed__1_once, _init_l_Lean_Fmt_fmtAddLit___closed__1);
v___x_171_ = lean_box(0);
v___x_172_ = 0;
v___x_173_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_170_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*2, v___x_172_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*2 + 1, v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtAddLit(void){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l_Lean_Fmt_fmtAddLit___closed__2, &l_Lean_Fmt_fmtAddLit___closed__2_once, _init_l_Lean_Fmt_fmtAddLit___closed__2);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1(){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_187_ = l_Lean_Fmt_infixFmtAttribute;
v___x_188_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__1));
v___x_189_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___closed__3));
v___x_190_ = l_Lean_Fmt_fmtAddLit;
v___x_191_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_187_, v___x_188_, v___x_189_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1___boxed(lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1();
return v_res_193_;
}
}
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Level(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelParen___regBuiltin_Lean_Fmt_fmtLevelParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelMax___regBuiltin_Lean_Fmt_fmtLevelMax__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelIMax___regBuiltin_Lean_Fmt_fmtLevelIMax__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtLevelHole___regBuiltin_Lean_Fmt_fmtLevelHole__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtAddLit = _init_l_Lean_Fmt_fmtAddLit();
lean_mark_persistent(l_Lean_Fmt_fmtAddLit);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Level_0__Lean_Fmt_fmtAddLit___regBuiltin_Lean_Fmt_fmtAddLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Level(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Level(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Level(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Level(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_Formatters_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Parser_Level(builtin);
}
#ifdef __cplusplus
}
#endif
