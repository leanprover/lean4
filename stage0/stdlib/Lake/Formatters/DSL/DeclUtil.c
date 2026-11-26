// Lean compiler output
// Module: Lake.Formatters.DSL.DeclUtil
// Imports: public import Lean.Fmt.FmtM.Basic public import Lake.DSL.DeclUtil import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_sepLines(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_nl;
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_retainedWhitespace(lean_object*);
lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Fmt_fmtBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Formatters_fmtIdentOrStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_Formatters_fmtIdentOrStr___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value;
static const lean_string_object l_Lake_Formatters_fmtIdentOrStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l_Lake_Formatters_fmtIdentOrStr___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtIdentOrStr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "identOrStr"};
static const lean_object* l_Lake_Formatters_fmtIdentOrStr___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtIdentOrStr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtIdentOrStr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtIdentOrStr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__3_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 188, 128, 7, 103, 245, 245, 49)}};
static const lean_object* l_Lake_Formatters_fmtIdentOrStr___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__3_value;
static const lean_string_object l_Lake_Formatters_fmtIdentOrStr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_Formatters_fmtIdentOrStr___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__4_value;
static const lean_ctor_object l_Lake_Formatters_fmtIdentOrStr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_Formatters_fmtIdentOrStr___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__5_value;
static const lean_string_object l_Lake_Formatters_fmtIdentOrStr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lake_Formatters_fmtIdentOrStr___closed__6 = (const lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__6_value;
static const lean_ctor_object l_Lake_Formatters_fmtIdentOrStr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lake_Formatters_fmtIdentOrStr___closed__7 = (const lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtIdentOrStr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtIdentOrStr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Formatters"};
static const lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__0_value;
static const lean_string_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtIdentOrStr"};
static const lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__1_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__2_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 129, 86, 252, 188, 212, 130, 11)}};
static const lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__2 = (const lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtDeclField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declField"};
static const lean_object* l_Lake_Formatters_fmtDeclField___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtDeclField___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtDeclField___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtDeclField___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtDeclField___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtDeclField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtDeclField___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtDeclField___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 4, 47, 196, 245, 170, 224, 183)}};
static const lean_object* l_Lake_Formatters_fmtDeclField___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtDeclField___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDeclField(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDeclField___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtDeclField"};
static const lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 142, 213, 164, 156, 25, 187, 207)}};
static const lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtBracketedSimpleBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "bracketedSimpleBinder"};
static const lean_object* l_Lake_Formatters_fmtBracketedSimpleBinder___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtBracketedSimpleBinder___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtBracketedSimpleBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtBracketedSimpleBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtBracketedSimpleBinder___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtBracketedSimpleBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtBracketedSimpleBinder___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtBracketedSimpleBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 236, 129, 27, 124, 223, 134, 77)}};
static const lean_object* l_Lake_Formatters_fmtBracketedSimpleBinder___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtBracketedSimpleBinder___closed__1_value;
static const lean_array_object l_Lake_Formatters_fmtBracketedSimpleBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Formatters_fmtBracketedSimpleBinder___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtBracketedSimpleBinder___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtBracketedSimpleBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtBracketedSimpleBinder___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtBracketedSimpleBinder"};
static const lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 114, 254, 64, 137, 147, 186, 159)}};
static const lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtSimpleBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simpleBinder"};
static const lean_object* l_Lake_Formatters_fmtSimpleBinder___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtSimpleBinder___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtSimpleBinder___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtSimpleBinder___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtSimpleBinder___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtSimpleBinder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtSimpleBinder___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtSimpleBinder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 16, 244, 231, 102, 138, 237, 36)}};
static const lean_object* l_Lake_Formatters_fmtSimpleBinder___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtSimpleBinder___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtSimpleBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtSimpleBinder___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtSimpleBinder"};
static const lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 120, 211, 246, 192, 151, 126, 73)}};
static const lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtWithOptConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 253, 70, 178, 90, 186, 195, 40)}};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtWithOptConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValStruct"};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__3_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 214, 189, 204, 150, 4, 239, 13)}};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__3_value;
static const lean_string_object l_Lake_Formatters_fmtWithOptConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declValWhere"};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__4_value;
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__5_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__5_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__4_value),LEAN_SCALAR_PTR_LITERAL(151, 133, 86, 223, 245, 102, 246, 81)}};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__5_value;
static const lean_string_object l_Lake_Formatters_fmtWithOptConfig___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__6 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__6_value;
static const lean_string_object l_Lake_Formatters_fmtWithOptConfig___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__7 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__7_value;
static const lean_string_object l_Lake_Formatters_fmtWithOptConfig___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__8 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__8_value;
static const lean_string_object l_Lake_Formatters_fmtWithOptConfig___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__9 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__9_value;
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__10_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__10_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__8_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__10_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__10 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__10_value;
static const lean_string_object l_Lake_Formatters_fmtWithOptConfig___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__11 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__11_value;
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__12 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__12_value;
static const lean_string_object l_Lake_Formatters_fmtWithOptConfig___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__13 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__13_value;
static const lean_string_object l_Lake_Formatters_fmtWithOptConfig___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__14 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__14_value;
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__15_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__15_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__8_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__15_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__14_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__15 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__15_value;
static const lean_string_object l_Lake_Formatters_fmtWithOptConfig___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structVal"};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__16 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__16_value;
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__17_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtIdentOrStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithOptConfig___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__17_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__16_value),LEAN_SCALAR_PTR_LITERAL(111, 76, 221, 200, 37, 245, 130, 150)}};
static const lean_object* l_Lake_Formatters_fmtWithOptConfig___closed__17 = (const lean_object*)&l_Lake_Formatters_fmtWithOptConfig___closed__17_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithOptConfig(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithOptConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtIdentOrStr(lean_object* v_x_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = ((lean_object*)(l_Lake_Formatters_fmtIdentOrStr___closed__3));
lean_inc(v_x_14_);
v___x_18_ = l_Lean_Syntax_isOfKind(v_x_14_, v___x_17_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_x_14_);
v___x_19_ = l_Lean_Fmt_Error_partialFormatter;
v___x_20_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v_a_16_);
return v___x_20_;
}
else
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_21_ = lean_unsigned_to_nat(0u);
v___x_22_ = l_Lean_Syntax_getArg(v_x_14_, v___x_21_);
lean_dec(v_x_14_);
v___x_23_ = ((lean_object*)(l_Lake_Formatters_fmtIdentOrStr___closed__5));
lean_inc(v___x_22_);
v___x_24_ = l_Lean_Syntax_isOfKind(v___x_22_, v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = ((lean_object*)(l_Lake_Formatters_fmtIdentOrStr___closed__7));
lean_inc(v___x_22_);
v___x_26_ = l_Lean_Syntax_isOfKind(v___x_22_, v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec(v___x_22_);
v___x_27_ = l_Lean_Fmt_Error_partialFormatter;
v___x_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v_a_16_);
return v___x_28_;
}
else
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Fmt_fmt(v___x_22_, v_a_15_, v_a_16_);
return v___x_29_;
}
}
else
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Fmt_fmt(v___x_22_, v_a_15_, v_a_16_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtIdentOrStr___boxed(lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lake_Formatters_fmtIdentOrStr(v_x_31_, v_a_32_, v_a_33_);
lean_dec_ref(v_a_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1(){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_42_ = l_Lean_Fmt_fmtAttribute;
v___x_43_ = ((lean_object*)(l_Lake_Formatters_fmtIdentOrStr___closed__3));
v___x_44_ = ((lean_object*)(l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___closed__2));
v___x_45_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtIdentOrStr___boxed), 3, 0);
v___x_46_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_42_, v___x_43_, v___x_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1___boxed(lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1();
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDeclField(lean_object* v_x_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = ((lean_object*)(l_Lake_Formatters_fmtDeclField___closed__1));
lean_inc(v_x_54_);
v___x_58_ = l_Lean_Syntax_isOfKind(v_x_54_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_x_54_);
v___x_59_ = l_Lean_Fmt_Error_partialFormatter;
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v_a_56_);
return v___x_60_;
}
else
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = l_Lean_Syntax_getArg(v_x_54_, v___x_61_);
v___x_63_ = ((lean_object*)(l_Lake_Formatters_fmtIdentOrStr___closed__5));
lean_inc(v___x_62_);
v___x_64_ = l_Lean_Syntax_isOfKind(v___x_62_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v___x_62_);
lean_dec(v_x_54_);
v___x_65_ = l_Lean_Fmt_Error_partialFormatter;
v___x_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v_a_56_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Fmt_fmt(v___x_62_, v_a_55_, v_a_56_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v_a_69_; lean_object* v___x_70_; lean_object* v_colonEqTk_71_; lean_object* v___x_72_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
v_a_69_ = lean_ctor_get(v___x_67_, 1);
lean_inc(v_a_69_);
lean_dec_ref_known(v___x_67_, 2);
v___x_70_ = lean_unsigned_to_nat(1u);
v_colonEqTk_71_ = l_Lean_Syntax_getArg(v_x_54_, v___x_70_);
v___x_72_ = l_Lean_Fmt_fmt(v_colonEqTk_71_, v_a_55_, v_a_69_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v_a_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
v_a_74_ = lean_ctor_get(v___x_72_, 1);
lean_inc(v_a_74_);
lean_dec_ref_known(v___x_72_, 2);
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = l_Lean_Syntax_getArg(v_x_54_, v___x_75_);
lean_dec(v_x_54_);
v___x_77_ = l_Lean_Fmt_fmt(v___x_76_, v_a_55_, v_a_74_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_88_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_a_79_ = lean_ctor_get(v___x_77_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_88_ == 0)
{
v___x_81_ = v___x_77_;
v_isShared_82_ = v_isSharedCheck_88_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_88_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_83_ = 0;
v___x_84_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_68_, v_a_73_, v_a_78_, v___x_83_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_84_);
v___x_86_ = v___x_81_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_a_79_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
else
{
lean_dec(v_a_73_);
lean_dec(v_a_68_);
return v___x_77_;
}
}
else
{
lean_dec(v_a_68_);
lean_dec(v_x_54_);
return v___x_72_;
}
}
else
{
lean_dec(v_x_54_);
return v___x_67_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDeclField___boxed(lean_object* v_x_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lake_Formatters_fmtDeclField(v_x_89_, v_a_90_, v_a_91_);
lean_dec_ref(v_a_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1(){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_99_ = l_Lean_Fmt_fmtAttribute;
v___x_100_ = ((lean_object*)(l_Lake_Formatters_fmtDeclField___closed__1));
v___x_101_ = ((lean_object*)(l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___closed__1));
v___x_102_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtDeclField___boxed), 3, 0);
v___x_103_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_99_, v___x_100_, v___x_101_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1___boxed(lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1();
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtBracketedSimpleBinder(lean_object* v_x_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lake_Formatters_fmtBracketedSimpleBinder___closed__1));
lean_inc(v_x_113_);
v___x_117_ = l_Lean_Syntax_isOfKind(v_x_113_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v_x_113_);
v___x_118_ = l_Lean_Fmt_Error_partialFormatter;
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_a_115_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = l_Lean_Syntax_getArg(v_x_113_, v___x_120_);
v___x_122_ = ((lean_object*)(l_Lake_Formatters_fmtIdentOrStr___closed__5));
lean_inc(v___x_121_);
v___x_123_ = l_Lean_Syntax_isOfKind(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v___x_121_);
lean_dec(v_x_113_);
v___x_124_ = l_Lean_Fmt_Error_partialFormatter;
v___x_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_a_115_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v_lbTk_127_; lean_object* v_typeAscriptionTk_x3f_129_; lean_object* v_type_x3f_130_; lean_object* v___y_131_; lean_object* v___y_132_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v_lbTk_127_ = l_Lean_Syntax_getArg(v_x_113_, v___x_126_);
v___x_143_ = lean_unsigned_to_nat(2u);
v___x_144_ = l_Lean_Syntax_getArg(v_x_113_, v___x_143_);
v___x_145_ = l_Lean_Syntax_isNone(v___x_144_);
if (v___x_145_ == 0)
{
uint8_t v___x_146_; 
lean_inc(v___x_144_);
v___x_146_ = l_Lean_Syntax_matchesNull(v___x_144_, v___x_143_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v___x_144_);
lean_dec(v_lbTk_127_);
lean_dec(v___x_121_);
lean_dec(v_x_113_);
v___x_147_ = l_Lean_Fmt_Error_partialFormatter;
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_a_115_);
return v___x_148_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_149_; lean_object* v_type_x3f_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_typeAscriptionTk_x3f_149_ = l_Lean_Syntax_getArg(v___x_144_, v___x_126_);
v_type_x3f_150_ = l_Lean_Syntax_getArg(v___x_144_, v___x_120_);
lean_dec(v___x_144_);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v_typeAscriptionTk_x3f_149_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v_type_x3f_150_);
v_typeAscriptionTk_x3f_129_ = v___x_151_;
v_type_x3f_130_ = v___x_152_;
v___y_131_ = v_a_114_;
v___y_132_ = v_a_115_;
goto v___jp_128_;
}
}
else
{
lean_object* v___x_153_; 
lean_dec(v___x_144_);
v___x_153_ = lean_box(0);
v_typeAscriptionTk_x3f_129_ = v___x_153_;
v_type_x3f_130_ = v___x_153_;
v___y_131_ = v_a_114_;
v___y_132_ = v_a_115_;
goto v___jp_128_;
}
v___jp_128_:
{
lean_object* v___x_133_; lean_object* v_rbTk_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_133_ = lean_unsigned_to_nat(3u);
v_rbTk_134_ = l_Lean_Syntax_getArg(v_x_113_, v___x_133_);
lean_dec(v_x_113_);
v___x_135_ = lean_mk_empty_array_with_capacity(v___x_120_);
lean_inc_ref_n(v___x_135_, 2);
v___x_136_ = lean_array_push(v___x_135_, v_lbTk_127_);
v___x_137_ = lean_array_push(v___x_135_, v___x_121_);
v___x_138_ = ((lean_object*)(l_Lake_Formatters_fmtBracketedSimpleBinder___closed__2));
v___x_139_ = lean_box(0);
v___x_140_ = lean_array_push(v___x_135_, v_rbTk_134_);
v___x_141_ = lean_box(1);
v___x_142_ = l_Lean_Fmt_fmtBinder(v___x_136_, v___x_137_, v___x_138_, v_typeAscriptionTk_x3f_129_, v_type_x3f_130_, v___x_139_, v___x_140_, v___x_141_, v___y_131_, v___y_132_);
return v___x_142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtBracketedSimpleBinder___boxed(lean_object* v_x_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lake_Formatters_fmtBracketedSimpleBinder(v_x_154_, v_a_155_, v_a_156_);
lean_dec_ref(v_a_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1(){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = l_Lean_Fmt_fmtAttribute;
v___x_165_ = ((lean_object*)(l_Lake_Formatters_fmtBracketedSimpleBinder___closed__1));
v___x_166_ = ((lean_object*)(l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___closed__1));
v___x_167_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtBracketedSimpleBinder___boxed), 3, 0);
v___x_168_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_164_, v___x_165_, v___x_166_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1___boxed(lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1();
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtSimpleBinder(lean_object* v_x_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lake_Formatters_fmtSimpleBinder___closed__1));
lean_inc(v_x_176_);
v___x_180_ = l_Lean_Syntax_isOfKind(v_x_176_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_x_176_);
v___x_181_ = l_Lean_Fmt_Error_partialFormatter;
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_178_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = l_Lean_Syntax_getArg(v_x_176_, v___x_183_);
lean_dec(v_x_176_);
v___x_185_ = ((lean_object*)(l_Lake_Formatters_fmtIdentOrStr___closed__5));
lean_inc(v___x_184_);
v___x_186_ = l_Lean_Syntax_isOfKind(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lake_Formatters_fmtBracketedSimpleBinder___closed__1));
lean_inc(v___x_184_);
v___x_188_ = l_Lean_Syntax_isOfKind(v___x_184_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v___x_184_);
v___x_189_ = l_Lean_Fmt_Error_partialFormatter;
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_178_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Fmt_fmt(v___x_184_, v_a_177_, v_a_178_);
return v___x_191_;
}
}
else
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Fmt_fmt(v___x_184_, v_a_177_, v_a_178_);
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtSimpleBinder___boxed(lean_object* v_x_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lake_Formatters_fmtSimpleBinder(v_x_193_, v_a_194_, v_a_195_);
lean_dec_ref(v_a_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1(){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_203_ = l_Lean_Fmt_fmtAttribute;
v___x_204_ = ((lean_object*)(l_Lake_Formatters_fmtSimpleBinder___closed__1));
v___x_205_ = ((lean_object*)(l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___closed__1));
v___x_206_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtSimpleBinder___boxed), 3, 0);
v___x_207_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_203_, v___x_204_, v___x_205_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1___boxed(lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1();
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithOptConfig(lean_object* v_signature_249_, lean_object* v_config_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__1));
lean_inc(v_config_250_);
v___x_254_ = l_Lean_Syntax_isOfKind(v_config_250_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_config_250_);
lean_dec_ref(v_signature_249_);
v___x_255_ = l_Lean_Fmt_Error_partialFormatter;
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_a_252_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = l_Lean_Syntax_getArg(v_config_250_, v___x_257_);
lean_dec(v_config_250_);
lean_inc(v___x_258_);
v___x_259_ = l_Lean_Syntax_matchesNull(v___x_258_, v___x_257_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; 
v___x_260_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_258_);
v___x_261_ = l_Lean_Syntax_matchesNull(v___x_258_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v___x_258_);
lean_dec_ref(v_signature_249_);
v___x_295_ = l_Lean_Fmt_Error_partialFormatter;
v___x_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_a_252_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; 
v___x_297_ = l_Lean_Syntax_getArg(v___x_258_, v___x_257_);
lean_dec(v___x_258_);
v___x_298_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__3));
lean_inc(v___x_297_);
v___x_299_ = l_Lean_Syntax_isOfKind(v___x_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__5));
lean_inc(v___x_297_);
v___x_328_ = l_Lean_Syntax_isOfKind(v___x_297_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v___x_297_);
lean_dec_ref(v_signature_249_);
v___x_329_ = l_Lean_Fmt_Error_partialFormatter;
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v_a_252_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_331_ = l_Lean_Syntax_getArg(v___x_297_, v___x_260_);
v___x_332_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__10));
lean_inc(v___x_331_);
v___x_333_ = l_Lean_Syntax_isOfKind(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec(v___x_331_);
lean_dec(v___x_297_);
lean_dec_ref(v_signature_249_);
v___x_334_ = l_Lean_Fmt_Error_partialFormatter;
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_a_252_);
return v___x_335_;
}
else
{
lean_object* v_whereTk_336_; lean_object* v___x_337_; lean_object* v_whereDecls_x3f_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_whereTk_336_ = l_Lean_Syntax_getArg(v___x_297_, v___x_257_);
v___x_337_ = l_Lean_Syntax_getArg(v___x_331_, v___x_257_);
lean_dec(v___x_331_);
v___x_378_ = lean_unsigned_to_nat(2u);
v___x_379_ = l_Lean_Syntax_getArg(v___x_297_, v___x_378_);
lean_dec(v___x_297_);
v___x_380_ = l_Lean_Syntax_isNone(v___x_379_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; 
lean_inc(v___x_379_);
v___x_381_ = l_Lean_Syntax_matchesNull(v___x_379_, v___x_260_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec(v___x_379_);
lean_dec(v___x_337_);
lean_dec(v_whereTk_336_);
lean_dec_ref(v_signature_249_);
v___x_382_ = l_Lean_Fmt_Error_partialFormatter;
v___x_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v_a_252_);
return v___x_383_;
}
else
{
lean_object* v_whereDecls_x3f_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v_whereDecls_x3f_384_ = l_Lean_Syntax_getArg(v___x_379_, v___x_257_);
lean_dec(v___x_379_);
v___x_385_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__15));
lean_inc(v_whereDecls_x3f_384_);
v___x_386_ = l_Lean_Syntax_isOfKind(v_whereDecls_x3f_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v_whereDecls_x3f_384_);
lean_dec(v___x_337_);
lean_dec(v_whereTk_336_);
lean_dec_ref(v_signature_249_);
v___x_387_ = l_Lean_Fmt_Error_partialFormatter;
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_a_252_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v_whereDecls_x3f_384_);
v_whereDecls_x3f_339_ = v___x_389_;
v___y_340_ = v_a_251_;
v___y_341_ = v_a_252_;
goto v___jp_338_;
}
}
}
else
{
lean_object* v___x_390_; 
lean_dec(v___x_379_);
v___x_390_ = lean_box(0);
v_whereDecls_x3f_339_ = v___x_390_;
v___y_340_ = v_a_251_;
v___y_341_ = v_a_252_;
goto v___jp_338_;
}
v___jp_338_:
{
lean_object* v___x_342_; 
lean_inc(v_whereTk_336_);
v___x_342_ = l_Lean_Fmt_fmt(v_whereTk_336_, v___y_340_, v___y_341_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v_a_344_; lean_object* v_fields_345_; lean_object* v___x_346_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
v_a_344_ = lean_ctor_get(v___x_342_, 1);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_342_, 2);
v_fields_345_ = l_Lean_Syntax_getArgs(v___x_337_);
lean_dec(v___x_337_);
lean_inc_ref(v_fields_345_);
v___x_346_ = l_Lean_Fmt_fmtTSepArray___redArg(v_fields_345_, v___y_340_, v_a_344_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
v_a_348_ = lean_ctor_get(v___x_346_, 1);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_346_, 2);
v___x_349_ = lean_mk_empty_array_with_capacity(v___x_260_);
v___x_350_ = lean_array_push(v___x_349_, v_whereTk_336_);
v___x_351_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fields_345_);
lean_dec_ref(v_fields_345_);
v___x_352_ = l_Array_append___redArg(v___x_350_, v___x_351_);
lean_dec_ref(v___x_351_);
v___x_353_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__12));
v___x_354_ = lean_box(2);
v___x_355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_353_);
lean_ctor_set(v___x_355_, 2, v___x_352_);
v___x_356_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___x_355_, v___x_261_, v___y_340_, v_a_348_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v_a_358_; lean_object* v___x_359_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
v_a_358_ = lean_ctor_get(v___x_356_, 1);
lean_inc(v_a_358_);
lean_dec_ref_known(v___x_356_, 2);
v___x_359_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__13));
if (lean_obj_tag(v_whereDecls_x3f_339_) == 0)
{
lean_object* v___x_360_; 
v___x_360_ = lean_box(0);
v___y_301_ = v_a_357_;
v___y_302_ = v___x_359_;
v___y_303_ = v___y_340_;
v___y_304_ = v_a_343_;
v___y_305_ = v_a_347_;
v___y_306_ = v_a_358_;
v___y_307_ = v___x_360_;
goto v___jp_300_;
}
else
{
lean_object* v_val_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_val_361_ = lean_ctor_get(v_whereDecls_x3f_339_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v_whereDecls_x3f_339_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v_whereDecls_x3f_339_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_val_361_);
lean_dec(v_whereDecls_x3f_339_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_val_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
v___y_301_ = v_a_357_;
v___y_302_ = v___x_359_;
v___y_303_ = v___y_340_;
v___y_304_ = v_a_343_;
v___y_305_ = v_a_347_;
v___y_306_ = v_a_358_;
v___y_307_ = v___x_366_;
goto v___jp_300_;
}
}
}
}
else
{
lean_dec(v_a_347_);
lean_dec(v_a_343_);
lean_dec(v_whereDecls_x3f_339_);
lean_dec_ref(v_signature_249_);
return v___x_356_;
}
}
else
{
lean_object* v_a_369_; lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec_ref(v_fields_345_);
lean_dec(v_a_343_);
lean_dec(v_whereDecls_x3f_339_);
lean_dec(v_whereTk_336_);
lean_dec_ref(v_signature_249_);
v_a_369_ = lean_ctor_get(v___x_346_, 0);
v_a_370_ = lean_ctor_get(v___x_346_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_346_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_inc(v_a_369_);
lean_dec(v___x_346_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_369_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_dec(v_whereDecls_x3f_339_);
lean_dec(v___x_337_);
lean_dec(v_whereTk_336_);
lean_dec_ref(v_signature_249_);
return v___x_342_;
}
}
}
}
}
else
{
lean_object* v___x_391_; lean_object* v_whereDecls_x3f_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_391_ = l_Lean_Syntax_getArg(v___x_297_, v___x_257_);
v___x_441_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__17));
lean_inc(v___x_391_);
v___x_442_ = l_Lean_Syntax_isOfKind(v___x_391_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v___x_391_);
lean_dec(v___x_297_);
lean_dec_ref(v_signature_249_);
v___x_443_ = l_Lean_Fmt_Error_partialFormatter;
v___x_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v_a_252_);
return v___x_444_;
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = l_Lean_Syntax_getArg(v___x_297_, v___x_260_);
lean_dec(v___x_297_);
v___x_446_ = l_Lean_Syntax_isNone(v___x_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; 
lean_inc(v___x_445_);
v___x_447_ = l_Lean_Syntax_matchesNull(v___x_445_, v___x_260_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec(v___x_445_);
lean_dec(v___x_391_);
lean_dec_ref(v_signature_249_);
v___x_448_ = l_Lean_Fmt_Error_partialFormatter;
v___x_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v_a_252_);
return v___x_449_;
}
else
{
lean_object* v_whereDecls_x3f_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_whereDecls_x3f_450_ = l_Lean_Syntax_getArg(v___x_445_, v___x_257_);
lean_dec(v___x_445_);
v___x_451_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__15));
lean_inc(v_whereDecls_x3f_450_);
v___x_452_ = l_Lean_Syntax_isOfKind(v_whereDecls_x3f_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec(v_whereDecls_x3f_450_);
lean_dec(v___x_391_);
lean_dec_ref(v_signature_249_);
v___x_453_ = l_Lean_Fmt_Error_partialFormatter;
v___x_454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v_a_252_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v_whereDecls_x3f_450_);
v_whereDecls_x3f_393_ = v___x_455_;
v___y_394_ = v_a_251_;
v___y_395_ = v_a_252_;
goto v___jp_392_;
}
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v___x_445_);
v___x_456_ = lean_box(0);
v_whereDecls_x3f_393_ = v___x_456_;
v___y_394_ = v_a_251_;
v___y_395_ = v_a_252_;
goto v___jp_392_;
}
}
v___jp_392_:
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__17));
lean_inc(v___x_391_);
v___x_397_ = l_Lean_Syntax_isOfKind(v___x_391_, v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v_whereDecls_x3f_393_);
lean_dec(v___x_391_);
lean_dec_ref(v_signature_249_);
v___x_398_ = l_Lean_Fmt_Error_partialFormatter;
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___y_395_);
return v___x_399_;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_400_ = l_Lean_Syntax_getArg(v___x_391_, v___x_260_);
v___x_401_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__10));
lean_inc(v___x_400_);
v___x_402_ = l_Lean_Syntax_isOfKind(v___x_400_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v___x_400_);
lean_dec(v_whereDecls_x3f_393_);
lean_dec(v___x_391_);
lean_dec_ref(v_signature_249_);
v___x_403_ = l_Lean_Fmt_Error_partialFormatter;
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___y_395_);
return v___x_404_;
}
else
{
lean_object* v_lbTk_405_; lean_object* v___x_406_; 
v_lbTk_405_ = l_Lean_Syntax_getArg(v___x_391_, v___x_257_);
v___x_406_ = l_Lean_Fmt_fmt(v_lbTk_405_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v_a_408_; lean_object* v___x_409_; lean_object* v_fields_410_; lean_object* v___x_411_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
v_a_408_ = lean_ctor_get(v___x_406_, 1);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_406_, 2);
v___x_409_ = l_Lean_Syntax_getArg(v___x_400_, v___x_257_);
lean_dec(v___x_400_);
v_fields_410_ = l_Lean_Syntax_getArgs(v___x_409_);
lean_dec(v___x_409_);
v___x_411_ = l_Lean_Fmt_fmtTSepArray___redArg(v_fields_410_, v___y_394_, v_a_408_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v_a_413_; lean_object* v___x_414_; lean_object* v_rbTk_415_; lean_object* v___x_416_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
v_a_413_ = lean_ctor_get(v___x_411_, 1);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_411_, 2);
v___x_414_ = lean_unsigned_to_nat(2u);
v_rbTk_415_ = l_Lean_Syntax_getArg(v___x_391_, v___x_414_);
v___x_416_ = l_Lean_Fmt_fmt(v_rbTk_415_, v___y_394_, v_a_413_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v_a_418_; lean_object* v___x_419_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
v_a_418_ = lean_ctor_get(v___x_416_, 1);
lean_inc(v_a_418_);
lean_dec_ref_known(v___x_416_, 2);
v___x_419_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___x_391_, v___x_261_, v___y_394_, v_a_418_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v_a_421_; lean_object* v___x_422_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
v_a_421_ = lean_ctor_get(v___x_419_, 1);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_419_, 2);
v___x_422_ = ((lean_object*)(l_Lake_Formatters_fmtWithOptConfig___closed__13));
if (lean_obj_tag(v_whereDecls_x3f_393_) == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_box(0);
v___y_263_ = v_a_412_;
v___y_264_ = v_a_421_;
v___y_265_ = v_a_420_;
v___y_266_ = v___y_394_;
v___y_267_ = v_a_417_;
v___y_268_ = v_a_407_;
v___y_269_ = v___x_422_;
v___y_270_ = v___x_423_;
goto v___jp_262_;
}
else
{
lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_val_424_ = lean_ctor_get(v_whereDecls_x3f_393_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_whereDecls_x3f_393_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v_whereDecls_x3f_393_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_dec(v_whereDecls_x3f_393_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_val_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
v___y_263_ = v_a_412_;
v___y_264_ = v_a_421_;
v___y_265_ = v_a_420_;
v___y_266_ = v___y_394_;
v___y_267_ = v_a_417_;
v___y_268_ = v_a_407_;
v___y_269_ = v___x_422_;
v___y_270_ = v___x_429_;
goto v___jp_262_;
}
}
}
}
else
{
lean_dec(v_a_417_);
lean_dec(v_a_412_);
lean_dec(v_a_407_);
lean_dec(v_whereDecls_x3f_393_);
lean_dec_ref(v_signature_249_);
return v___x_419_;
}
}
else
{
lean_dec(v_a_412_);
lean_dec(v_a_407_);
lean_dec(v_whereDecls_x3f_393_);
lean_dec(v___x_391_);
lean_dec_ref(v_signature_249_);
return v___x_416_;
}
}
else
{
lean_object* v_a_432_; lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec(v_a_407_);
lean_dec(v_whereDecls_x3f_393_);
lean_dec(v___x_391_);
lean_dec_ref(v_signature_249_);
v_a_432_ = lean_ctor_get(v___x_411_, 0);
v_a_433_ = lean_ctor_get(v___x_411_, 1);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_411_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_inc(v_a_432_);
lean_dec(v___x_411_);
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
lean_dec(v___x_400_);
lean_dec(v_whereDecls_x3f_393_);
lean_dec(v___x_391_);
lean_dec_ref(v_signature_249_);
return v___x_406_;
}
}
}
}
}
v___jp_300_:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Fmt_fmt_x3f(v___y_307_, v___y_303_, v___y_306_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_326_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_a_310_ = lean_ctor_get(v___x_308_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_326_ == 0)
{
v___x_312_ = v___x_308_;
v_isShared_313_ = v_isSharedCheck_326_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_326_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
lean_inc_ref(v___y_302_);
v___x_314_ = l_Lean_Fmt_Layouts_sepLines(v___y_302_, v___y_305_, v___x_299_);
lean_dec_ref(v___y_305_);
v___x_315_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_314_);
v___x_316_ = l_Lean_Fmt_Layouts_whereDeclaration(v_signature_249_, v___y_304_, v___x_315_);
v___x_317_ = lean_unsigned_to_nat(3u);
v___x_318_ = lean_mk_empty_array_with_capacity(v___x_317_);
v___x_319_ = lean_array_push(v___x_318_, v___x_316_);
v___x_320_ = lean_array_push(v___x_319_, v___y_301_);
v___x_321_ = lean_array_push(v___x_320_, v_a_309_);
v___x_322_ = l_Lean_Fmt_Layouts_retainedWhitespace(v___x_321_);
lean_dec_ref(v___x_321_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_322_);
v___x_324_ = v___x_312_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_a_310_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_dec_ref(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec_ref(v___y_301_);
lean_dec_ref(v_signature_249_);
return v___x_308_;
}
}
}
v___jp_262_:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Fmt_fmt_x3f(v___y_270_, v___y_266_, v___y_264_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_294_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_a_273_ = lean_ctor_get(v___x_271_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_294_ == 0)
{
v___x_275_ = v___x_271_;
v_isShared_276_ = v_isSharedCheck_294_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_294_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
lean_inc_ref(v___y_269_);
v___x_277_ = l_Lean_Fmt_Layouts_sepLines(v___y_269_, v___y_263_, v___x_259_);
lean_dec_ref(v___y_263_);
v___x_278_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_277_);
v___x_279_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_280_ = 1;
v___x_281_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*1, v___x_261_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*1 + 1, v___x_280_);
v___x_282_ = l_Lean_Fmt_Layouts_bracketed(v___y_268_, v___x_278_, v___y_267_, v___x_281_);
v___x_283_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_284_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_signature_249_, v___x_283_, v___x_282_, v___x_259_);
v___x_285_ = lean_unsigned_to_nat(3u);
v___x_286_ = lean_mk_empty_array_with_capacity(v___x_285_);
v___x_287_ = lean_array_push(v___x_286_, v___x_284_);
v___x_288_ = lean_array_push(v___x_287_, v___y_265_);
v___x_289_ = lean_array_push(v___x_288_, v_a_272_);
v___x_290_ = l_Lean_Fmt_Layouts_retainedWhitespace(v___x_289_);
lean_dec_ref(v___x_289_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_290_);
v___x_292_ = v___x_275_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_a_273_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_dec_ref(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec_ref(v___y_265_);
lean_dec_ref(v___y_263_);
lean_dec_ref(v_signature_249_);
return v___x_271_;
}
}
}
else
{
lean_object* v___x_457_; 
lean_dec(v___x_258_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_signature_249_);
lean_ctor_set(v___x_457_, 1, v_a_252_);
return v___x_457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithOptConfig___boxed(lean_object* v_signature_458_, lean_object* v_config_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lake_Formatters_fmtWithOptConfig(v_signature_458_, v_config_459_, v_a_460_, v_a_461_);
lean_dec_ref(v_a_460_);
return v_res_462_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_DeclUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Formatters_DSL_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtIdentOrStr___regBuiltin_Lake_Formatters_fmtIdentOrStr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtDeclField___regBuiltin_Lake_Formatters_fmtDeclField__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtBracketedSimpleBinder___regBuiltin_Lake_Formatters_fmtBracketedSimpleBinder__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_DeclUtil_0__Lake_Formatters_fmtSimpleBinder___regBuiltin_Lake_Formatters_fmtSimpleBinder__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Formatters_DSL_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lake_DSL_DeclUtil(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Formatters_DSL_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Formatters_DSL_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Formatters_DSL_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Formatters_DSL_DeclUtil(builtin);
}
#ifdef __cplusplus
}
#endif
