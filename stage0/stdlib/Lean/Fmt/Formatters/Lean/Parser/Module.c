// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Parser.Module
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Parser.Module import Lean.Fmt.FmtM.CommonFormatters import Lean.Fmt.FmtM.Comments import Init.Data import Init.While
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object*);
uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_untagged(lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Fmt_fmtWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
lean_object* l_Lean_Fmt_Layouts_spacedLines(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__3_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 219, 158, 40, 50, 143, 61, 44)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__4_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__5 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__5_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__5_value),LEAN_SCALAR_PTR_LITERAL(107, 73, 92, 3, 207, 252, 164, 131)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__6 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__6_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__7 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__7_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__7_value),LEAN_SCALAR_PTR_LITERAL(89, 228, 64, 55, 26, 167, 248, 235)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__8 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__8_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__9 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__9_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__9_value),LEAN_SCALAR_PTR_LITERAL(198, 166, 14, 39, 152, 190, 236, 172)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__10 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__3_value),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtHeader___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__4_value),((lean_object*)&l_Lean_Fmt_fmtHeader___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 65, 253, 3, 148, 106, 71, 75)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtHeader___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Formatters"};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__6_value),((lean_object*)&l_Lean_Fmt_fmtHeader___closed__7_value),LEAN_SCALAR_PTR_LITERAL(3, 21, 16, 61, 99, 129, 86, 30)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__8_value),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 203, 16, 188, 226, 77, 94, 156)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__9_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__9_value),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 132, 219, 9, 157, 187, 212, 239)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__10_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__10_value),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 63, 59, 117, 109, 1, 219, 49)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__11 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__11_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(250, 196, 43, 31, 122, 198, 213, 112)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__12 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__12_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__12_value),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 166, 240, 11, 71, 38, 233, 228)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__13 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__13_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__13_value),((lean_object*)&l_Lean_Fmt_fmtHeader___closed__5_value),LEAN_SCALAR_PTR_LITERAL(213, 203, 178, 185, 22, 114, 70, 199)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__14 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__14_value;
static const lean_string_object l_Lean_Fmt_fmtHeader___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtImport"};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__15 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__15_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__14_value),((lean_object*)&l_Lean_Fmt_fmtHeader___closed__15_value),LEAN_SCALAR_PTR_LITERAL(167, 56, 129, 29, 193, 84, 10, 141)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__16 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__16_value;
static lean_once_cell_t l_Lean_Fmt_fmtHeader___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtHeader___closed__17;
static const lean_string_object l_Lean_Fmt_fmtHeader___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prelude"};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__18 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__18_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__19_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtHeader___closed__18_value),LEAN_SCALAR_PTR_LITERAL(182, 6, 18, 235, 50, 88, 101, 248)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__19 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__19_value;
static const lean_string_object l_Lean_Fmt_fmtHeader___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "moduleTk"};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__20 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__20_value;
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Fmt_fmtHeader___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHeader___closed__21_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtHeader___closed__20_value),LEAN_SCALAR_PTR_LITERAL(198, 239, 28, 252, 21, 233, 71, 221)}};
static const lean_object* l_Lean_Fmt_fmtHeader___closed__21 = (const lean_object*)&l_Lean_Fmt_fmtHeader___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHeader(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHeader___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtHeader"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtHeader___closed__5_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 151, 252, 77, 241, 222, 155, 137)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_headerDocs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_headerDocs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_cmdDocs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_cmdDocs___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Fmt_fmtModule___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtModule___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtModule___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cmds"};
static const lean_object* l_Lean_Fmt_fmtModule___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtModule___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtModule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtModule___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtModule___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 203, 142, 146, 93, 76, 229, 9)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtModule"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtHeader___closed__5_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(55, 165, 26, 100, 128, 25, 23, 60)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport(lean_object* v_x_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__4));
lean_inc(v_x_28_);
v___x_32_ = l_Lean_Syntax_isOfKind(v_x_28_, v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v_x_28_);
v___x_33_ = l_Lean_Fmt_Error_partialFormatter;
v___x_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v_a_30_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v___y_37_; lean_object* v___y_38_; lean_object* v___y_39_; lean_object* v___y_40_; lean_object* v_allTk_x3f_41_; lean_object* v___y_42_; lean_object* v___y_43_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v_metaTk_x3f_88_; lean_object* v___y_89_; lean_object* v___y_90_; lean_object* v_publicTk_x3f_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_125_ = l_Lean_Syntax_getArg(v_x_28_, v___x_35_);
v___x_126_ = l_Lean_Syntax_isNone(v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_125_);
v___x_128_ = l_Lean_Syntax_matchesNull(v___x_125_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v___x_125_);
lean_dec(v_x_28_);
v___x_129_ = l_Lean_Fmt_Error_partialFormatter;
v___x_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v_a_30_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = l_Lean_Syntax_getArg(v___x_125_, v___x_35_);
lean_dec(v___x_125_);
v___x_132_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__10));
lean_inc(v___x_131_);
v___x_133_ = l_Lean_Syntax_isOfKind(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v___x_131_);
lean_dec(v_x_28_);
v___x_134_ = l_Lean_Fmt_Error_partialFormatter;
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_a_30_);
return v___x_135_;
}
else
{
lean_object* v_publicTk_x3f_136_; lean_object* v___x_137_; 
v_publicTk_x3f_136_ = l_Lean_Syntax_getArg(v___x_131_, v___x_35_);
lean_dec(v___x_131_);
v___x_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_137_, 0, v_publicTk_x3f_136_);
v_publicTk_x3f_108_ = v___x_137_;
v___y_109_ = v_a_29_;
v___y_110_ = v_a_30_;
goto v___jp_107_;
}
}
}
else
{
lean_object* v___x_138_; 
lean_dec(v___x_125_);
v___x_138_ = lean_box(0);
v_publicTk_x3f_108_ = v___x_138_;
v___y_109_ = v_a_29_;
v___y_110_ = v_a_30_;
goto v___jp_107_;
}
v___jp_36_:
{
lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_44_ = lean_unsigned_to_nat(5u);
v___x_45_ = l_Lean_Syntax_getArg(v_x_28_, v___x_44_);
v___x_46_ = l_Lean_Syntax_matchesNull(v___x_45_, v___x_35_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_allTk_x3f_41_);
lean_dec(v___y_40_);
lean_dec(v___y_39_);
lean_dec(v___y_38_);
lean_dec(v_x_28_);
v___x_47_ = l_Lean_Fmt_Error_partialFormatter;
v___x_48_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___y_43_);
return v___x_48_;
}
else
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Fmt_fmt_x3f(v___y_40_, v___y_42_, v___y_43_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v_a_51_; lean_object* v___x_52_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
v_a_51_ = lean_ctor_get(v___x_49_, 1);
lean_inc(v_a_51_);
lean_dec_ref_known(v___x_49_, 2);
v___x_52_ = l_Lean_Fmt_fmt_x3f(v___y_39_, v___y_42_, v_a_51_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v_a_54_; lean_object* v___x_55_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
v_a_54_ = lean_ctor_get(v___x_52_, 1);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_52_, 2);
v___x_55_ = l_Lean_Fmt_fmt(v___y_38_, v___y_42_, v_a_54_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_56_; lean_object* v_a_57_; lean_object* v___x_58_; 
v_a_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_a_56_);
v_a_57_ = lean_ctor_get(v___x_55_, 1);
lean_inc(v_a_57_);
lean_dec_ref_known(v___x_55_, 2);
v___x_58_ = l_Lean_Fmt_fmt_x3f(v_allTk_x3f_41_, v___y_42_, v_a_57_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v_a_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_a_59_);
v_a_60_ = lean_ctor_get(v___x_58_, 1);
lean_inc(v_a_60_);
lean_dec_ref_known(v___x_58_, 2);
v___x_61_ = lean_unsigned_to_nat(4u);
v___x_62_ = l_Lean_Syntax_getArg(v_x_28_, v___x_61_);
lean_dec(v_x_28_);
v___x_63_ = l_Lean_Fmt_fmt(v___x_62_, v___y_42_, v_a_60_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_84_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_a_65_ = lean_ctor_get(v___x_63_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_84_ == 0)
{
v___x_67_ = v___x_63_;
v_isShared_68_ = v_isSharedCheck_84_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_84_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_69_ = lean_mk_empty_array_with_capacity(v___x_61_);
v___x_70_ = lean_array_push(v___x_69_, v_a_50_);
v___x_71_ = lean_array_push(v___x_70_, v_a_53_);
v___x_72_ = lean_array_push(v___x_71_, v_a_56_);
v___x_73_ = lean_array_push(v___x_72_, v_a_59_);
v___x_74_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_73_);
lean_dec_ref(v___x_73_);
v___x_75_ = lean_mk_empty_array_with_capacity(v___y_37_);
v___x_76_ = lean_array_push(v___x_75_, v___x_74_);
v___x_77_ = lean_array_push(v___x_76_, v_a_64_);
v___x_78_ = 0;
v___x_79_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_79_, 0, v___x_32_);
lean_ctor_set_uint8(v___x_79_, 1, v___x_78_);
lean_ctor_set_uint8(v___x_79_, 2, v___x_78_);
lean_ctor_set_uint8(v___x_79_, 3, v___x_78_);
v___x_80_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_77_, v___x_79_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_80_);
v___x_82_ = v___x_67_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_a_65_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
else
{
lean_dec(v_a_59_);
lean_dec(v_a_56_);
lean_dec(v_a_53_);
lean_dec(v_a_50_);
return v___x_63_;
}
}
else
{
lean_dec(v_a_56_);
lean_dec(v_a_53_);
lean_dec(v_a_50_);
lean_dec(v_x_28_);
return v___x_58_;
}
}
else
{
lean_dec(v_a_53_);
lean_dec(v_a_50_);
lean_dec(v_allTk_x3f_41_);
lean_dec(v_x_28_);
return v___x_55_;
}
}
else
{
lean_dec(v_a_50_);
lean_dec(v_allTk_x3f_41_);
lean_dec(v___y_38_);
lean_dec(v_x_28_);
return v___x_52_;
}
}
else
{
lean_dec(v_allTk_x3f_41_);
lean_dec(v___y_39_);
lean_dec(v___y_38_);
lean_dec(v_x_28_);
return v___x_49_;
}
}
}
v___jp_85_:
{
lean_object* v___x_91_; lean_object* v_importTk_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_91_ = lean_unsigned_to_nat(2u);
v_importTk_92_ = l_Lean_Syntax_getArg(v_x_28_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(3u);
v___x_94_ = l_Lean_Syntax_getArg(v_x_28_, v___x_93_);
v___x_95_ = l_Lean_Syntax_isNone(v___x_94_);
if (v___x_95_ == 0)
{
uint8_t v___x_96_; 
lean_inc(v___x_94_);
v___x_96_ = l_Lean_Syntax_matchesNull(v___x_94_, v___y_86_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v___x_94_);
lean_dec(v_importTk_92_);
lean_dec(v_metaTk_x3f_88_);
lean_dec(v___y_87_);
lean_dec(v_x_28_);
v___x_97_ = l_Lean_Fmt_Error_partialFormatter;
v___x_98_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___y_90_);
return v___x_98_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_99_ = l_Lean_Syntax_getArg(v___x_94_, v___x_35_);
lean_dec(v___x_94_);
v___x_100_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__6));
lean_inc(v___x_99_);
v___x_101_ = l_Lean_Syntax_isOfKind(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec(v___x_99_);
lean_dec(v_importTk_92_);
lean_dec(v_metaTk_x3f_88_);
lean_dec(v___y_87_);
lean_dec(v_x_28_);
v___x_102_ = l_Lean_Fmt_Error_partialFormatter;
v___x_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___y_90_);
return v___x_103_;
}
else
{
lean_object* v_allTk_x3f_104_; lean_object* v___x_105_; 
v_allTk_x3f_104_ = l_Lean_Syntax_getArg(v___x_99_, v___x_35_);
lean_dec(v___x_99_);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v_allTk_x3f_104_);
v___y_37_ = v___x_91_;
v___y_38_ = v_importTk_92_;
v___y_39_ = v_metaTk_x3f_88_;
v___y_40_ = v___y_87_;
v_allTk_x3f_41_ = v___x_105_;
v___y_42_ = v___y_89_;
v___y_43_ = v___y_90_;
goto v___jp_36_;
}
}
}
else
{
lean_object* v___x_106_; 
lean_dec(v___x_94_);
v___x_106_ = lean_box(0);
v___y_37_ = v___x_91_;
v___y_38_ = v_importTk_92_;
v___y_39_ = v_metaTk_x3f_88_;
v___y_40_ = v___y_87_;
v_allTk_x3f_41_ = v___x_106_;
v___y_42_ = v___y_89_;
v___y_43_ = v___y_90_;
goto v___jp_36_;
}
}
v___jp_107_:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = l_Lean_Syntax_getArg(v_x_28_, v___x_111_);
v___x_113_ = l_Lean_Syntax_isNone(v___x_112_);
if (v___x_113_ == 0)
{
uint8_t v___x_114_; 
lean_inc(v___x_112_);
v___x_114_ = l_Lean_Syntax_matchesNull(v___x_112_, v___x_111_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
lean_dec(v___x_112_);
lean_dec(v_publicTk_x3f_108_);
lean_dec(v_x_28_);
v___x_115_ = l_Lean_Fmt_Error_partialFormatter;
v___x_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___y_110_);
return v___x_116_;
}
else
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = l_Lean_Syntax_getArg(v___x_112_, v___x_35_);
lean_dec(v___x_112_);
v___x_118_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__8));
lean_inc(v___x_117_);
v___x_119_ = l_Lean_Syntax_isOfKind(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v___x_117_);
lean_dec(v_publicTk_x3f_108_);
lean_dec(v_x_28_);
v___x_120_ = l_Lean_Fmt_Error_partialFormatter;
v___x_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___y_110_);
return v___x_121_;
}
else
{
lean_object* v_metaTk_x3f_122_; lean_object* v___x_123_; 
v_metaTk_x3f_122_ = l_Lean_Syntax_getArg(v___x_117_, v___x_35_);
lean_dec(v___x_117_);
v___x_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_123_, 0, v_metaTk_x3f_122_);
v___y_86_ = v___x_111_;
v___y_87_ = v_publicTk_x3f_108_;
v_metaTk_x3f_88_ = v___x_123_;
v___y_89_ = v___y_109_;
v___y_90_ = v___y_110_;
goto v___jp_85_;
}
}
}
else
{
lean_object* v___x_124_; 
lean_dec(v___x_112_);
v___x_124_ = lean_box(0);
v___y_86_ = v___x_111_;
v___y_87_ = v_publicTk_x3f_108_;
v_metaTk_x3f_88_ = v___x_124_;
v___y_89_ = v___y_109_;
v___y_90_ = v___y_110_;
goto v___jp_85_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___boxed(lean_object* v_x_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport(v_x_139_, v_a_140_, v_a_141_);
lean_dec_ref(v_a_140_);
return v_res_142_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtHeader___closed__17(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = ((lean_object*)(l_Lean_Fmt_fmtHeader___closed__16));
v___x_187_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___boxed), 3, 0);
v___x_188_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtWith___boxed), 5, 2);
lean_closure_set(v___x_188_, 0, v___x_187_);
lean_closure_set(v___x_188_, 1, v___x_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHeader(lean_object* v_x_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_Fmt_fmtHeader___closed__1));
lean_inc(v_x_201_);
v___x_205_ = l_Lean_Syntax_isOfKind(v_x_201_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v_x_201_);
v___x_206_ = l_Lean_Fmt_Error_partialFormatter;
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v_a_203_);
return v___x_207_;
}
else
{
lean_object* v___x_208_; lean_object* v___y_210_; lean_object* v_preludeTk_x3f_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v_moduleTk_x3f_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_259_ = l_Lean_Syntax_getArg(v_x_201_, v___x_208_);
v___x_260_ = l_Lean_Syntax_isNone(v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_259_);
v___x_262_ = l_Lean_Syntax_matchesNull(v___x_259_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec(v___x_259_);
lean_dec(v_x_201_);
v___x_263_ = l_Lean_Fmt_Error_partialFormatter;
v___x_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_a_203_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_265_ = l_Lean_Syntax_getArg(v___x_259_, v___x_208_);
lean_dec(v___x_259_);
v___x_266_ = ((lean_object*)(l_Lean_Fmt_fmtHeader___closed__21));
lean_inc(v___x_265_);
v___x_267_ = l_Lean_Syntax_isOfKind(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v___x_265_);
lean_dec(v_x_201_);
v___x_268_ = l_Lean_Fmt_Error_partialFormatter;
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_a_203_);
return v___x_269_;
}
else
{
lean_object* v_moduleTk_x3f_270_; lean_object* v___x_271_; 
v_moduleTk_x3f_270_ = l_Lean_Syntax_getArg(v___x_265_, v___x_208_);
lean_dec(v___x_265_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v_moduleTk_x3f_270_);
v_moduleTk_x3f_242_ = v___x_271_;
v___y_243_ = v_a_202_;
v___y_244_ = v_a_203_;
goto v___jp_241_;
}
}
}
else
{
lean_object* v___x_272_; 
lean_dec(v___x_259_);
v___x_272_ = lean_box(0);
v_moduleTk_x3f_242_ = v___x_272_;
v___y_243_ = v_a_202_;
v___y_244_ = v_a_203_;
goto v___jp_241_;
}
v___jp_209_:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Fmt_fmt_x3f(v___y_210_, v___y_212_, v___y_213_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v_a_216_; lean_object* v___x_217_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
v_a_216_ = lean_ctor_get(v___x_214_, 1);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_214_, 2);
v___x_217_ = l_Lean_Fmt_fmt_x3f(v_preludeTk_x3f_211_, v___y_212_, v_a_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v_a_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_importsStx_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
v_a_219_ = lean_ctor_get(v___x_217_, 1);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_217_, 2);
v___x_220_ = lean_unsigned_to_nat(2u);
v___x_221_ = l_Lean_Syntax_getArg(v_x_201_, v___x_220_);
lean_dec(v_x_201_);
v_importsStx_222_ = l_Lean_Syntax_getArgs(v___x_221_);
lean_dec(v___x_221_);
v___x_223_ = lean_obj_once(&l_Lean_Fmt_fmtHeader___closed__17, &l_Lean_Fmt_fmtHeader___closed__17_once, _init_l_Lean_Fmt_fmtHeader___closed__17);
v___x_224_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v___x_223_, v_importsStx_222_, v___y_212_, v_a_219_);
lean_dec_ref(v_importsStx_222_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_240_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_a_226_ = lean_ctor_get(v___x_224_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_240_ == 0)
{
v___x_228_ = v___x_224_;
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_230_ = lean_mk_empty_array_with_capacity(v___x_220_);
lean_inc_ref(v___x_230_);
v___x_231_ = lean_array_push(v___x_230_, v_a_218_);
v___x_232_ = lean_array_push(v___x_231_, v_a_225_);
v___x_233_ = l_Lean_Fmt_Layouts_lines(v___x_232_);
lean_dec_ref(v___x_232_);
v___x_234_ = lean_array_push(v___x_230_, v_a_215_);
v___x_235_ = lean_array_push(v___x_234_, v___x_233_);
v___x_236_ = l_Lean_Fmt_Layouts_spacedLines(v___x_235_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_236_);
v___x_238_ = v___x_228_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_a_226_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_dec(v_a_218_);
lean_dec(v_a_215_);
return v___x_224_;
}
}
else
{
lean_dec(v_a_215_);
lean_dec(v_x_201_);
return v___x_217_;
}
}
else
{
lean_dec(v_preludeTk_x3f_211_);
lean_dec(v_x_201_);
return v___x_214_;
}
}
v___jp_241_:
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = l_Lean_Syntax_getArg(v_x_201_, v___x_245_);
v___x_247_ = l_Lean_Syntax_isNone(v___x_246_);
if (v___x_247_ == 0)
{
uint8_t v___x_248_; 
lean_inc(v___x_246_);
v___x_248_ = l_Lean_Syntax_matchesNull(v___x_246_, v___x_245_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v___x_246_);
lean_dec(v_moduleTk_x3f_242_);
lean_dec(v_x_201_);
v___x_249_ = l_Lean_Fmt_Error_partialFormatter;
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___y_244_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = l_Lean_Syntax_getArg(v___x_246_, v___x_208_);
lean_dec(v___x_246_);
v___x_252_ = ((lean_object*)(l_Lean_Fmt_fmtHeader___closed__19));
lean_inc(v___x_251_);
v___x_253_ = l_Lean_Syntax_isOfKind(v___x_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v___x_251_);
lean_dec(v_moduleTk_x3f_242_);
lean_dec(v_x_201_);
v___x_254_ = l_Lean_Fmt_Error_partialFormatter;
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___y_244_);
return v___x_255_;
}
else
{
lean_object* v_preludeTk_x3f_256_; lean_object* v___x_257_; 
v_preludeTk_x3f_256_ = l_Lean_Syntax_getArg(v___x_251_, v___x_208_);
lean_dec(v___x_251_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v_preludeTk_x3f_256_);
v___y_210_ = v_moduleTk_x3f_242_;
v_preludeTk_x3f_211_ = v___x_257_;
v___y_212_ = v___y_243_;
v___y_213_ = v___y_244_;
goto v___jp_209_;
}
}
}
else
{
lean_object* v___x_258_; 
lean_dec(v___x_246_);
v___x_258_ = lean_box(0);
v___y_210_ = v_moduleTk_x3f_242_;
v_preludeTk_x3f_211_ = v___x_258_;
v___y_212_ = v___y_243_;
v___y_213_ = v___y_244_;
goto v___jp_209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHeader___boxed(lean_object* v_x_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Fmt_fmtHeader(v_x_273_, v_a_274_, v_a_275_);
lean_dec_ref(v_a_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1(){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_283_ = l_Lean_Fmt_fmtAttribute;
v___x_284_ = ((lean_object*)(l_Lean_Fmt_fmtHeader___closed__1));
v___x_285_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___closed__1));
v___x_286_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtHeader___boxed), 3, 0);
v___x_287_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_283_, v___x_284_, v___x_285_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1___boxed(lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1();
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_headerDocs(lean_object* v_headerStx_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_293_; 
lean_inc(v_headerStx_290_);
v___x_293_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(v_headerStx_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v_a_295_; lean_object* v___x_296_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
v_a_295_ = lean_ctor_get(v___x_293_, 1);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_293_, 2);
lean_inc(v_headerStx_290_);
v___x_296_ = l_Lean_Fmt_fmt(v_headerStx_290_, v_a_291_, v_a_295_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v_a_298_; uint8_t v___x_299_; lean_object* v___x_300_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
v_a_298_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_296_, 2);
v___x_299_ = 1;
v___x_300_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v_headerStx_290_, v___x_299_, v_a_291_, v_a_298_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v_a_302_; lean_object* v___y_304_; uint8_t v___x_333_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_a_302_ = lean_ctor_get(v___x_300_, 1);
v___x_333_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_294_);
if (v___x_333_ == 0)
{
uint8_t v___x_334_; 
v___x_334_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_297_);
if (v___x_334_ == 0)
{
lean_object* v_doc_335_; lean_object* v_doc_336_; uint8_t v___x_337_; 
v_doc_335_ = lean_ctor_get(v_a_294_, 0);
lean_inc(v_doc_335_);
lean_dec(v_a_294_);
v_doc_336_ = lean_ctor_get(v_a_297_, 0);
lean_inc(v_doc_336_);
lean_dec(v_a_297_);
v___x_337_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_335_);
if (v___x_337_ == 0)
{
uint8_t v___x_338_; 
v___x_338_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_336_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_335_, v_doc_336_);
v___x_340_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_339_);
v___y_304_ = v___x_340_;
goto v___jp_303_;
}
else
{
lean_object* v___x_341_; 
lean_dec(v_doc_336_);
v___x_341_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_335_);
v___y_304_ = v___x_341_;
goto v___jp_303_;
}
}
else
{
lean_object* v___x_342_; 
lean_dec(v_doc_335_);
v___x_342_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_336_);
v___y_304_ = v___x_342_;
goto v___jp_303_;
}
}
else
{
lean_dec(v_a_297_);
v___y_304_ = v_a_294_;
goto v___jp_303_;
}
}
else
{
lean_dec(v_a_294_);
v___y_304_ = v_a_297_;
goto v___jp_303_;
}
v___jp_303_:
{
uint8_t v___x_305_; 
v___x_305_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_330_; 
lean_inc(v_a_302_);
lean_inc(v_a_301_);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; lean_object* v_unused_332_; 
v_unused_331_ = lean_ctor_get(v___x_300_, 1);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v___x_300_, 0);
lean_dec(v_unused_332_);
v___x_307_ = v___x_300_;
v_isShared_308_ = v_isSharedCheck_330_;
goto v_resetjp_306_;
}
else
{
lean_dec(v___x_300_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_330_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
uint8_t v___x_309_; 
v___x_309_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_301_);
if (v___x_309_ == 0)
{
lean_object* v_doc_310_; lean_object* v_doc_311_; uint8_t v___x_312_; 
v_doc_310_ = lean_ctor_get(v___y_304_, 0);
lean_inc(v_doc_310_);
lean_dec_ref(v___y_304_);
v_doc_311_ = lean_ctor_get(v_a_301_, 0);
lean_inc(v_doc_311_);
lean_dec(v_a_301_);
v___x_312_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_310_);
if (v___x_312_ == 0)
{
uint8_t v___x_313_; 
v___x_313_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_311_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_314_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_310_, v_doc_311_);
v___x_315_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_314_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_315_);
v___x_317_ = v___x_307_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_a_302_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_dec(v_doc_311_);
v___x_319_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_310_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_319_);
v___x_321_ = v___x_307_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_a_302_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_325_; 
lean_dec(v_doc_310_);
v___x_323_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_311_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_323_);
v___x_325_ = v___x_307_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_a_302_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_object* v___x_328_; 
lean_dec(v_a_301_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___y_304_);
v___x_328_ = v___x_307_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___y_304_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_a_302_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_dec_ref(v___y_304_);
return v___x_300_;
}
}
}
else
{
lean_dec(v_a_297_);
lean_dec(v_a_294_);
return v___x_300_;
}
}
else
{
lean_dec(v_a_294_);
lean_dec(v_headerStx_290_);
return v___x_296_;
}
}
else
{
lean_dec(v_headerStx_290_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_headerDocs___boxed(lean_object* v_headerStx_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_headerDocs(v_headerStx_343_, v_a_344_, v_a_345_);
lean_dec_ref(v_a_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_cmdDocs(lean_object* v_cmdStxs_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_350_ = lean_array_get_size(v_cmdStxs_347_);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_nat_dec_eq(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_box(0);
v___x_354_ = lean_array_get_borrowed(v___x_353_, v_cmdStxs_347_, v___x_351_);
lean_inc(v___x_354_);
v___x_355_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(v___x_354_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v_a_357_; lean_object* v___x_358_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
v_a_357_ = lean_ctor_get(v___x_355_, 1);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_355_, 2);
v___x_358_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(v_cmdStxs_347_, v_a_348_, v_a_357_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v_a_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
v_a_360_ = lean_ctor_get(v___x_358_, 1);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_358_, 2);
v___x_361_ = 1;
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_sub(v___x_350_, v___x_362_);
v___x_364_ = lean_array_get_borrowed(v___x_353_, v_cmdStxs_347_, v___x_363_);
lean_dec(v___x_363_);
lean_inc(v___x_364_);
v___x_365_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___x_364_, v___x_361_, v_a_348_, v_a_360_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v_a_367_; lean_object* v___y_369_; uint8_t v___x_398_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_a_367_ = lean_ctor_get(v___x_365_, 1);
v___x_398_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_356_);
if (v___x_398_ == 0)
{
uint8_t v___x_399_; 
v___x_399_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_359_);
if (v___x_399_ == 0)
{
lean_object* v_doc_400_; lean_object* v_doc_401_; uint8_t v___x_402_; 
v_doc_400_ = lean_ctor_get(v_a_356_, 0);
lean_inc(v_doc_400_);
lean_dec(v_a_356_);
v_doc_401_ = lean_ctor_get(v_a_359_, 0);
lean_inc(v_doc_401_);
lean_dec(v_a_359_);
v___x_402_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_400_);
if (v___x_402_ == 0)
{
uint8_t v___x_403_; 
v___x_403_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_401_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_400_, v_doc_401_);
v___x_405_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_404_);
v___y_369_ = v___x_405_;
goto v___jp_368_;
}
else
{
lean_object* v___x_406_; 
lean_dec(v_doc_401_);
v___x_406_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_400_);
v___y_369_ = v___x_406_;
goto v___jp_368_;
}
}
else
{
lean_object* v___x_407_; 
lean_dec(v_doc_400_);
v___x_407_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_401_);
v___y_369_ = v___x_407_;
goto v___jp_368_;
}
}
else
{
lean_dec(v_a_359_);
v___y_369_ = v_a_356_;
goto v___jp_368_;
}
}
else
{
lean_dec(v_a_356_);
v___y_369_ = v_a_359_;
goto v___jp_368_;
}
v___jp_368_:
{
uint8_t v___x_370_; 
v___x_370_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_395_; 
lean_inc(v_a_367_);
lean_inc(v_a_366_);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; lean_object* v_unused_397_; 
v_unused_396_ = lean_ctor_get(v___x_365_, 1);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v___x_365_, 0);
lean_dec(v_unused_397_);
v___x_372_ = v___x_365_;
v_isShared_373_ = v_isSharedCheck_395_;
goto v_resetjp_371_;
}
else
{
lean_dec(v___x_365_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_395_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
uint8_t v___x_374_; 
v___x_374_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_366_);
if (v___x_374_ == 0)
{
lean_object* v_doc_375_; lean_object* v_doc_376_; uint8_t v___x_377_; 
v_doc_375_ = lean_ctor_get(v___y_369_, 0);
lean_inc(v_doc_375_);
lean_dec_ref(v___y_369_);
v_doc_376_ = lean_ctor_get(v_a_366_, 0);
lean_inc(v_doc_376_);
lean_dec(v_a_366_);
v___x_377_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_375_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; 
v___x_378_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_376_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_379_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_375_, v_doc_376_);
v___x_380_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_379_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_380_);
v___x_382_ = v___x_372_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_a_367_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_386_; 
lean_dec(v_doc_376_);
v___x_384_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_375_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_384_);
v___x_386_ = v___x_372_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_a_367_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
else
{
lean_object* v___x_388_; lean_object* v___x_390_; 
lean_dec(v_doc_375_);
v___x_388_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_376_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_388_);
v___x_390_ = v___x_372_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_a_367_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v___x_393_; 
lean_dec(v_a_366_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___y_369_);
v___x_393_ = v___x_372_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___y_369_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_a_367_);
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
lean_dec_ref(v___y_369_);
return v___x_365_;
}
}
}
else
{
lean_dec(v_a_359_);
lean_dec(v_a_356_);
return v___x_365_;
}
}
else
{
lean_dec(v_a_356_);
return v___x_358_;
}
}
else
{
return v___x_355_;
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_a_349_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_cmdDocs___boxed(lean_object* v_cmdStxs_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_cmdDocs(v_cmdStxs_410_, v_a_411_, v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec_ref(v_cmdStxs_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtModule(lean_object* v_stx_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___y_420_; 
if (lean_obj_tag(v_stx_416_) == 1)
{
lean_object* v_kind_423_; 
v_kind_423_ = lean_ctor_get(v_stx_416_, 1);
if (lean_obj_tag(v_kind_423_) == 1)
{
lean_object* v_pre_424_; 
v_pre_424_ = lean_ctor_get(v_kind_423_, 0);
if (lean_obj_tag(v_pre_424_) == 1)
{
lean_object* v_pre_425_; 
v_pre_425_ = lean_ctor_get(v_pre_424_, 0);
if (lean_obj_tag(v_pre_425_) == 1)
{
lean_object* v_pre_426_; 
v_pre_426_ = lean_ctor_get(v_pre_425_, 0);
if (lean_obj_tag(v_pre_426_) == 1)
{
lean_object* v_pre_427_; 
v_pre_427_ = lean_ctor_get(v_pre_426_, 0);
if (lean_obj_tag(v_pre_427_) == 0)
{
lean_object* v_args_428_; lean_object* v_str_429_; lean_object* v_str_430_; lean_object* v_str_431_; lean_object* v_str_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_args_428_ = lean_ctor_get(v_stx_416_, 2);
v_str_429_ = lean_ctor_get(v_kind_423_, 1);
v_str_430_ = lean_ctor_get(v_pre_424_, 1);
v_str_431_ = lean_ctor_get(v_pre_425_, 1);
v_str_432_ = lean_ctor_get(v_pre_426_, 1);
v___x_433_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__0));
v___x_434_ = lean_string_dec_eq(v_str_432_, v___x_433_);
if (v___x_434_ == 0)
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
else
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__1));
v___x_436_ = lean_string_dec_eq(v_str_431_, v___x_435_);
if (v___x_436_ == 0)
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
else
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtImport___closed__2));
v___x_438_ = lean_string_dec_eq(v_str_430_, v___x_437_);
if (v___x_438_ == 0)
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
else
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_Fmt_fmtModule___closed__0));
v___x_440_ = lean_string_dec_eq(v_str_429_, v___x_439_);
if (v___x_440_ == 0)
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_array_get_size(v_args_428_);
v___x_442_ = lean_unsigned_to_nat(2u);
v___x_443_ = lean_nat_dec_eq(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_array_fget_borrowed(v_args_428_, v___x_444_);
if (lean_obj_tag(v___x_445_) == 1)
{
lean_object* v_kind_446_; 
v_kind_446_ = lean_ctor_get(v___x_445_, 1);
if (lean_obj_tag(v_kind_446_) == 1)
{
lean_object* v_pre_447_; 
v_pre_447_ = lean_ctor_get(v_kind_446_, 0);
if (lean_obj_tag(v_pre_447_) == 1)
{
lean_object* v_pre_448_; 
v_pre_448_ = lean_ctor_get(v_pre_447_, 0);
if (lean_obj_tag(v_pre_448_) == 1)
{
lean_object* v_pre_449_; 
v_pre_449_ = lean_ctor_get(v_pre_448_, 0);
if (lean_obj_tag(v_pre_449_) == 1)
{
lean_object* v_pre_450_; 
v_pre_450_ = lean_ctor_get(v_pre_449_, 0);
if (lean_obj_tag(v_pre_450_) == 0)
{
lean_object* v_args_451_; lean_object* v_str_452_; lean_object* v_str_453_; lean_object* v_str_454_; lean_object* v_str_455_; uint8_t v___x_456_; 
v_args_451_ = lean_ctor_get(v___x_445_, 2);
v_str_452_ = lean_ctor_get(v_kind_446_, 1);
v_str_453_ = lean_ctor_get(v_pre_447_, 1);
v_str_454_ = lean_ctor_get(v_pre_448_, 1);
v_str_455_ = lean_ctor_get(v_pre_449_, 1);
v___x_456_ = lean_string_dec_eq(v_str_455_, v___x_433_);
if (v___x_456_ == 0)
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
else
{
uint8_t v___x_457_; 
v___x_457_ = lean_string_dec_eq(v_str_454_, v___x_435_);
if (v___x_457_ == 0)
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
else
{
uint8_t v___x_458_; 
v___x_458_ = lean_string_dec_eq(v_str_453_, v___x_437_);
if (v___x_458_ == 0)
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_Fmt_fmtModule___closed__1));
v___x_460_ = lean_string_dec_eq(v_str_452_, v___x_459_);
if (v___x_460_ == 0)
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_array_fget_borrowed(v_args_428_, v___x_461_);
lean_inc(v___x_462_);
v___x_463_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_headerDocs(v___x_462_, v_a_417_, v_a_418_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
v_a_465_ = lean_ctor_get(v___x_463_, 1);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_463_, 2);
v___x_466_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule_cmdDocs(v_args_451_, v_a_417_, v_a_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v_a_468_; uint8_t v___x_469_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_a_468_ = lean_ctor_get(v___x_466_, 1);
v___x_469_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_464_);
if (v___x_469_ == 0)
{
lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_494_; 
lean_inc(v_a_468_);
lean_inc(v_a_467_);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; lean_object* v_unused_496_; 
v_unused_495_ = lean_ctor_get(v___x_466_, 1);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v___x_466_, 0);
lean_dec(v_unused_496_);
v___x_471_ = v___x_466_;
v_isShared_472_ = v_isSharedCheck_494_;
goto v_resetjp_470_;
}
else
{
lean_dec(v___x_466_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_494_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
uint8_t v___x_473_; 
v___x_473_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_467_);
if (v___x_473_ == 0)
{
lean_object* v_doc_474_; lean_object* v_doc_475_; uint8_t v___x_476_; 
v_doc_474_ = lean_ctor_get(v_a_464_, 0);
lean_inc(v_doc_474_);
lean_dec(v_a_464_);
v_doc_475_ = lean_ctor_get(v_a_467_, 0);
lean_inc(v_doc_475_);
lean_dec(v_a_467_);
v___x_476_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_474_);
if (v___x_476_ == 0)
{
uint8_t v___x_477_; 
v___x_477_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_475_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_478_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_474_, v_doc_475_);
v___x_479_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_478_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_479_);
v___x_481_ = v___x_471_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_a_468_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
else
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec(v_doc_475_);
v___x_483_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_474_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_483_);
v___x_485_ = v___x_471_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_a_468_);
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
lean_object* v___x_487_; lean_object* v___x_489_; 
lean_dec(v_doc_474_);
v___x_487_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_475_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_487_);
v___x_489_ = v___x_471_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_a_468_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
else
{
lean_object* v___x_492_; 
lean_dec(v_a_467_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v_a_464_);
v___x_492_ = v___x_471_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_464_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_a_468_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_dec(v_a_464_);
return v___x_466_;
}
}
else
{
lean_dec(v_a_464_);
return v___x_466_;
}
}
else
{
return v___x_463_;
}
}
}
}
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
}
}
}
}
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
}
else
{
v___y_420_ = v_a_418_;
goto v___jp_419_;
}
v___jp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = l_Lean_Fmt_Error_partialFormatter;
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___y_420_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtModule___boxed(lean_object* v_stx_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Fmt_fmtModule(v_stx_497_, v_a_498_, v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_stx_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1(){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_512_ = l_Lean_Fmt_fmtAttribute;
v___x_513_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__0));
v___x_514_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___closed__2));
v___x_515_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtModule___boxed), 3, 0);
v___x_516_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_512_, v___x_513_, v___x_514_, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1___boxed(lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1();
return v_res_518_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_Comments(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Module(uint8_t builtin) {
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
res = runtime_initialize_Lean_Fmt_FmtM_Comments(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtHeader___regBuiltin_Lean_Fmt_fmtHeader__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Module_0__Lean_Fmt_fmtModule___regBuiltin_Lean_Fmt_fmtModule__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Module(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_Comments(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Module(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_Comments(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Parser_Module(builtin);
}
#ifdef __cplusplus
}
#endif
