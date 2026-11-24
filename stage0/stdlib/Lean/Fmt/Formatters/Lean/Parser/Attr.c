// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Parser.Attr
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Parser.Attr import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSimpleAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtSimpleAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSimpleAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtSimpleAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSimpleAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Fmt_fmtSimpleAttr___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtSimpleAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Fmt_fmtSimpleAttr___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpleAttr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpleAttr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpleAttr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtSimpleAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Fmt_fmtSimpleAttr___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtSimpleAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtSimpleAttr___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtSimpleAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtSimpleAttr___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpleAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpleAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtSimpleAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(178, 93, 130, 6, 221, 109, 109, 78)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMacroAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Fmt_fmtMacroAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMacroAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMacroAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMacroAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 70, 6, 8, 133, 137, 74)}};
static const lean_object* l_Lean_Fmt_fmtMacroAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMacroAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtMacroAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 57, 175, 244, 214, 211, 175, 109)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtExportAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l_Lean_Fmt_fmtExportAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtExportAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtExportAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtExportAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExportAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtExportAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExportAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtExportAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExportAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtExportAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 70, 85, 26, 88, 142, 178, 115)}};
static const lean_object* l_Lean_Fmt_fmtExportAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtExportAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExportAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExportAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtExportAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 155, 210, 161, 18, 39, 155, 95)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRecursorAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "recursor"};
static const lean_object* l_Lean_Fmt_fmtRecursorAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRecursorAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRecursorAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRecursorAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRecursorAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRecursorAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRecursorAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtRecursorAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRecursorAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRecursorAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 29, 106, 40, 200, 118, 31, 85)}};
static const lean_object* l_Lean_Fmt_fmtRecursorAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRecursorAttr___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRecursorAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtRecursorAttr___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRecursorAttr___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtRecursorAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRecursorAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtRecursorAttr___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRecursorAttr___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRecursorAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRecursorAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtRecursorAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 99, 116, 89, 3, 160, 11, 18)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtClassAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtClassAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtAtomic___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "class"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 14, 146, 125, 144, 1, 65, 64)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtClassAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(71, 216, 216, 38, 138, 73, 200, 247)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtInstanceAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l_Lean_Fmt_fmtInstanceAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtInstanceAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtInstanceAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtInstanceAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInstanceAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtInstanceAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInstanceAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtInstanceAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInstanceAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtInstanceAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 1, 138, 227, 223, 112, 103, 179)}};
static const lean_object* l_Lean_Fmt_fmtInstanceAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtInstanceAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInstanceAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInstanceAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtInstanceAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 216, 146, 154, 140, 3, 147, 125)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDefaultInstanceAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "default_instance"};
static const lean_object* l_Lean_Fmt_fmtDefaultInstanceAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDefaultInstanceAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDefaultInstanceAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDefaultInstanceAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDefaultInstanceAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDefaultInstanceAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDefaultInstanceAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtDefaultInstanceAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDefaultInstanceAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDefaultInstanceAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 215, 188, 14, 80, 67, 224, 116)}};
static const lean_object* l_Lean_Fmt_fmtDefaultInstanceAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDefaultInstanceAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDefaultInstanceAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDefaultInstanceAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtDefaultInstanceAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 136, 59, 130, 61, 171, 0, 220)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSpecializeAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "specialize"};
static const lean_object* l_Lean_Fmt_fmtSpecializeAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSpecializeAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSpecializeAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSpecializeAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSpecializeAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSpecializeAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSpecializeAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtSpecializeAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSpecializeAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSpecializeAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 28, 50, 2, 100, 118, 84, 52)}};
static const lean_object* l_Lean_Fmt_fmtSpecializeAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSpecializeAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSpecializeAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSpecializeAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtSpecializeAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 105, 215, 125, 149, 20, 239, 124)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtExternEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "externEntry"};
static const lean_object* l_Lean_Fmt_fmtExternEntry___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtExternEntry___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtExternEntry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtExternEntry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExternEntry___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtExternEntry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExternEntry___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtExternEntry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExternEntry___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtExternEntry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 120, 255, 6, 244, 195, 179, 180)}};
static const lean_object* l_Lean_Fmt_fmtExternEntry___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtExternEntry___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtExternEntry___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Fmt_fmtExternEntry___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtExternEntry___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtExternEntry___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtExternEntry___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Fmt_fmtExternEntry___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtExternEntry___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExternEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExternEntry___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtExternEntry"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 46, 247, 110, 188, 169, 174, 127)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtExternAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "extern"};
static const lean_object* l_Lean_Fmt_fmtExternAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtExternAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtExternAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtExternAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExternAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtExternAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExternAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtExternAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtExternAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtExternAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 126, 252, 124, 35, 62, 180, 112)}};
static const lean_object* l_Lean_Fmt_fmtExternAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtExternAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExternAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExternAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtExternAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 5, 193, 23, 43, 156, 104, 121)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticAltAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tactic_alt"};
static const lean_object* l_Lean_Fmt_fmtTacticAltAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticAltAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticAltAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticAltAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticAltAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticAltAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticAltAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticAltAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticAltAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticAltAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 168, 96, 206, 229, 58, 101)}};
static const lean_object* l_Lean_Fmt_fmtTacticAltAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticAltAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticAltAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticAltAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtTacticAltAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 166, 224, 161, 200, 119, 119, 40)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticTagAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tactic_tag"};
static const lean_object* l_Lean_Fmt_fmtTacticTagAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticTagAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticTagAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticTagAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticTagAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticTagAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticTagAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticTagAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticTagAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticTagAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 70, 119, 85, 147, 120, 119, 38)}};
static const lean_object* l_Lean_Fmt_fmtTacticTagAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticTagAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticTagAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticTagAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtTacticTagAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 168, 43, 193, 141, 124, 60, 15)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTacticNameAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_name"};
static const lean_object* l_Lean_Fmt_fmtTacticNameAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTacticNameAttr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTacticNameAttr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticNameAttr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticNameAttr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticNameAttr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticNameAttr___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Fmt_fmtTacticNameAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTacticNameAttr___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTacticNameAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 253, 162, 55, 13, 176, 86, 10)}};
static const lean_object* l_Lean_Fmt_fmtTacticNameAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTacticNameAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticNameAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticNameAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtTacticNameAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSimpleAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 20, 118, 176, 16, 212, 138, 188)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpleAttr(lean_object* v_x_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lean_Fmt_fmtSimpleAttr___closed__4));
lean_inc(v_x_13_);
v___x_17_ = l_Lean_Syntax_isOfKind(v_x_13_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_x_13_);
v___x_18_ = l_Lean_Fmt_Error_partialFormatter;
v___x_19_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v_a_15_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; lean_object* v___y_25_; lean_object* v___y_26_; lean_object* v___y_27_; lean_object* v___y_28_; lean_object* v_arg_x3f_47_; lean_object* v___y_48_; lean_object* v___y_49_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = l_Lean_Syntax_getArg(v_x_13_, v___x_20_);
v___x_22_ = ((lean_object*)(l_Lean_Fmt_fmtSimpleAttr___closed__6));
lean_inc(v___x_21_);
v___x_23_ = l_Lean_Syntax_isOfKind(v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v___x_21_);
lean_dec(v_x_13_);
v___x_64_ = l_Lean_Fmt_Error_partialFormatter;
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v_a_15_);
return v___x_65_;
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = l_Lean_Syntax_getArg(v_x_13_, v___x_66_);
lean_dec(v_x_13_);
v___x_68_ = l_Lean_Syntax_isNone(v___x_67_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
lean_inc(v___x_67_);
v___x_69_ = l_Lean_Syntax_matchesNull(v___x_67_, v___x_66_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v___x_67_);
lean_dec(v___x_21_);
v___x_70_ = l_Lean_Fmt_Error_partialFormatter;
v___x_71_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v_a_15_);
return v___x_71_;
}
else
{
lean_object* v_arg_x3f_72_; lean_object* v___x_73_; 
v_arg_x3f_72_ = l_Lean_Syntax_getArg(v___x_67_, v___x_20_);
lean_dec(v___x_67_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v_arg_x3f_72_);
v_arg_x3f_47_ = v___x_73_;
v___y_48_ = v_a_14_;
v___y_49_ = v_a_15_;
goto v___jp_46_;
}
}
else
{
lean_object* v___x_74_; 
lean_dec(v___x_67_);
v___x_74_ = lean_box(0);
v_arg_x3f_47_ = v___x_74_;
v___y_48_ = v_a_14_;
v___y_49_ = v_a_15_;
goto v___jp_46_;
}
}
v___jp_24_:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Fmt_fmt_x3f(v___y_28_, v___y_27_, v___y_25_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_45_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_a_31_ = lean_ctor_get(v___x_29_, 1);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_33_ = v___x_29_;
v_isShared_34_ = v_isSharedCheck_45_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_45_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_35_ = lean_unsigned_to_nat(2u);
v___x_36_ = lean_mk_empty_array_with_capacity(v___x_35_);
v___x_37_ = lean_array_push(v___x_36_, v___y_26_);
v___x_38_ = lean_array_push(v___x_37_, v_a_30_);
v___x_39_ = 0;
v___x_40_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_40_, 0, v___x_23_);
lean_ctor_set_uint8(v___x_40_, 1, v___x_39_);
lean_ctor_set_uint8(v___x_40_, 2, v___x_39_);
lean_ctor_set_uint8(v___x_40_, 3, v___x_39_);
v___x_41_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_38_, v___x_40_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_41_);
v___x_43_ = v___x_33_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_a_31_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
else
{
lean_dec_ref(v___y_26_);
return v___x_29_;
}
}
v___jp_46_:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Fmt_fmt(v___x_21_, v___y_48_, v___y_49_);
if (lean_obj_tag(v___x_50_) == 0)
{
if (lean_obj_tag(v_arg_x3f_47_) == 0)
{
lean_object* v_a_51_; lean_object* v_a_52_; lean_object* v___x_53_; 
v_a_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_a_51_);
v_a_52_ = lean_ctor_get(v___x_50_, 1);
lean_inc(v_a_52_);
lean_dec_ref_known(v___x_50_, 2);
v___x_53_ = lean_box(0);
v___y_25_ = v_a_52_;
v___y_26_ = v_a_51_;
v___y_27_ = v___y_48_;
v___y_28_ = v___x_53_;
goto v___jp_24_;
}
else
{
lean_object* v_a_54_; lean_object* v_a_55_; lean_object* v_val_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
v_a_54_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_a_54_);
v_a_55_ = lean_ctor_get(v___x_50_, 1);
lean_inc(v_a_55_);
lean_dec_ref_known(v___x_50_, 2);
v_val_56_ = lean_ctor_get(v_arg_x3f_47_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v_arg_x3f_47_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v_arg_x3f_47_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_val_56_);
lean_dec(v_arg_x3f_47_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_val_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
v___y_25_ = v_a_55_;
v___y_26_ = v_a_54_;
v___y_27_ = v___y_48_;
v___y_28_ = v___x_61_;
goto v___jp_24_;
}
}
}
}
else
{
lean_dec(v_arg_x3f_47_);
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSimpleAttr___boxed(lean_object* v_x_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Fmt_fmtSimpleAttr(v_x_75_, v_a_76_, v_a_77_);
lean_dec_ref(v_a_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1(){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = l_Lean_Fmt_fmtAttribute;
v___x_87_ = ((lean_object*)(l_Lean_Fmt_fmtSimpleAttr___closed__4));
v___x_88_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___closed__2));
v___x_89_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSimpleAttr___boxed), 3, 0);
v___x_90_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_86_, v___x_87_, v___x_88_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1___boxed(lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1();
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroAttr(lean_object* v_x_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = ((lean_object*)(l_Lean_Fmt_fmtMacroAttr___closed__1));
lean_inc(v_x_99_);
v___x_103_ = l_Lean_Syntax_isOfKind(v_x_99_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_x_99_);
v___x_104_ = l_Lean_Fmt_Error_partialFormatter;
v___x_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v_a_101_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = l_Lean_Syntax_getArg(v_x_99_, v___x_106_);
v___x_108_ = ((lean_object*)(l_Lean_Fmt_fmtSimpleAttr___closed__6));
lean_inc(v___x_107_);
v___x_109_ = l_Lean_Syntax_isOfKind(v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec(v___x_107_);
lean_dec(v_x_99_);
v___x_110_ = l_Lean_Fmt_Error_partialFormatter;
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_a_101_);
return v___x_111_;
}
else
{
lean_object* v___x_112_; lean_object* v_macroTk_113_; lean_object* v___x_114_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v_macroTk_113_ = l_Lean_Syntax_getArg(v_x_99_, v___x_112_);
lean_dec(v_x_99_);
v___x_114_ = l_Lean_Fmt_fmt(v_macroTk_113_, v_a_100_, v_a_101_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v_a_116_; lean_object* v___x_117_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_a_115_);
v_a_116_ = lean_ctor_get(v___x_114_, 1);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_114_, 2);
v___x_117_ = l_Lean_Fmt_fmt(v___x_107_, v_a_100_, v_a_116_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_133_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_a_119_ = lean_ctor_get(v___x_117_, 1);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_133_ == 0)
{
v___x_121_ = v___x_117_;
v_isShared_122_ = v_isSharedCheck_133_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_133_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_123_ = lean_unsigned_to_nat(2u);
v___x_124_ = lean_mk_empty_array_with_capacity(v___x_123_);
v___x_125_ = lean_array_push(v___x_124_, v_a_115_);
v___x_126_ = lean_array_push(v___x_125_, v_a_118_);
v___x_127_ = 0;
v___x_128_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_128_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_128_, 1, v___x_127_);
lean_ctor_set_uint8(v___x_128_, 2, v___x_127_);
lean_ctor_set_uint8(v___x_128_, 3, v___x_127_);
v___x_129_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_126_, v___x_128_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_129_);
v___x_131_ = v___x_121_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_a_119_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
else
{
lean_dec(v_a_115_);
return v___x_117_;
}
}
else
{
lean_dec(v___x_107_);
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroAttr___boxed(lean_object* v_x_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Fmt_fmtMacroAttr(v_x_134_, v_a_135_, v_a_136_);
lean_dec_ref(v_a_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_144_ = l_Lean_Fmt_fmtAttribute;
v___x_145_ = ((lean_object*)(l_Lean_Fmt_fmtMacroAttr___closed__1));
v___x_146_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___closed__1));
v___x_147_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMacroAttr___boxed), 3, 0);
v___x_148_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_144_, v___x_145_, v___x_146_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1___boxed(lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1();
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExportAttr(lean_object* v_x_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_Fmt_fmtExportAttr___closed__1));
lean_inc(v_x_157_);
v___x_161_ = l_Lean_Syntax_isOfKind(v_x_157_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_x_157_);
v___x_162_ = l_Lean_Fmt_Error_partialFormatter;
v___x_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_a_159_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = l_Lean_Syntax_getArg(v_x_157_, v___x_164_);
v___x_166_ = ((lean_object*)(l_Lean_Fmt_fmtSimpleAttr___closed__6));
lean_inc(v___x_165_);
v___x_167_ = l_Lean_Syntax_isOfKind(v___x_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v___x_165_);
lean_dec(v_x_157_);
v___x_168_ = l_Lean_Fmt_Error_partialFormatter;
v___x_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_a_159_);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v_exportTk_171_; lean_object* v___x_172_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v_exportTk_171_ = l_Lean_Syntax_getArg(v_x_157_, v___x_170_);
lean_dec(v_x_157_);
v___x_172_ = l_Lean_Fmt_fmt(v_exportTk_171_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v_a_174_; lean_object* v___x_175_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
v_a_174_ = lean_ctor_get(v___x_172_, 1);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_172_, 2);
v___x_175_ = l_Lean_Fmt_fmt(v___x_165_, v_a_158_, v_a_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_191_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_a_177_ = lean_ctor_get(v___x_175_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_191_ == 0)
{
v___x_179_ = v___x_175_;
v_isShared_180_ = v_isSharedCheck_191_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_191_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_181_ = lean_unsigned_to_nat(2u);
v___x_182_ = lean_mk_empty_array_with_capacity(v___x_181_);
v___x_183_ = lean_array_push(v___x_182_, v_a_173_);
v___x_184_ = lean_array_push(v___x_183_, v_a_176_);
v___x_185_ = 0;
v___x_186_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_186_, 0, v___x_167_);
lean_ctor_set_uint8(v___x_186_, 1, v___x_185_);
lean_ctor_set_uint8(v___x_186_, 2, v___x_185_);
lean_ctor_set_uint8(v___x_186_, 3, v___x_185_);
v___x_187_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_184_, v___x_186_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_187_);
v___x_189_ = v___x_179_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_a_177_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
else
{
lean_dec(v_a_173_);
return v___x_175_;
}
}
else
{
lean_dec(v___x_165_);
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExportAttr___boxed(lean_object* v_x_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Fmt_fmtExportAttr(v_x_192_, v_a_193_, v_a_194_);
lean_dec_ref(v_a_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1(){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_202_ = l_Lean_Fmt_fmtAttribute;
v___x_203_ = ((lean_object*)(l_Lean_Fmt_fmtExportAttr___closed__1));
v___x_204_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___closed__1));
v___x_205_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExportAttr___boxed), 3, 0);
v___x_206_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_202_, v___x_203_, v___x_204_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1___boxed(lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1();
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRecursorAttr(lean_object* v_x_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_Fmt_fmtRecursorAttr___closed__1));
lean_inc(v_x_218_);
v___x_222_ = l_Lean_Syntax_isOfKind(v_x_218_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v_x_218_);
v___x_223_ = l_Lean_Fmt_Error_partialFormatter;
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v_a_220_);
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = l_Lean_Syntax_getArg(v_x_218_, v___x_225_);
v___x_227_ = ((lean_object*)(l_Lean_Fmt_fmtRecursorAttr___closed__3));
lean_inc(v___x_226_);
v___x_228_ = l_Lean_Syntax_isOfKind(v___x_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v___x_226_);
lean_dec(v_x_218_);
v___x_229_ = l_Lean_Fmt_Error_partialFormatter;
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v_a_220_);
return v___x_230_;
}
else
{
lean_object* v___x_231_; lean_object* v_recursorTk_232_; lean_object* v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v_recursorTk_232_ = l_Lean_Syntax_getArg(v_x_218_, v___x_231_);
lean_dec(v_x_218_);
v___x_233_ = l_Lean_Fmt_fmt(v_recursorTk_232_, v_a_219_, v_a_220_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v_a_235_; lean_object* v___x_236_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
v_a_235_ = lean_ctor_get(v___x_233_, 1);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_233_, 2);
v___x_236_ = l_Lean_Fmt_fmt(v___x_226_, v_a_219_, v_a_235_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_252_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_a_238_ = lean_ctor_get(v___x_236_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_252_ == 0)
{
v___x_240_ = v___x_236_;
v_isShared_241_ = v_isSharedCheck_252_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_252_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_242_ = lean_unsigned_to_nat(2u);
v___x_243_ = lean_mk_empty_array_with_capacity(v___x_242_);
v___x_244_ = lean_array_push(v___x_243_, v_a_234_);
v___x_245_ = lean_array_push(v___x_244_, v_a_237_);
v___x_246_ = 0;
v___x_247_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_247_, 0, v___x_228_);
lean_ctor_set_uint8(v___x_247_, 1, v___x_246_);
lean_ctor_set_uint8(v___x_247_, 2, v___x_246_);
lean_ctor_set_uint8(v___x_247_, 3, v___x_246_);
v___x_248_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_245_, v___x_247_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_248_);
v___x_250_ = v___x_240_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_a_238_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_dec(v_a_234_);
return v___x_236_;
}
}
else
{
lean_dec(v___x_226_);
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRecursorAttr___boxed(lean_object* v_x_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Fmt_fmtRecursorAttr(v_x_253_, v_a_254_, v_a_255_);
lean_dec_ref(v_a_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1(){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_263_ = l_Lean_Fmt_fmtAttribute;
v___x_264_ = ((lean_object*)(l_Lean_Fmt_fmtRecursorAttr___closed__1));
v___x_265_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___closed__1));
v___x_266_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRecursorAttr___boxed), 3, 0);
v___x_267_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_263_, v___x_264_, v___x_265_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1___boxed(lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1();
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtClassAttr(lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Fmt_fmtAtomic(v_a_270_, v_a_271_, v_a_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtClassAttr___boxed(lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Fmt_fmtClassAttr(v_a_274_, v_a_275_, v_a_276_);
lean_dec_ref(v_a_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1(){
_start:
{
lean_object* v___f_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___f_291_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__0));
v___x_292_ = l_Lean_Fmt_fmtAttribute;
v___x_293_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__2));
v___x_294_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___closed__4));
v___x_295_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_292_, v___x_293_, v___x_294_, v___f_291_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1___boxed(lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1();
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInstanceAttr(lean_object* v_x_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; 
v___x_307_ = ((lean_object*)(l_Lean_Fmt_fmtInstanceAttr___closed__1));
lean_inc(v_x_304_);
v___x_308_ = l_Lean_Syntax_isOfKind(v_x_304_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_x_304_);
v___x_331_ = l_Lean_Fmt_Error_partialFormatter;
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_a_306_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v_instanceTk_334_; lean_object* v_prio_x3f_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_333_ = lean_unsigned_to_nat(0u);
v_instanceTk_334_ = l_Lean_Syntax_getArg(v_x_304_, v___x_333_);
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = l_Lean_Syntax_getArg(v_x_304_, v___x_353_);
lean_dec(v_x_304_);
v___x_355_ = l_Lean_Syntax_isNone(v___x_354_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; 
lean_inc(v___x_354_);
v___x_356_ = l_Lean_Syntax_matchesNull(v___x_354_, v___x_353_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v___x_354_);
lean_dec(v_instanceTk_334_);
v___x_357_ = l_Lean_Fmt_Error_partialFormatter;
v___x_358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_a_306_);
return v___x_358_;
}
else
{
lean_object* v_prio_x3f_359_; lean_object* v___x_360_; 
v_prio_x3f_359_ = l_Lean_Syntax_getArg(v___x_354_, v___x_333_);
lean_dec(v___x_354_);
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v_prio_x3f_359_);
v_prio_x3f_336_ = v___x_360_;
v___y_337_ = v_a_305_;
v___y_338_ = v_a_306_;
goto v___jp_335_;
}
}
else
{
lean_object* v___x_361_; 
lean_dec(v___x_354_);
v___x_361_ = lean_box(0);
v_prio_x3f_336_ = v___x_361_;
v___y_337_ = v_a_305_;
v___y_338_ = v_a_306_;
goto v___jp_335_;
}
v___jp_335_:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Fmt_fmt(v_instanceTk_334_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
if (lean_obj_tag(v_prio_x3f_336_) == 0)
{
lean_object* v_a_340_; lean_object* v_a_341_; lean_object* v___x_342_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
v_a_341_ = lean_ctor_get(v___x_339_, 1);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_339_, 2);
v___x_342_ = lean_box(0);
v___y_310_ = v_a_341_;
v___y_311_ = v___y_337_;
v___y_312_ = v_a_340_;
v___y_313_ = v___x_342_;
goto v___jp_309_;
}
else
{
lean_object* v_a_343_; lean_object* v_a_344_; lean_object* v_val_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_a_343_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_343_);
v_a_344_ = lean_ctor_get(v___x_339_, 1);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_339_, 2);
v_val_345_ = lean_ctor_get(v_prio_x3f_336_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v_prio_x3f_336_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v_prio_x3f_336_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_val_345_);
lean_dec(v_prio_x3f_336_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_val_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
v___y_310_ = v_a_344_;
v___y_311_ = v___y_337_;
v___y_312_ = v_a_343_;
v___y_313_ = v___x_350_;
goto v___jp_309_;
}
}
}
}
else
{
lean_dec(v_prio_x3f_336_);
return v___x_339_;
}
}
}
v___jp_309_:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Fmt_fmt_x3f(v___y_313_, v___y_311_, v___y_310_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_330_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_a_316_ = lean_ctor_get(v___x_314_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_330_ == 0)
{
v___x_318_ = v___x_314_;
v_isShared_319_ = v_isSharedCheck_330_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_330_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_320_ = lean_unsigned_to_nat(2u);
v___x_321_ = lean_mk_empty_array_with_capacity(v___x_320_);
v___x_322_ = lean_array_push(v___x_321_, v___y_312_);
v___x_323_ = lean_array_push(v___x_322_, v_a_315_);
v___x_324_ = 0;
v___x_325_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_325_, 0, v___x_308_);
lean_ctor_set_uint8(v___x_325_, 1, v___x_324_);
lean_ctor_set_uint8(v___x_325_, 2, v___x_324_);
lean_ctor_set_uint8(v___x_325_, 3, v___x_324_);
v___x_326_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_323_, v___x_325_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_326_);
v___x_328_ = v___x_318_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_a_316_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
else
{
lean_dec_ref(v___y_312_);
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInstanceAttr___boxed(lean_object* v_x_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Fmt_fmtInstanceAttr(v_x_362_, v_a_363_, v_a_364_);
lean_dec_ref(v_a_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1(){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_372_ = l_Lean_Fmt_fmtAttribute;
v___x_373_ = ((lean_object*)(l_Lean_Fmt_fmtInstanceAttr___closed__1));
v___x_374_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___closed__1));
v___x_375_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInstanceAttr___boxed), 3, 0);
v___x_376_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_372_, v___x_373_, v___x_374_, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1___boxed(lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1();
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDefaultInstanceAttr(lean_object* v_x_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; 
v___x_388_ = ((lean_object*)(l_Lean_Fmt_fmtDefaultInstanceAttr___closed__1));
lean_inc(v_x_385_);
v___x_389_ = l_Lean_Syntax_isOfKind(v_x_385_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec(v_x_385_);
v___x_412_ = l_Lean_Fmt_Error_partialFormatter;
v___x_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_a_387_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v_instanceTk_415_; lean_object* v_prio_x3f_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v_instanceTk_415_ = l_Lean_Syntax_getArg(v_x_385_, v___x_414_);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = l_Lean_Syntax_getArg(v_x_385_, v___x_434_);
lean_dec(v_x_385_);
v___x_436_ = l_Lean_Syntax_isNone(v___x_435_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; 
lean_inc(v___x_435_);
v___x_437_ = l_Lean_Syntax_matchesNull(v___x_435_, v___x_434_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v___x_435_);
lean_dec(v_instanceTk_415_);
v___x_438_ = l_Lean_Fmt_Error_partialFormatter;
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v_a_387_);
return v___x_439_;
}
else
{
lean_object* v_prio_x3f_440_; lean_object* v___x_441_; 
v_prio_x3f_440_ = l_Lean_Syntax_getArg(v___x_435_, v___x_414_);
lean_dec(v___x_435_);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v_prio_x3f_440_);
v_prio_x3f_417_ = v___x_441_;
v___y_418_ = v_a_386_;
v___y_419_ = v_a_387_;
goto v___jp_416_;
}
}
else
{
lean_object* v___x_442_; 
lean_dec(v___x_435_);
v___x_442_ = lean_box(0);
v_prio_x3f_417_ = v___x_442_;
v___y_418_ = v_a_386_;
v___y_419_ = v_a_387_;
goto v___jp_416_;
}
v___jp_416_:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Fmt_fmt(v_instanceTk_415_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_420_) == 0)
{
if (lean_obj_tag(v_prio_x3f_417_) == 0)
{
lean_object* v_a_421_; lean_object* v_a_422_; lean_object* v___x_423_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
v_a_422_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_420_, 2);
v___x_423_ = lean_box(0);
v___y_391_ = v_a_421_;
v___y_392_ = v_a_422_;
v___y_393_ = v___y_418_;
v___y_394_ = v___x_423_;
goto v___jp_390_;
}
else
{
lean_object* v_a_424_; lean_object* v_a_425_; lean_object* v_val_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_a_424_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_424_);
v_a_425_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_420_, 2);
v_val_426_ = lean_ctor_get(v_prio_x3f_417_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_prio_x3f_417_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v_prio_x3f_417_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_val_426_);
lean_dec(v_prio_x3f_417_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_val_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
v___y_391_ = v_a_424_;
v___y_392_ = v_a_425_;
v___y_393_ = v___y_418_;
v___y_394_ = v___x_431_;
goto v___jp_390_;
}
}
}
}
else
{
lean_dec(v_prio_x3f_417_);
return v___x_420_;
}
}
}
v___jp_390_:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Fmt_fmt_x3f(v___y_394_, v___y_393_, v___y_392_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_411_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_a_397_ = lean_ctor_get(v___x_395_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_411_ == 0)
{
v___x_399_ = v___x_395_;
v_isShared_400_ = v_isSharedCheck_411_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_411_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_401_ = lean_unsigned_to_nat(2u);
v___x_402_ = lean_mk_empty_array_with_capacity(v___x_401_);
v___x_403_ = lean_array_push(v___x_402_, v___y_391_);
v___x_404_ = lean_array_push(v___x_403_, v_a_396_);
v___x_405_ = 0;
v___x_406_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_406_, 0, v___x_389_);
lean_ctor_set_uint8(v___x_406_, 1, v___x_405_);
lean_ctor_set_uint8(v___x_406_, 2, v___x_405_);
lean_ctor_set_uint8(v___x_406_, 3, v___x_405_);
v___x_407_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_404_, v___x_406_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_407_);
v___x_409_ = v___x_399_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_a_397_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_dec_ref(v___y_391_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDefaultInstanceAttr___boxed(lean_object* v_x_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Fmt_fmtDefaultInstanceAttr(v_x_443_, v_a_444_, v_a_445_);
lean_dec_ref(v_a_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1(){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_453_ = l_Lean_Fmt_fmtAttribute;
v___x_454_ = ((lean_object*)(l_Lean_Fmt_fmtDefaultInstanceAttr___closed__1));
v___x_455_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___closed__1));
v___x_456_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDefaultInstanceAttr___boxed), 3, 0);
v___x_457_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_453_, v___x_454_, v___x_455_, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1___boxed(lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1();
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSpecializeAttr(lean_object* v_x_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = ((lean_object*)(l_Lean_Fmt_fmtSpecializeAttr___closed__1));
lean_inc(v_x_466_);
v___x_470_ = l_Lean_Syntax_isOfKind(v_x_466_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v_x_466_);
v___x_471_ = l_Lean_Fmt_Error_partialFormatter;
v___x_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v_a_468_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; lean_object* v_specializeTk_474_; lean_object* v___x_475_; 
v___x_473_ = lean_unsigned_to_nat(0u);
v_specializeTk_474_ = l_Lean_Syntax_getArg(v_x_466_, v___x_473_);
v___x_475_ = l_Lean_Fmt_fmt(v_specializeTk_474_, v_a_467_, v_a_468_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v_a_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_args_480_; lean_object* v___x_481_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
v_a_477_ = lean_ctor_get(v___x_475_, 1);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_475_, 2);
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = l_Lean_Syntax_getArg(v_x_466_, v___x_478_);
lean_dec(v_x_466_);
v_args_480_ = l_Lean_Syntax_getArgs(v___x_479_);
lean_dec(v___x_479_);
v___x_481_ = l_Lean_Fmt_fmtArray___redArg(v_args_480_, v_a_467_, v_a_477_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_496_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_a_483_ = lean_ctor_get(v___x_481_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_496_ == 0)
{
v___x_485_ = v___x_481_;
v_isShared_486_ = v_isSharedCheck_496_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_496_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_487_ = lean_mk_empty_array_with_capacity(v___x_478_);
v___x_488_ = lean_array_push(v___x_487_, v_a_476_);
v___x_489_ = l_Array_append___redArg(v___x_488_, v_a_482_);
lean_dec(v_a_482_);
v___x_490_ = 0;
v___x_491_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_491_, 0, v___x_470_);
lean_ctor_set_uint8(v___x_491_, 1, v___x_490_);
lean_ctor_set_uint8(v___x_491_, 2, v___x_490_);
lean_ctor_set_uint8(v___x_491_, 3, v___x_490_);
v___x_492_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_489_, v___x_491_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_492_);
v___x_494_ = v___x_485_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_a_483_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v_a_497_; lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_a_476_);
v_a_497_ = lean_ctor_get(v___x_481_, 0);
v_a_498_ = lean_ctor_get(v___x_481_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_481_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_inc(v_a_497_);
lean_dec(v___x_481_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_497_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
else
{
lean_dec(v_x_466_);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSpecializeAttr___boxed(lean_object* v_x_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Fmt_fmtSpecializeAttr(v_x_506_, v_a_507_, v_a_508_);
lean_dec_ref(v_a_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1(){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_516_ = l_Lean_Fmt_fmtAttribute;
v___x_517_ = ((lean_object*)(l_Lean_Fmt_fmtSpecializeAttr___closed__1));
v___x_518_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___closed__1));
v___x_519_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSpecializeAttr___boxed), 3, 0);
v___x_520_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_516_, v___x_517_, v___x_518_, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1___boxed(lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1();
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExternEntry(lean_object* v_x_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v___x_535_; uint8_t v___x_536_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_568_; lean_object* v_inlineTk_x3f_569_; lean_object* v___y_570_; lean_object* v___y_571_; 
v___x_535_ = ((lean_object*)(l_Lean_Fmt_fmtExternEntry___closed__1));
lean_inc(v_x_532_);
v___x_536_ = l_Lean_Syntax_isOfKind(v_x_532_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_x_532_);
v___x_587_ = l_Lean_Fmt_Error_partialFormatter;
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_a_534_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v_id_x3f_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_603_ = l_Lean_Syntax_getArg(v_x_532_, v___x_589_);
v___x_604_ = l_Lean_Syntax_isNone(v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_603_);
v___x_606_ = l_Lean_Syntax_matchesNull(v___x_603_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v___x_603_);
lean_dec(v_x_532_);
v___x_607_ = l_Lean_Fmt_Error_partialFormatter;
v___x_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_a_534_);
return v___x_608_;
}
else
{
lean_object* v_id_x3f_609_; lean_object* v___x_610_; 
v_id_x3f_609_ = l_Lean_Syntax_getArg(v___x_603_, v___x_589_);
lean_dec(v___x_603_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v_id_x3f_609_);
v_id_x3f_591_ = v___x_610_;
v___y_592_ = v_a_533_;
v___y_593_ = v_a_534_;
goto v___jp_590_;
}
}
else
{
lean_object* v___x_611_; 
lean_dec(v___x_603_);
v___x_611_ = lean_box(0);
v_id_x3f_591_ = v___x_611_;
v___y_592_ = v_a_533_;
v___y_593_ = v_a_534_;
goto v___jp_590_;
}
v___jp_590_:
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = l_Lean_Syntax_getArg(v_x_532_, v___x_594_);
v___x_596_ = l_Lean_Syntax_isNone(v___x_595_);
if (v___x_596_ == 0)
{
uint8_t v___x_597_; 
lean_inc(v___x_595_);
v___x_597_ = l_Lean_Syntax_matchesNull(v___x_595_, v___x_594_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v___x_595_);
lean_dec(v_id_x3f_591_);
lean_dec(v_x_532_);
v___x_598_ = l_Lean_Fmt_Error_partialFormatter;
v___x_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___y_593_);
return v___x_599_;
}
else
{
lean_object* v_inlineTk_x3f_600_; lean_object* v___x_601_; 
v_inlineTk_x3f_600_ = l_Lean_Syntax_getArg(v___x_595_, v___x_589_);
lean_dec(v___x_595_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_inlineTk_x3f_600_);
v___y_568_ = v_id_x3f_591_;
v_inlineTk_x3f_569_ = v___x_601_;
v___y_570_ = v___y_592_;
v___y_571_ = v___y_593_;
goto v___jp_567_;
}
}
else
{
lean_object* v___x_602_; 
lean_dec(v___x_595_);
v___x_602_ = lean_box(0);
v___y_568_ = v_id_x3f_591_;
v_inlineTk_x3f_569_ = v___x_602_;
v___y_570_ = v___y_592_;
v___y_571_ = v___y_593_;
goto v___jp_567_;
}
}
}
v___jp_537_:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Fmt_fmt_x3f(v___y_542_, v___y_541_, v___y_540_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v_a_545_; lean_object* v___x_546_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
v_a_545_ = lean_ctor_get(v___x_543_, 1);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_543_, 2);
v___x_546_ = l_Lean_Fmt_fmt_x3f(v___y_538_, v___y_541_, v_a_545_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v_a_548_; lean_object* v___x_549_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
v_a_548_ = lean_ctor_get(v___x_546_, 1);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_546_, 2);
v___x_549_ = l_Lean_Fmt_fmt(v___y_539_, v___y_541_, v_a_548_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_566_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_a_551_ = lean_ctor_get(v___x_549_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_566_ == 0)
{
v___x_553_ = v___x_549_;
v_isShared_554_ = v_isSharedCheck_566_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_566_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_555_ = lean_unsigned_to_nat(3u);
v___x_556_ = lean_mk_empty_array_with_capacity(v___x_555_);
v___x_557_ = lean_array_push(v___x_556_, v_a_544_);
v___x_558_ = lean_array_push(v___x_557_, v_a_547_);
v___x_559_ = lean_array_push(v___x_558_, v_a_550_);
v___x_560_ = 0;
v___x_561_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_561_, 0, v___x_536_);
lean_ctor_set_uint8(v___x_561_, 1, v___x_560_);
lean_ctor_set_uint8(v___x_561_, 2, v___x_560_);
lean_ctor_set_uint8(v___x_561_, 3, v___x_560_);
v___x_562_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_559_, v___x_561_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_562_);
v___x_564_ = v___x_553_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_a_551_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
else
{
lean_dec(v_a_547_);
lean_dec(v_a_544_);
return v___x_549_;
}
}
else
{
lean_dec(v_a_544_);
lean_dec(v___y_539_);
return v___x_546_;
}
}
else
{
lean_dec(v___y_539_);
lean_dec(v___y_538_);
return v___x_543_;
}
}
v___jp_567_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_572_ = lean_unsigned_to_nat(2u);
v___x_573_ = l_Lean_Syntax_getArg(v_x_532_, v___x_572_);
lean_dec(v_x_532_);
v___x_574_ = ((lean_object*)(l_Lean_Fmt_fmtExternEntry___closed__3));
lean_inc(v___x_573_);
v___x_575_ = l_Lean_Syntax_isOfKind(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v___x_573_);
lean_dec(v_inlineTk_x3f_569_);
lean_dec(v___y_568_);
v___x_576_ = l_Lean_Fmt_Error_partialFormatter;
v___x_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___y_571_);
return v___x_577_;
}
else
{
if (lean_obj_tag(v___y_568_) == 0)
{
lean_object* v___x_578_; 
v___x_578_ = lean_box(0);
v___y_538_ = v_inlineTk_x3f_569_;
v___y_539_ = v___x_573_;
v___y_540_ = v___y_571_;
v___y_541_ = v___y_570_;
v___y_542_ = v___x_578_;
goto v___jp_537_;
}
else
{
lean_object* v_val_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
v_val_579_ = lean_ctor_get(v___y_568_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___y_568_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___y_568_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_val_579_);
lean_dec(v___y_568_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_val_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v___y_538_ = v_inlineTk_x3f_569_;
v___y_539_ = v___x_573_;
v___y_540_ = v___y_571_;
v___y_541_ = v___y_570_;
v___y_542_ = v___x_584_;
goto v___jp_537_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExternEntry___boxed(lean_object* v_x_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Fmt_fmtExternEntry(v_x_612_, v_a_613_, v_a_614_);
lean_dec_ref(v_a_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1(){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_622_ = l_Lean_Fmt_fmtAttribute;
v___x_623_ = ((lean_object*)(l_Lean_Fmt_fmtExternEntry___closed__1));
v___x_624_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___closed__1));
v___x_625_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExternEntry___boxed), 3, 0);
v___x_626_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_622_, v___x_623_, v___x_624_, v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1___boxed(lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1();
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExternAttr(lean_object* v_x_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = ((lean_object*)(l_Lean_Fmt_fmtExternAttr___closed__1));
lean_inc(v_x_635_);
v___x_639_ = l_Lean_Syntax_isOfKind(v_x_635_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v_x_635_);
v___x_640_ = l_Lean_Fmt_Error_partialFormatter;
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v_a_637_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v_externTk_643_; lean_object* v___x_644_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v_externTk_643_ = l_Lean_Syntax_getArg(v_x_635_, v___x_642_);
v___x_644_ = l_Lean_Fmt_fmt(v_externTk_643_, v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v_a_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_entries_649_; lean_object* v___x_650_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
v_a_646_ = lean_ctor_get(v___x_644_, 1);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_644_, 2);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = l_Lean_Syntax_getArg(v_x_635_, v___x_647_);
lean_dec(v_x_635_);
v_entries_649_ = l_Lean_Syntax_getArgs(v___x_648_);
lean_dec(v___x_648_);
v___x_650_ = l_Lean_Fmt_fmtArray___redArg(v_entries_649_, v_a_636_, v_a_646_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_665_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_a_652_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_665_ == 0)
{
v___x_654_ = v___x_650_;
v_isShared_655_ = v_isSharedCheck_665_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_665_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_656_ = lean_mk_empty_array_with_capacity(v___x_647_);
v___x_657_ = lean_array_push(v___x_656_, v_a_645_);
v___x_658_ = l_Array_append___redArg(v___x_657_, v_a_651_);
lean_dec(v_a_651_);
v___x_659_ = 0;
v___x_660_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_660_, 0, v___x_639_);
lean_ctor_set_uint8(v___x_660_, 1, v___x_659_);
lean_ctor_set_uint8(v___x_660_, 2, v___x_659_);
lean_ctor_set_uint8(v___x_660_, 3, v___x_659_);
v___x_661_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_658_, v___x_660_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_661_);
v___x_663_ = v___x_654_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_a_652_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec(v_a_645_);
v_a_666_ = lean_ctor_get(v___x_650_, 0);
v_a_667_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_650_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_inc(v_a_666_);
lean_dec(v___x_650_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_666_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_dec(v_x_635_);
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtExternAttr___boxed(lean_object* v_x_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Fmt_fmtExternAttr(v_x_675_, v_a_676_, v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1(){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_685_ = l_Lean_Fmt_fmtAttribute;
v___x_686_ = ((lean_object*)(l_Lean_Fmt_fmtExternAttr___closed__1));
v___x_687_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___closed__1));
v___x_688_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtExternAttr___boxed), 3, 0);
v___x_689_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_685_, v___x_686_, v___x_687_, v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1___boxed(lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1();
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticAltAttr(lean_object* v_x_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_Fmt_fmtTacticAltAttr___closed__1));
lean_inc(v_x_698_);
v___x_702_ = l_Lean_Syntax_isOfKind(v_x_698_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v_x_698_);
v___x_703_ = l_Lean_Fmt_Error_partialFormatter;
v___x_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_a_700_);
return v___x_704_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = l_Lean_Syntax_getArg(v_x_698_, v___x_705_);
v___x_707_ = ((lean_object*)(l_Lean_Fmt_fmtSimpleAttr___closed__6));
lean_inc(v___x_706_);
v___x_708_ = l_Lean_Syntax_isOfKind(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec(v___x_706_);
lean_dec(v_x_698_);
v___x_709_ = l_Lean_Fmt_Error_partialFormatter;
v___x_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v_a_700_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v_tacticAltTk_712_; lean_object* v___x_713_; 
v___x_711_ = lean_unsigned_to_nat(0u);
v_tacticAltTk_712_ = l_Lean_Syntax_getArg(v_x_698_, v___x_711_);
lean_dec(v_x_698_);
v___x_713_ = l_Lean_Fmt_fmt(v_tacticAltTk_712_, v_a_699_, v_a_700_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v_a_715_; lean_object* v___x_716_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
v_a_715_ = lean_ctor_get(v___x_713_, 1);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_713_, 2);
v___x_716_ = l_Lean_Fmt_fmt(v___x_706_, v_a_699_, v_a_715_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_732_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_a_718_ = lean_ctor_get(v___x_716_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_732_ == 0)
{
v___x_720_ = v___x_716_;
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_722_ = lean_unsigned_to_nat(2u);
v___x_723_ = lean_mk_empty_array_with_capacity(v___x_722_);
v___x_724_ = lean_array_push(v___x_723_, v_a_714_);
v___x_725_ = lean_array_push(v___x_724_, v_a_717_);
v___x_726_ = 0;
v___x_727_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_727_, 0, v___x_708_);
lean_ctor_set_uint8(v___x_727_, 1, v___x_726_);
lean_ctor_set_uint8(v___x_727_, 2, v___x_726_);
lean_ctor_set_uint8(v___x_727_, 3, v___x_726_);
v___x_728_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_725_, v___x_727_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_728_);
v___x_730_ = v___x_720_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_a_718_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_dec(v_a_714_);
return v___x_716_;
}
}
else
{
lean_dec(v___x_706_);
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticAltAttr___boxed(lean_object* v_x_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Fmt_fmtTacticAltAttr(v_x_733_, v_a_734_, v_a_735_);
lean_dec_ref(v_a_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1(){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_743_ = l_Lean_Fmt_fmtAttribute;
v___x_744_ = ((lean_object*)(l_Lean_Fmt_fmtTacticAltAttr___closed__1));
v___x_745_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___closed__1));
v___x_746_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticAltAttr___boxed), 3, 0);
v___x_747_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_743_, v___x_744_, v___x_745_, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1___boxed(lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1();
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticTagAttr(lean_object* v_x_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_Fmt_fmtTacticTagAttr___closed__1));
lean_inc(v_x_756_);
v___x_760_ = l_Lean_Syntax_isOfKind(v_x_756_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec(v_x_756_);
v___x_761_ = l_Lean_Fmt_Error_partialFormatter;
v___x_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v_a_758_);
return v___x_762_;
}
else
{
lean_object* v___x_763_; lean_object* v_tacticTagTk_764_; lean_object* v___x_765_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v_tacticTagTk_764_ = l_Lean_Syntax_getArg(v_x_756_, v___x_763_);
v___x_765_ = l_Lean_Fmt_fmt(v_tacticTagTk_764_, v_a_757_, v_a_758_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v_ids_770_; lean_object* v___x_771_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
v_a_767_ = lean_ctor_get(v___x_765_, 1);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_765_, 2);
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = l_Lean_Syntax_getArg(v_x_756_, v___x_768_);
lean_dec(v_x_756_);
v_ids_770_ = l_Lean_Syntax_getArgs(v___x_769_);
lean_dec(v___x_769_);
v___x_771_ = l_Lean_Fmt_fmtArray___redArg(v_ids_770_, v_a_757_, v_a_767_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_786_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_a_773_ = lean_ctor_get(v___x_771_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_786_ == 0)
{
v___x_775_ = v___x_771_;
v_isShared_776_ = v_isSharedCheck_786_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_786_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_777_ = lean_mk_empty_array_with_capacity(v___x_768_);
v___x_778_ = lean_array_push(v___x_777_, v_a_766_);
v___x_779_ = l_Array_append___redArg(v___x_778_, v_a_772_);
lean_dec(v_a_772_);
v___x_780_ = 0;
v___x_781_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_781_, 0, v___x_760_);
lean_ctor_set_uint8(v___x_781_, 1, v___x_780_);
lean_ctor_set_uint8(v___x_781_, 2, v___x_780_);
lean_ctor_set_uint8(v___x_781_, 3, v___x_780_);
v___x_782_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_779_, v___x_781_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_782_);
v___x_784_ = v___x_775_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_a_773_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_787_; lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_a_766_);
v_a_787_ = lean_ctor_get(v___x_771_, 0);
v_a_788_ = lean_ctor_get(v___x_771_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_771_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_inc(v_a_787_);
lean_dec(v___x_771_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_787_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_dec(v_x_756_);
return v___x_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticTagAttr___boxed(lean_object* v_x_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Fmt_fmtTacticTagAttr(v_x_796_, v_a_797_, v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1(){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_806_ = l_Lean_Fmt_fmtAttribute;
v___x_807_ = ((lean_object*)(l_Lean_Fmt_fmtTacticTagAttr___closed__1));
v___x_808_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___closed__1));
v___x_809_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticTagAttr___boxed), 3, 0);
v___x_810_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_806_, v___x_807_, v___x_808_, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1___boxed(lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1();
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticNameAttr(lean_object* v_x_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = ((lean_object*)(l_Lean_Fmt_fmtTacticNameAttr___closed__1));
lean_inc(v_x_819_);
v___x_823_ = l_Lean_Syntax_isOfKind(v_x_819_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec(v_x_819_);
v___x_824_ = l_Lean_Fmt_Error_partialFormatter;
v___x_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v_a_821_);
return v___x_825_;
}
else
{
lean_object* v___x_826_; lean_object* v_tacticNameTk_827_; lean_object* v___x_828_; 
v___x_826_ = lean_unsigned_to_nat(0u);
v_tacticNameTk_827_ = l_Lean_Syntax_getArg(v_x_819_, v___x_826_);
v___x_828_ = l_Lean_Fmt_fmt(v_tacticNameTk_827_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v_a_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
v_a_830_ = lean_ctor_get(v___x_828_, 1);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_828_, 2);
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = l_Lean_Syntax_getArg(v_x_819_, v___x_831_);
lean_dec(v_x_819_);
v___x_833_ = l_Lean_Fmt_fmt(v___x_832_, v_a_820_, v_a_830_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_849_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_a_835_ = lean_ctor_get(v___x_833_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_849_ == 0)
{
v___x_837_ = v___x_833_;
v_isShared_838_ = v_isSharedCheck_849_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_849_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_839_ = lean_unsigned_to_nat(2u);
v___x_840_ = lean_mk_empty_array_with_capacity(v___x_839_);
v___x_841_ = lean_array_push(v___x_840_, v_a_829_);
v___x_842_ = lean_array_push(v___x_841_, v_a_834_);
v___x_843_ = 0;
v___x_844_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_844_, 0, v___x_823_);
lean_ctor_set_uint8(v___x_844_, 1, v___x_843_);
lean_ctor_set_uint8(v___x_844_, 2, v___x_843_);
lean_ctor_set_uint8(v___x_844_, 3, v___x_843_);
v___x_845_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_842_, v___x_844_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_845_);
v___x_847_ = v___x_837_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_a_835_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_dec(v_a_829_);
return v___x_833_;
}
}
else
{
lean_dec(v_x_819_);
return v___x_828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTacticNameAttr___boxed(lean_object* v_x_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Fmt_fmtTacticNameAttr(v_x_850_, v_a_851_, v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1(){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_860_ = l_Lean_Fmt_fmtAttribute;
v___x_861_ = ((lean_object*)(l_Lean_Fmt_fmtTacticNameAttr___closed__1));
v___x_862_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___closed__1));
v___x_863_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTacticNameAttr___boxed), 3, 0);
v___x_864_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_860_, v___x_861_, v___x_862_, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1___boxed(lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1();
return v_res_866_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Attr(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSimpleAttr___regBuiltin_Lean_Fmt_fmtSimpleAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtMacroAttr___regBuiltin_Lean_Fmt_fmtMacroAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExportAttr___regBuiltin_Lean_Fmt_fmtExportAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtRecursorAttr___regBuiltin_Lean_Fmt_fmtRecursorAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtClassAttr___regBuiltin_Lean_Fmt_fmtClassAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtInstanceAttr___regBuiltin_Lean_Fmt_fmtInstanceAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtDefaultInstanceAttr___regBuiltin_Lean_Fmt_fmtDefaultInstanceAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtSpecializeAttr___regBuiltin_Lean_Fmt_fmtSpecializeAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternEntry___regBuiltin_Lean_Fmt_fmtExternEntry__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtExternAttr___regBuiltin_Lean_Fmt_fmtExternAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticAltAttr___regBuiltin_Lean_Fmt_fmtTacticAltAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticTagAttr___regBuiltin_Lean_Fmt_fmtTacticTagAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Attr_0__Lean_Fmt_fmtTacticNameAttr___regBuiltin_Lean_Fmt_fmtTacticNameAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Attr(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Attr(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Parser_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
