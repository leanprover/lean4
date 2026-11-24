// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Parser.Extra
// Imports: public import Lean.Parser.Extra public import Lean.Fmt.FmtM.Basic meta import Lean.Parser.Term meta import Lean.Parser.Extra import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHygieneInfo___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHygieneInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHygieneInfo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtHygieneInfo"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(81, 189, 38, 78, 229, 17, 48, 25)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__5 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHexnum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHexnum___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtAtomic___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtHexnum"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(94, 96, 113, 91, 33, 239, 127, 151)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRegisterParserAlias___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "termRegister_parser_alias(Kind:=_)______"};
static const lean_object* l_Lean_Fmt_fmtRegisterParserAlias___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterParserAlias___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterParserAlias___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 135, 36, 196, 99, 128, 246, 50)}};
static const lean_object* l_Lean_Fmt_fmtRegisterParserAlias___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterParserAlias___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtRegisterParserAlias___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterParserAlias___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtRegisterParserAlias___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterParserAlias___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Fmt_fmtRegisterParserAlias___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterParserAlias___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Fmt_fmtRegisterParserAlias___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterParserAlias___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Fmt_fmtRegisterParserAlias___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterParserAlias___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__6_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Fmt_fmtRegisterParserAlias___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtRegisterParserAlias___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterParserAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterParserAlias___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtRegisterParserAlias"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 227, 122, 147, 178, 224, 129, 58)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHygieneInfo___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v_a_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHygieneInfo(lean_object* v_x_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Fmt_fmtHygieneInfo___redArg(v_a_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHygieneInfo___boxed(lean_object* v_x_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Fmt_fmtHygieneInfo(v_x_8_, v_a_9_, v_a_10_);
lean_dec_ref(v_a_9_);
lean_dec(v_x_8_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1(){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_23_ = l_Lean_Fmt_fmtAttribute;
v___x_24_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__1));
v___x_25_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___closed__5));
v___x_26_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtHygieneInfo___boxed), 3, 0);
v___x_27_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_23_, v___x_24_, v___x_25_, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1___boxed(lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1();
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHexnum(lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Fmt_fmtAtomic(v_a_30_, v_a_31_, v_a_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHexnum___boxed(lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Fmt_fmtHexnum(v_a_34_, v_a_35_, v_a_36_);
lean_dec_ref(v_a_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1(){
_start:
{
lean_object* v___f_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___f_48_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__0));
v___x_49_ = l_Lean_Fmt_fmtAttribute;
v___x_50_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__2));
v___x_51_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___closed__4));
v___x_52_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_49_, v___x_50_, v___x_51_, v___f_48_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1___boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1();
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterParserAlias(lean_object* v_x_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_71_; uint8_t v___x_72_; lean_object* v___y_74_; lean_object* v___y_75_; lean_object* v___y_76_; lean_object* v___y_77_; lean_object* v___y_78_; lean_object* v___y_79_; lean_object* v___y_80_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_131_; lean_object* v___y_132_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___y_136_; lean_object* v___y_137_; lean_object* v___y_138_; lean_object* v___y_139_; lean_object* v___y_140_; lean_object* v___y_141_; 
v___x_71_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterParserAlias___closed__1));
lean_inc(v_x_68_);
v___x_72_ = l_Lean_Syntax_isOfKind(v_x_68_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v_x_68_);
v___x_156_ = l_Lean_Fmt_Error_partialFormatter;
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_70_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v_registerTk_159_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v_info_x3f_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___x_185_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v_aliasName_x3f_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v_lbTk_x3f_211_; lean_object* v_kindTk_x3f_212_; lean_object* v_colonEqTk_x3f_213_; lean_object* v_kind_x3f_214_; lean_object* v_rbTk_x3f_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v_registerTk_159_ = l_Lean_Syntax_getArg(v_x_68_, v___x_158_);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_231_ = l_Lean_Syntax_getArg(v_x_68_, v___x_185_);
v___x_232_ = l_Lean_Syntax_isNone(v___x_231_);
if (v___x_232_ == 0)
{
uint8_t v___x_233_; 
lean_inc(v___x_231_);
v___x_233_ = l_Lean_Syntax_matchesNull(v___x_231_, v___x_185_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v___x_231_);
lean_dec(v_registerTk_159_);
lean_dec(v_x_68_);
v___x_234_ = l_Lean_Fmt_Error_partialFormatter;
v___x_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v_a_70_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = l_Lean_Syntax_getArg(v___x_231_, v___x_158_);
lean_dec(v___x_231_);
v___x_237_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterParserAlias___closed__7));
lean_inc(v___x_236_);
v___x_238_ = l_Lean_Syntax_isOfKind(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec(v___x_236_);
lean_dec(v_registerTk_159_);
lean_dec(v_x_68_);
v___x_239_ = l_Lean_Fmt_Error_partialFormatter;
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v_a_70_);
return v___x_240_;
}
else
{
lean_object* v_lbTk_x3f_241_; lean_object* v_kindTk_x3f_242_; lean_object* v___x_243_; lean_object* v_colonEqTk_x3f_244_; lean_object* v___x_245_; lean_object* v_kind_x3f_246_; lean_object* v___x_247_; lean_object* v_rbTk_x3f_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_lbTk_x3f_241_ = l_Lean_Syntax_getArg(v___x_236_, v___x_158_);
v_kindTk_x3f_242_ = l_Lean_Syntax_getArg(v___x_236_, v___x_185_);
v___x_243_ = lean_unsigned_to_nat(2u);
v_colonEqTk_x3f_244_ = l_Lean_Syntax_getArg(v___x_236_, v___x_243_);
v___x_245_ = lean_unsigned_to_nat(3u);
v_kind_x3f_246_ = l_Lean_Syntax_getArg(v___x_236_, v___x_245_);
v___x_247_ = lean_unsigned_to_nat(4u);
v_rbTk_x3f_248_ = l_Lean_Syntax_getArg(v___x_236_, v___x_247_);
lean_dec(v___x_236_);
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v_lbTk_x3f_241_);
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v_kindTk_x3f_242_);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v_colonEqTk_x3f_244_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v_kind_x3f_246_);
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v_rbTk_x3f_248_);
v_lbTk_x3f_211_ = v___x_249_;
v_kindTk_x3f_212_ = v___x_250_;
v_colonEqTk_x3f_213_ = v___x_251_;
v_kind_x3f_214_ = v___x_252_;
v_rbTk_x3f_215_ = v___x_253_;
v___y_216_ = v_a_69_;
v___y_217_ = v_a_70_;
goto v___jp_210_;
}
}
}
else
{
lean_object* v___x_254_; 
lean_dec(v___x_231_);
v___x_254_ = lean_box(0);
v_lbTk_x3f_211_ = v___x_254_;
v_kindTk_x3f_212_ = v___x_254_;
v_colonEqTk_x3f_213_ = v___x_254_;
v_kind_x3f_214_ = v___x_254_;
v_rbTk_x3f_215_ = v___x_254_;
v___y_216_ = v_a_69_;
v___y_217_ = v_a_70_;
goto v___jp_210_;
}
v___jp_160_:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Fmt_fmt(v_registerTk_159_, v___y_169_, v___y_170_);
if (lean_obj_tag(v___x_171_) == 0)
{
if (lean_obj_tag(v___y_163_) == 0)
{
lean_object* v_a_172_; lean_object* v_a_173_; lean_object* v___x_174_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
v_a_173_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_171_, 2);
v___x_174_ = lean_box(0);
v___y_131_ = v___y_161_;
v___y_132_ = v___y_162_;
v___y_133_ = v_info_x3f_168_;
v___y_134_ = v_a_172_;
v___y_135_ = v_a_173_;
v___y_136_ = v___y_164_;
v___y_137_ = v___y_165_;
v___y_138_ = v___y_169_;
v___y_139_ = v___y_167_;
v___y_140_ = v___y_166_;
v___y_141_ = v___x_174_;
goto v___jp_130_;
}
else
{
lean_object* v_a_175_; lean_object* v_a_176_; lean_object* v_val_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_a_175_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_175_);
v_a_176_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_a_176_);
lean_dec_ref_known(v___x_171_, 2);
v_val_177_ = lean_ctor_get(v___y_163_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___y_163_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___y_163_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_val_177_);
lean_dec(v___y_163_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_val_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
v___y_131_ = v___y_161_;
v___y_132_ = v___y_162_;
v___y_133_ = v_info_x3f_168_;
v___y_134_ = v_a_175_;
v___y_135_ = v_a_176_;
v___y_136_ = v___y_164_;
v___y_137_ = v___y_165_;
v___y_138_ = v___y_169_;
v___y_139_ = v___y_167_;
v___y_140_ = v___y_166_;
v___y_141_ = v___x_182_;
goto v___jp_130_;
}
}
}
}
else
{
lean_dec(v_info_x3f_168_);
lean_dec(v___y_167_);
lean_dec(v___y_166_);
lean_dec(v___y_165_);
lean_dec(v___y_164_);
lean_dec(v___y_163_);
lean_dec(v___y_162_);
lean_dec(v___y_161_);
return v___x_171_;
}
}
v___jp_186_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_195_ = lean_unsigned_to_nat(3u);
v___x_196_ = l_Lean_Syntax_getArg(v_x_68_, v___x_195_);
v___x_197_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterParserAlias___closed__3));
lean_inc(v___x_196_);
v___x_198_ = l_Lean_Syntax_isOfKind(v___x_196_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v___x_196_);
lean_dec(v_aliasName_x3f_192_);
lean_dec(v___y_191_);
lean_dec(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec(v___y_187_);
lean_dec(v_registerTk_159_);
lean_dec(v_x_68_);
v___x_199_ = l_Lean_Fmt_Error_partialFormatter;
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___y_194_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_201_ = lean_unsigned_to_nat(4u);
v___x_202_ = l_Lean_Syntax_getArg(v_x_68_, v___x_201_);
lean_dec(v_x_68_);
v___x_203_ = l_Lean_Syntax_isNone(v___x_202_);
if (v___x_203_ == 0)
{
uint8_t v___x_204_; 
lean_inc(v___x_202_);
v___x_204_ = l_Lean_Syntax_matchesNull(v___x_202_, v___x_185_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v___x_202_);
lean_dec(v___x_196_);
lean_dec(v_aliasName_x3f_192_);
lean_dec(v___y_191_);
lean_dec(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec(v___y_187_);
lean_dec(v_registerTk_159_);
v___x_205_ = l_Lean_Fmt_Error_partialFormatter;
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___y_194_);
return v___x_206_;
}
else
{
lean_object* v_info_x3f_207_; lean_object* v___x_208_; 
v_info_x3f_207_ = l_Lean_Syntax_getArg(v___x_202_, v___x_158_);
lean_dec(v___x_202_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v_info_x3f_207_);
v___y_161_ = v___y_187_;
v___y_162_ = v_aliasName_x3f_192_;
v___y_163_ = v___y_188_;
v___y_164_ = v___y_189_;
v___y_165_ = v___x_196_;
v___y_166_ = v___y_191_;
v___y_167_ = v___y_190_;
v_info_x3f_168_ = v___x_208_;
v___y_169_ = v___y_193_;
v___y_170_ = v___y_194_;
goto v___jp_160_;
}
}
else
{
lean_object* v___x_209_; 
lean_dec(v___x_202_);
v___x_209_ = lean_box(0);
v___y_161_ = v___y_187_;
v___y_162_ = v_aliasName_x3f_192_;
v___y_163_ = v___y_188_;
v___y_164_ = v___y_189_;
v___y_165_ = v___x_196_;
v___y_166_ = v___y_191_;
v___y_167_ = v___y_190_;
v_info_x3f_168_ = v___x_209_;
v___y_169_ = v___y_193_;
v___y_170_ = v___y_194_;
goto v___jp_160_;
}
}
}
v___jp_210_:
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = l_Lean_Syntax_getArg(v_x_68_, v___x_218_);
v___x_220_ = l_Lean_Syntax_isNone(v___x_219_);
if (v___x_220_ == 0)
{
uint8_t v___x_221_; 
lean_inc(v___x_219_);
v___x_221_ = l_Lean_Syntax_matchesNull(v___x_219_, v___x_185_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec(v___x_219_);
lean_dec(v_rbTk_x3f_215_);
lean_dec(v_kind_x3f_214_);
lean_dec(v_colonEqTk_x3f_213_);
lean_dec(v_kindTk_x3f_212_);
lean_dec(v_lbTk_x3f_211_);
lean_dec(v_registerTk_159_);
lean_dec(v_x_68_);
v___x_222_ = l_Lean_Fmt_Error_partialFormatter;
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___y_217_);
return v___x_223_;
}
else
{
lean_object* v_aliasName_x3f_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_aliasName_x3f_224_ = l_Lean_Syntax_getArg(v___x_219_, v___x_158_);
lean_dec(v___x_219_);
v___x_225_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterParserAlias___closed__5));
lean_inc(v_aliasName_x3f_224_);
v___x_226_ = l_Lean_Syntax_isOfKind(v_aliasName_x3f_224_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec(v_aliasName_x3f_224_);
lean_dec(v_rbTk_x3f_215_);
lean_dec(v_kind_x3f_214_);
lean_dec(v_colonEqTk_x3f_213_);
lean_dec(v_kindTk_x3f_212_);
lean_dec(v_lbTk_x3f_211_);
lean_dec(v_registerTk_159_);
lean_dec(v_x_68_);
v___x_227_ = l_Lean_Fmt_Error_partialFormatter;
v___x_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___y_217_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v_aliasName_x3f_224_);
v___y_187_ = v_kindTk_x3f_212_;
v___y_188_ = v_kind_x3f_214_;
v___y_189_ = v_lbTk_x3f_211_;
v___y_190_ = v_rbTk_x3f_215_;
v___y_191_ = v_colonEqTk_x3f_213_;
v_aliasName_x3f_192_ = v___x_229_;
v___y_193_ = v___y_216_;
v___y_194_ = v___y_217_;
goto v___jp_186_;
}
}
}
else
{
lean_object* v___x_230_; 
lean_dec(v___x_219_);
v___x_230_ = lean_box(0);
v___y_187_ = v_kindTk_x3f_212_;
v___y_188_ = v_kind_x3f_214_;
v___y_189_ = v_lbTk_x3f_211_;
v___y_190_ = v_rbTk_x3f_215_;
v___y_191_ = v_colonEqTk_x3f_213_;
v_aliasName_x3f_192_ = v___x_230_;
v___y_193_ = v___y_216_;
v___y_194_ = v___y_217_;
goto v___jp_186_;
}
}
}
v___jp_73_:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Fmt_fmt_x3f(v___y_80_, v___y_78_, v___y_79_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_104_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
v_a_83_ = lean_ctor_get(v___x_81_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_104_ == 0)
{
v___x_85_ = v___x_81_;
v_isShared_86_ = v_isSharedCheck_104_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_inc(v_a_82_);
lean_dec(v___x_81_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_104_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_87_ = lean_unsigned_to_nat(2u);
v___x_88_ = lean_mk_empty_array_with_capacity(v___x_87_);
v___x_89_ = lean_array_push(v___x_88_, v___y_77_);
v___x_90_ = lean_array_push(v___x_89_, v___y_76_);
v___x_91_ = 0;
v___x_92_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_92_, 0, v___x_72_);
lean_ctor_set_uint8(v___x_92_, 1, v___x_91_);
lean_ctor_set_uint8(v___x_92_, 2, v___x_91_);
lean_ctor_set_uint8(v___x_92_, 3, v___x_91_);
lean_inc_ref(v___x_92_);
v___x_93_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_90_, v___x_92_);
v___x_94_ = lean_unsigned_to_nat(4u);
v___x_95_ = lean_mk_empty_array_with_capacity(v___x_94_);
v___x_96_ = lean_array_push(v___x_95_, v___x_93_);
v___x_97_ = lean_array_push(v___x_96_, v___y_74_);
v___x_98_ = lean_array_push(v___x_97_, v___y_75_);
v___x_99_ = lean_array_push(v___x_98_, v_a_82_);
v___x_100_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_99_, v___x_92_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_100_);
v___x_102_ = v___x_85_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_a_83_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
lean_dec_ref(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec_ref(v___y_74_);
return v___x_81_;
}
}
v___jp_105_:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Fmt_fmt_x3f(v___y_112_, v___y_111_, v___y_109_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v_a_115_; lean_object* v___x_116_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
v_a_115_ = lean_ctor_get(v___x_113_, 1);
lean_inc(v_a_115_);
lean_dec_ref_known(v___x_113_, 2);
v___x_116_ = l_Lean_Fmt_fmt(v___y_110_, v___y_111_, v_a_115_);
if (lean_obj_tag(v___x_116_) == 0)
{
if (lean_obj_tag(v___y_107_) == 0)
{
lean_object* v_a_117_; lean_object* v_a_118_; lean_object* v___x_119_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
v_a_118_ = lean_ctor_get(v___x_116_, 1);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_116_, 2);
v___x_119_ = lean_box(0);
v___y_74_ = v_a_114_;
v___y_75_ = v_a_117_;
v___y_76_ = v___y_106_;
v___y_77_ = v___y_108_;
v___y_78_ = v___y_111_;
v___y_79_ = v_a_118_;
v___y_80_ = v___x_119_;
goto v___jp_73_;
}
else
{
lean_object* v_a_120_; lean_object* v_a_121_; lean_object* v_val_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_a_120_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_120_);
v_a_121_ = lean_ctor_get(v___x_116_, 1);
lean_inc(v_a_121_);
lean_dec_ref_known(v___x_116_, 2);
v_val_122_ = lean_ctor_get(v___y_107_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___y_107_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___y_107_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_val_122_);
lean_dec(v___y_107_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_val_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
v___y_74_ = v_a_114_;
v___y_75_ = v_a_120_;
v___y_76_ = v___y_106_;
v___y_77_ = v___y_108_;
v___y_78_ = v___y_111_;
v___y_79_ = v_a_121_;
v___y_80_ = v___x_127_;
goto v___jp_73_;
}
}
}
}
else
{
lean_dec(v_a_114_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v___x_116_;
}
}
else
{
lean_dec(v___y_110_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v___x_113_;
}
}
v___jp_130_:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v___y_136_, v___y_131_, v___y_140_, v___y_141_, v___y_139_, v___y_138_, v___y_135_);
if (lean_obj_tag(v___x_142_) == 0)
{
if (lean_obj_tag(v___y_132_) == 0)
{
lean_object* v_a_143_; lean_object* v_a_144_; lean_object* v___x_145_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
v_a_144_ = lean_ctor_get(v___x_142_, 1);
lean_inc(v_a_144_);
lean_dec_ref_known(v___x_142_, 2);
v___x_145_ = lean_box(0);
v___y_106_ = v_a_143_;
v___y_107_ = v___y_133_;
v___y_108_ = v___y_134_;
v___y_109_ = v_a_144_;
v___y_110_ = v___y_137_;
v___y_111_ = v___y_138_;
v___y_112_ = v___x_145_;
goto v___jp_105_;
}
else
{
lean_object* v_a_146_; lean_object* v_a_147_; lean_object* v_val_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_a_146_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_146_);
v_a_147_ = lean_ctor_get(v___x_142_, 1);
lean_inc(v_a_147_);
lean_dec_ref_known(v___x_142_, 2);
v_val_148_ = lean_ctor_get(v___y_132_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___y_132_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___y_132_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_val_148_);
lean_dec(v___y_132_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_val_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
v___y_106_ = v_a_146_;
v___y_107_ = v___y_133_;
v___y_108_ = v___y_134_;
v___y_109_ = v_a_147_;
v___y_110_ = v___y_137_;
v___y_111_ = v___y_138_;
v___y_112_ = v___x_153_;
goto v___jp_105_;
}
}
}
}
else
{
lean_dec(v___y_137_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec(v___y_132_);
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterParserAlias___boxed(lean_object* v_x_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Fmt_fmtRegisterParserAlias(v_x_255_, v_a_256_, v_a_257_);
lean_dec_ref(v_a_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1(){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_265_ = l_Lean_Fmt_fmtAttribute;
v___x_266_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterParserAlias___closed__1));
v___x_267_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___closed__1));
v___x_268_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRegisterParserAlias___boxed), 3, 0);
v___x_269_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_265_, v___x_266_, v___x_267_, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1___boxed(lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1();
return v_res_271_;
}
}
lean_object* runtime_initialize_Lean_Parser_Extra(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Extra(builtin);
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
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHygieneInfo___regBuiltin_Lean_Fmt_fmtHygieneInfo__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtHexnum___regBuiltin_Lean_Fmt_fmtHexnum__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Extra_0__Lean_Fmt_fmtRegisterParserAlias___regBuiltin_Lean_Fmt_fmtRegisterParserAlias__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Extra(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Extra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Extra(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Extra(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Parser_Extra(builtin);
}
#ifdef __cplusplus
}
#endif
