// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Parser.Syntax
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Parser.Syntax import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtRaw(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_fill(lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator(lean_object*);
lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_metaDeclarationSignature___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_metaDeclarationSignature___closed__0 = (const lean_object*)&l_Lean_Fmt_metaDeclarationSignature___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_metaDeclarationSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_metaDeclarationSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaDeclarationSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaDeclarationSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtElabDeclarationSignature___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtElabDeclarationSignature___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtElabDeclarationSignature___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabDeclarationSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabDeclarationSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaAssignmentDeclaration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaAssignmentDeclaration___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaMatchDeclaration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaMatchDeclaration___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtPrecedence___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtPrecedence___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtPrecedence___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtPrecedence___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtPrecedence___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "precedence"};
static const lean_object* l_Lean_Fmt_fmtPrecedence___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtPrecedence___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtPrecedence___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtPrecedence___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 243, 176, 51, 48, 112, 202, 160)}};
static const lean_object* l_Lean_Fmt_fmtPrecedence___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrecedence(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrecedence___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtPrecedence"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 15, 214, 223, 182, 48, 73, 41)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntaxParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Fmt_fmtSyntaxParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtSyntaxParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Fmt_fmtSyntaxParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxParen___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxParen___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxParen___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxParen___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 185, 174, 62, 133, 84, 210, 196)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxParen___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtSyntaxParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 27, 88, 200, 142, 51, 239, 59)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntaxCat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cat"};
static const lean_object* l_Lean_Fmt_fmtSyntaxCat___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxCat___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxCat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxCat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxCat___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxCat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxCat___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxCat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxCat___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntaxCat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 91, 11, 245, 227, 176, 7, 196)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxCat___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxCat___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSyntaxCat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtSyntaxCat___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxCat___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxCat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSyntaxCat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxCat___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxCat___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxCat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxCat___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtSyntaxCat"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 146, 7, 153, 68, 83, 115, 140)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntaxUnary___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unary"};
static const lean_object* l_Lean_Fmt_fmtSyntaxUnary___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxUnary___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxUnary___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxUnary___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxUnary___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxUnary___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxUnary___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxUnary___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxUnary___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntaxUnary___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 77, 42, 108, 13, 102, 39, 65)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxUnary___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxUnary___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxUnary(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxUnary___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtSyntaxUnary"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 18, 180, 18, 120, 53, 78, 108)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntaxBinary___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binary"};
static const lean_object* l_Lean_Fmt_fmtSyntaxBinary___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxBinary___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxBinary___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxBinary___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxBinary___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxBinary___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxBinary___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxBinary___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxBinary___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntaxBinary___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 183, 160, 219, 133, 108, 161)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxBinary___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxBinary___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxBinary(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxBinary___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtSyntaxBinary"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 249, 109, 0, 84, 77, 41, 6)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntaxSepBy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l_Lean_Fmt_fmtSyntaxSepBy___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxSepBy___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxSepBy___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxSepBy___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxSepBy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 96, 22, 193, 32, 12, 216, 27)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxSepBy___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtSyntaxSepBy___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Fmt_fmtSyntaxSepBy___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxSepBy___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxSepBy___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy___closed__3_value;
static const lean_array_object l_Lean_Fmt_fmtSyntaxSepBy___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtSyntaxSepBy___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxSepBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxSepBy___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtSyntaxSepBy"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 1, 229, 191, 186, 10, 131, 249)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntaxSepBy1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sepBy1"};
static const lean_object* l_Lean_Fmt_fmtSyntaxSepBy1___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy1___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxSepBy1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxSepBy1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxSepBy1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxSepBy1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy1___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 224, 0, 238, 204, 234, 239, 47)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxSepBy1___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxSepBy1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxSepBy1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxSepBy1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtSyntaxSepBy1"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 156, 242, 166, 137, 90, 192, 160)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntaxAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "atom"};
static const lean_object* l_Lean_Fmt_fmtSyntaxAtom___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxAtom___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxAtom___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxAtom___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxAtom___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxAtom___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxAtom___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxAtom___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntaxAtom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 22, 146, 169, 39, 242, 124, 88)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxAtom___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxAtom___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxAtom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxAtom___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtSyntaxAtom"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 67, 72, 113, 80, 154, 141, 24)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntaxNonReserved___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nonReserved"};
static const lean_object* l_Lean_Fmt_fmtSyntaxNonReserved___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxNonReserved___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxNonReserved___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxNonReserved___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxNonReserved___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxNonReserved___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxNonReserved___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxNonReserved___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxNonReserved___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntaxNonReserved___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 78, 166, 169, 121, 44, 215, 226)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxNonReserved___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxNonReserved___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxNonReserved(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxNonReserved___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtSyntaxNonReserved"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 173, 35, 189, 128, 182, 11, 195)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unicodeAtom"};
static const lean_object* l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSyntaxParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 147, 94, 13, 45, 35, 101, 109)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxUnicodeAtom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxUnicodeAtom___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtSyntaxUnicodeAtom"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 153, 2, 217, 218, 244, 223, 36)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtNamedName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtNamedName___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtNamedName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Fmt_fmtNamedName___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtNamedName___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtNamedName___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtNamedName___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtNamedName___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtNamedName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Fmt_fmtNamedName___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtNamedName___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNamedName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNamedName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtNamedName"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 179, 82, 225, 23, 128, 11, 198)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtIdentPrec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "identPrec"};
static const lean_object* l_Lean_Fmt_fmtIdentPrec___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtIdentPrec___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtIdentPrec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtIdentPrec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIdentPrec___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtIdentPrec___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIdentPrec___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtIdentPrec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIdentPrec___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtIdentPrec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 25, 252, 182, 120, 175, 78, 126)}};
static const lean_object* l_Lean_Fmt_fmtIdentPrec___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtIdentPrec___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIdentPrec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIdentPrec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtIdentPrec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 0, 26, 9, 137, 88, 226, 9)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefix___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtAtomic___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "prefix"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 255, 86, 177, 195, 168, 212, 163)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtPrefix"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 63, 120, 93, 230, 89, 211)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfix___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "infix"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 202, 116, 85, 196, 237, 101, 141)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtInfix"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(193, 25, 53, 210, 95, 146, 85, 160)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "infixl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 176, 144, 146, 48, 231, 100, 173)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtInfixl"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 44, 223, 156, 80, 167, 49, 242)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "infixr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 7, 27, 92, 157, 7, 198, 225)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtInfixr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(119, 83, 10, 89, 92, 26, 58, 43)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfix___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "postfix"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 175, 134, 52, 144, 48, 141, 10)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtPostfix"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(35, 250, 105, 247, 114, 253, 118, 181)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMixfix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mixfix"};
static const lean_object* l_Lean_Fmt_fmtMixfix___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMixfix___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 31, 80, 86, 44, 46, 155, 0)}};
static const lean_object* l_Lean_Fmt_fmtMixfix___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMixfix___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtMixfix___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Fmt_fmtMixfix___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtMixfix___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__2_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Fmt_fmtMixfix___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtMixfix___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtMixfix___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtMixfix___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtMixfix___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtMixfix___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Fmt_fmtMixfix___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtMixfix___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Fmt_fmtMixfix___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtMixfix___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtMixfix___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Fmt_fmtMixfix___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtMixfix___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__8_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__8_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__8_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__7_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Fmt_fmtMixfix___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtMixfix___closed__8_value;
static const lean_string_object l_Lean_Fmt_fmtMixfix___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtMixfix___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtMixfix___closed__9_value;
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__10_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__10_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtMixfix___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__10_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMixfix___closed__9_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtMixfix___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtMixfix___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMixfix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMixfix___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtMixfix"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 16, 196, 152, 44, 248, 57, 155)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtNotation_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtNotation_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtNotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notation"};
static const lean_object* l_Lean_Fmt_fmtNotation___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtNotation___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtNotation___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtNotation___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtNotation___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtNotation___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtNotation___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtNotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtNotation___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtNotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 34, 53, 7, 182, 20, 8, 182)}};
static const lean_object* l_Lean_Fmt_fmtNotation___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtNotation___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNotation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNotation___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtNotation"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 181, 137, 50, 5, 216, 181, 166)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMacroRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Fmt_fmtMacroRules___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMacroRules___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtMacroRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "macro_rules"};
static const lean_object* l_Lean_Fmt_fmtMacroRules___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMacroRules___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtMacroRules___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroRules___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroRules___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroRules___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroRules___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroRules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroRules___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMacroRules___closed__1_value),LEAN_SCALAR_PTR_LITERAL(125, 80, 75, 5, 165, 87, 197, 1)}};
static const lean_object* l_Lean_Fmt_fmtMacroRules___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtMacroRules___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroRules(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroRules___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtMacroRules"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 113, 57, 40, 202, 156, 234, 208)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntaxCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Fmt_fmtSyntaxCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxCmd___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxCmd___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntaxCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxCmd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtSyntaxCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 164, 117, 93, 87, 117, 173, 228)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSyntaxAbbrev___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "syntaxAbbrev"};
static const lean_object* l_Lean_Fmt_fmtSyntaxAbbrev___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxAbbrev___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxAbbrev___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxAbbrev___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxAbbrev___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxAbbrev___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxAbbrev___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtSyntaxAbbrev___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSyntaxAbbrev___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtSyntaxAbbrev___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 194, 172, 134, 159, 244, 204, 250)}};
static const lean_object* l_Lean_Fmt_fmtSyntaxAbbrev___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSyntaxAbbrev___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxAbbrev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxAbbrev___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtSyntaxAbbrev"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 210, 113, 158, 70, 101, 25, 45)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCatBehaviorBoth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCatBehaviorBoth___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "catBehaviorBoth"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 183, 160, 167, 69, 135, 212, 9)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtCatBehaviorBoth"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(95, 64, 100, 156, 184, 88, 28, 238)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCatBehaviorSymbol(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCatBehaviorSymbol___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "catBehaviorSymbol"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 24, 1, 237, 160, 37, 111, 220)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtCatBehaviorSymbol"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 249, 228, 186, 221, 54, 46, 62)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDeclareSyntaxCat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "syntaxCat"};
static const lean_object* l_Lean_Fmt_fmtDeclareSyntaxCat___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSyntaxCat___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSyntaxCat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSyntaxCat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareSyntaxCat___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSyntaxCat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareSyntaxCat___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeclareSyntaxCat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeclareSyntaxCat___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDeclareSyntaxCat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 111, 111, 178, 172, 19, 49, 32)}};
static const lean_object* l_Lean_Fmt_fmtDeclareSyntaxCat___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDeclareSyntaxCat___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareSyntaxCat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareSyntaxCat___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtDeclareSyntaxCat"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 247, 146, 53, 184, 194, 193, 155)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMacroArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "macroArg"};
static const lean_object* l_Lean_Fmt_fmtMacroArg___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMacroArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMacroArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMacroArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 202, 94, 136, 146, 138, 176, 98)}};
static const lean_object* l_Lean_Fmt_fmtMacroArg___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMacroArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtMacroArg"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 235, 53, 195, 208, 99, 90, 131)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMacroRhs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "macroRhs"};
static const lean_object* l_Lean_Fmt_fmtMacroRhs___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMacroRhs___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMacroRhs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroRhs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroRhs___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroRhs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroRhs___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacroRhs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacroRhs___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMacroRhs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 168, 196, 195, 142, 145, 92, 217)}};
static const lean_object* l_Lean_Fmt_fmtMacroRhs___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMacroRhs___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroRhs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroRhs___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtMacroRhs"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 207, 255, 7, 56, 231, 198, 5)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtMacro_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtMacro_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtMacro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Fmt_fmtMacro___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtMacro___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtMacro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacro___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacro___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacro___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 185, 197, 33, 231, 124, 123, 210)}};
static const lean_object* l_Lean_Fmt_fmtMacro___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtMacro___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtMacro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "macroTail"};
static const lean_object* l_Lean_Fmt_fmtMacro___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtMacro___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtMacro___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacro___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacro___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacro___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacro___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtMacro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtMacro___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtMacro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 237, 207, 2, 224, 55, 150, 48)}};
static const lean_object* l_Lean_Fmt_fmtMacro___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtMacro___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacro___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtMacro"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 47, 191, 252, 205, 234, 119, 157)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtElabRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elab_rules"};
static const lean_object* l_Lean_Fmt_fmtElabRules___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtElabRules___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtElabRules___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtElabRules___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElabRules___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtElabRules___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElabRules___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtElabRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElabRules___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtElabRules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 70, 226, 250, 127, 121, 118, 247)}};
static const lean_object* l_Lean_Fmt_fmtElabRules___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtElabRules___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabRules(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabRules___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtElabRules"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 78, 34, 123, 221, 112, 100, 251)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elab"};
static const lean_object* l_Lean_Fmt_fmtElab___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtElab___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtElab___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtElab___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElab___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtElab___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElab___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElab___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 177, 45, 203, 60, 20, 245, 118)}};
static const lean_object* l_Lean_Fmt_fmtElab___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtElab___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabTail"};
static const lean_object* l_Lean_Fmt_fmtElab___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtElab___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtElab___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtElab___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElab___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtElab___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElab___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElab___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtElab___closed__2_value),LEAN_SCALAR_PTR_LITERAL(131, 240, 225, 71, 37, 75, 83, 37)}};
static const lean_object* l_Lean_Fmt_fmtElab___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtElab___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElab___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fmtElab"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 9, 70, 249, 241, 97, 246, 184)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderPredicate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "binderPredicate"};
static const lean_object* l_Lean_Fmt_fmtBinderPredicate___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredicate___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredicate___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredicate___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredicate___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredicate___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredicate___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtNamedName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderPredicate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderPredicate___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtBinderPredicate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 82, 29, 204, 20, 106, 176, 47)}};
static const lean_object* l_Lean_Fmt_fmtBinderPredicate___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderPredicate___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredicate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredicate___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtBinderPredicate"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecedence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 236, 176, 244, 74, 137, 250, 239)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_metaDeclarationSignature(lean_object* v_declTk_4_, lean_object* v_declSuffix_x3f_5_, lean_object* v_declParams_6_, lean_object* v_metaSignature_x3f_7_, lean_object* v_colonTk_x3f_8_, lean_object* v_kind_x3f_9_){
_start:
{
uint8_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; lean_object* v___x_17_; lean_object* v_fullDeclTk_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v_lhs_23_; uint8_t v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_10_ = 0;
v___x_11_ = l_Lean_Fmt_Layouts_prefixOperator(v_declTk_4_, v_declSuffix_x3f_5_, v___x_10_);
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_mk_empty_array_with_capacity(v___x_12_);
v___x_14_ = lean_array_push(v___x_13_, v___x_11_);
v___x_15_ = l_Array_append___redArg(v___x_14_, v_declParams_6_);
v___x_16_ = 1;
v___x_17_ = ((lean_object*)(l_Lean_Fmt_metaDeclarationSignature___closed__0));
v_fullDeclTk_18_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_15_, v___x_17_);
v___x_19_ = lean_unsigned_to_nat(2u);
v___x_20_ = lean_mk_empty_array_with_capacity(v___x_19_);
lean_inc_ref(v___x_20_);
v___x_21_ = lean_array_push(v___x_20_, v_fullDeclTk_18_);
v___x_22_ = lean_array_push(v___x_21_, v_metaSignature_x3f_7_);
v_lhs_23_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_22_, v___x_16_);
lean_dec_ref(v___x_22_);
v___x_24_ = 2;
v___x_25_ = l_Lean_Fmt_Layouts_prefixOperator(v_colonTk_x3f_8_, v_kind_x3f_9_, v___x_24_);
v___x_26_ = lean_array_push(v___x_20_, v_lhs_23_);
v___x_27_ = lean_array_push(v___x_26_, v___x_25_);
v___x_28_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_27_, v___x_16_);
lean_dec_ref(v___x_27_);
v___x_29_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_metaDeclarationSignature___boxed(lean_object* v_declTk_30_, lean_object* v_declSuffix_x3f_31_, lean_object* v_declParams_32_, lean_object* v_metaSignature_x3f_33_, lean_object* v_colonTk_x3f_34_, lean_object* v_kind_x3f_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Fmt_metaDeclarationSignature(v_declTk_30_, v_declSuffix_x3f_31_, v_declParams_32_, v_metaSignature_x3f_33_, v_colonTk_x3f_34_, v_kind_x3f_35_);
lean_dec_ref(v_declParams_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaDeclarationSignature(lean_object* v_declTk_37_, lean_object* v_declSuffix_x3f_38_, lean_object* v_declParams_39_, lean_object* v_metaSignature_x3f_40_, lean_object* v_colonTk_x3f_41_, lean_object* v_kind_x3f_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Fmt_fmt(v_declTk_37_, v_a_43_, v_a_44_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v_a_46_; lean_object* v_a_47_; lean_object* v___x_48_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_a_46_);
v_a_47_ = lean_ctor_get(v___x_45_, 1);
lean_inc(v_a_47_);
lean_dec_ref_known(v___x_45_, 2);
v___x_48_ = l_Lean_Fmt_fmt_x3f(v_declSuffix_x3f_38_, v_a_43_, v_a_47_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v_a_50_; lean_object* v___x_51_; 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_a_49_);
v_a_50_ = lean_ctor_get(v___x_48_, 1);
lean_inc(v_a_50_);
lean_dec_ref_known(v___x_48_, 2);
v___x_51_ = l_Lean_Fmt_fmt_x3f(v_colonTk_x3f_41_, v_a_43_, v_a_50_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v_a_53_; lean_object* v___x_54_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
v_a_53_ = lean_ctor_get(v___x_51_, 1);
lean_inc(v_a_53_);
lean_dec_ref_known(v___x_51_, 2);
v___x_54_ = l_Lean_Fmt_fmt_x3f(v_kind_x3f_42_, v_a_43_, v_a_53_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_64_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_a_56_ = lean_ctor_get(v___x_54_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_64_ == 0)
{
v___x_58_ = v___x_54_;
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = l_Lean_Fmt_metaDeclarationSignature(v_a_46_, v_a_49_, v_declParams_39_, v_metaSignature_x3f_40_, v_a_52_, v_a_55_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v___x_60_);
v___x_62_ = v___x_58_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_a_56_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
else
{
lean_dec(v_a_52_);
lean_dec(v_a_49_);
lean_dec(v_a_46_);
lean_dec_ref(v_metaSignature_x3f_40_);
return v___x_54_;
}
}
else
{
lean_dec(v_a_49_);
lean_dec(v_a_46_);
lean_dec(v_kind_x3f_42_);
lean_dec_ref(v_metaSignature_x3f_40_);
return v___x_51_;
}
}
else
{
lean_dec(v_a_46_);
lean_dec(v_kind_x3f_42_);
lean_dec(v_colonTk_x3f_41_);
lean_dec_ref(v_metaSignature_x3f_40_);
return v___x_48_;
}
}
else
{
lean_dec(v_kind_x3f_42_);
lean_dec(v_colonTk_x3f_41_);
lean_dec_ref(v_metaSignature_x3f_40_);
lean_dec(v_declSuffix_x3f_38_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaDeclarationSignature___boxed(lean_object* v_declTk_65_, lean_object* v_declSuffix_x3f_66_, lean_object* v_declParams_67_, lean_object* v_metaSignature_x3f_68_, lean_object* v_colonTk_x3f_69_, lean_object* v_kind_x3f_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Fmt_fmtMetaDeclarationSignature(v_declTk_65_, v_declSuffix_x3f_66_, v_declParams_67_, v_metaSignature_x3f_68_, v_colonTk_x3f_69_, v_kind_x3f_70_, v_a_71_, v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec_ref(v_declParams_67_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabDeclarationSignature(lean_object* v_declTk_77_, lean_object* v_declSuffix_x3f_78_, lean_object* v_declParams_79_, lean_object* v_metaSignature_80_, lean_object* v_colonTk_x3f_81_, lean_object* v_kind_x3f_82_, lean_object* v_leTk_x3f_83_, lean_object* v_expectedType_x3f_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Fmt_fmt(v_declTk_77_, v_a_85_, v_a_86_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v_a_89_; lean_object* v___x_90_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
v_a_89_ = lean_ctor_get(v___x_87_, 1);
lean_inc(v_a_89_);
lean_dec_ref_known(v___x_87_, 2);
v___x_90_ = l_Lean_Fmt_fmt_x3f(v_declSuffix_x3f_78_, v_a_85_, v_a_89_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v_a_92_; lean_object* v___x_93_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
v_a_92_ = lean_ctor_get(v___x_90_, 1);
lean_inc(v_a_92_);
lean_dec_ref_known(v___x_90_, 2);
v___x_93_ = l_Lean_Fmt_fmt_x3f(v_colonTk_x3f_81_, v_a_85_, v_a_92_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v___x_96_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
v_a_95_ = lean_ctor_get(v___x_93_, 1);
lean_inc(v_a_95_);
lean_dec_ref_known(v___x_93_, 2);
v___x_96_ = l_Lean_Fmt_fmt_x3f(v_kind_x3f_82_, v_a_85_, v_a_95_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v___x_99_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
v_a_98_ = lean_ctor_get(v___x_96_, 1);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_96_, 2);
v___x_99_ = l_Lean_Fmt_fmt_x3f(v_leTk_x3f_83_, v_a_85_, v_a_98_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v_a_101_; lean_object* v___x_102_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
v_a_101_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_99_, 2);
v___x_102_ = l_Lean_Fmt_fmt_x3f(v_expectedType_x3f_84_, v_a_85_, v_a_101_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_134_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_a_104_ = lean_ctor_get(v___x_102_, 1);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_134_ == 0)
{
v___x_106_ = v___x_102_;
v_isShared_107_ = v_isSharedCheck_134_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_134_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_108_ = 0;
v___x_109_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_88_, v_a_91_, v___x_108_);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_mk_empty_array_with_capacity(v___x_110_);
v___x_112_ = lean_array_push(v___x_111_, v___x_109_);
v___x_113_ = l_Array_append___redArg(v___x_112_, v_declParams_79_);
v___x_114_ = 1;
v___x_115_ = ((lean_object*)(l_Lean_Fmt_metaDeclarationSignature___closed__0));
v___x_116_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_113_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(2u);
v___x_118_ = lean_mk_empty_array_with_capacity(v___x_117_);
v___x_119_ = lean_array_push(v___x_118_, v___x_116_);
v___x_120_ = lean_array_push(v___x_119_, v_metaSignature_80_);
v___x_121_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_120_, v___x_114_);
lean_dec_ref(v___x_120_);
v___x_122_ = lean_unsigned_to_nat(5u);
v___x_123_ = lean_mk_empty_array_with_capacity(v___x_122_);
v___x_124_ = lean_array_push(v___x_123_, v___x_121_);
v___x_125_ = lean_array_push(v___x_124_, v_a_94_);
v___x_126_ = lean_array_push(v___x_125_, v_a_97_);
v___x_127_ = lean_array_push(v___x_126_, v_a_100_);
v___x_128_ = lean_array_push(v___x_127_, v_a_103_);
v___x_129_ = ((lean_object*)(l_Lean_Fmt_fmtElabDeclarationSignature___closed__0));
v___x_130_ = l_Lean_Fmt_Layouts_infixOperator(v___x_128_, v___x_129_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_130_);
v___x_132_ = v___x_106_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_a_104_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
else
{
lean_dec(v_a_100_);
lean_dec(v_a_97_);
lean_dec(v_a_94_);
lean_dec(v_a_91_);
lean_dec(v_a_88_);
lean_dec_ref(v_metaSignature_80_);
return v___x_102_;
}
}
else
{
lean_dec(v_a_97_);
lean_dec(v_a_94_);
lean_dec(v_a_91_);
lean_dec(v_a_88_);
lean_dec(v_expectedType_x3f_84_);
lean_dec_ref(v_metaSignature_80_);
return v___x_99_;
}
}
else
{
lean_dec(v_a_94_);
lean_dec(v_a_91_);
lean_dec(v_a_88_);
lean_dec(v_expectedType_x3f_84_);
lean_dec(v_leTk_x3f_83_);
lean_dec_ref(v_metaSignature_80_);
return v___x_96_;
}
}
else
{
lean_dec(v_a_91_);
lean_dec(v_a_88_);
lean_dec(v_expectedType_x3f_84_);
lean_dec(v_leTk_x3f_83_);
lean_dec(v_kind_x3f_82_);
lean_dec_ref(v_metaSignature_80_);
return v___x_93_;
}
}
else
{
lean_dec(v_a_88_);
lean_dec(v_expectedType_x3f_84_);
lean_dec(v_leTk_x3f_83_);
lean_dec(v_kind_x3f_82_);
lean_dec(v_colonTk_x3f_81_);
lean_dec_ref(v_metaSignature_80_);
return v___x_90_;
}
}
else
{
lean_dec(v_expectedType_x3f_84_);
lean_dec(v_leTk_x3f_83_);
lean_dec(v_kind_x3f_82_);
lean_dec(v_colonTk_x3f_81_);
lean_dec_ref(v_metaSignature_80_);
lean_dec(v_declSuffix_x3f_78_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabDeclarationSignature___boxed(lean_object* v_declTk_135_, lean_object* v_declSuffix_x3f_136_, lean_object* v_declParams_137_, lean_object* v_metaSignature_138_, lean_object* v_colonTk_x3f_139_, lean_object* v_kind_x3f_140_, lean_object* v_leTk_x3f_141_, lean_object* v_expectedType_x3f_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Fmt_fmtElabDeclarationSignature(v_declTk_135_, v_declSuffix_x3f_136_, v_declParams_137_, v_metaSignature_138_, v_colonTk_x3f_139_, v_kind_x3f_140_, v_leTk_x3f_141_, v_expectedType_x3f_142_, v_a_143_, v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec_ref(v_declParams_137_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaAssignmentDeclaration(lean_object* v_docComment_x3f_146_, lean_object* v_attributes_x3f_147_, lean_object* v_mods_148_, lean_object* v_declTk_149_, lean_object* v_declSuffix_x3f_150_, lean_object* v_declParams_151_, lean_object* v_metaSignature_152_, lean_object* v_colonTk_x3f_153_, lean_object* v_kind_x3f_154_, lean_object* v_sepTk_155_, lean_object* v_body_156_, uint8_t v_rawBody_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Fmt_fmtMetaDeclarationSignature(v_declTk_149_, v_declSuffix_x3f_150_, v_declParams_151_, v_metaSignature_152_, v_colonTk_x3f_153_, v_kind_x3f_154_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v_a_162_; lean_object* v___x_163_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
v_a_162_ = lean_ctor_get(v___x_160_, 1);
lean_inc(v_a_162_);
lean_dec_ref_known(v___x_160_, 2);
v___x_163_ = l_Lean_Fmt_fmt(v_sepTk_155_, v_a_158_, v_a_162_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v_a_165_; lean_object* v_body_167_; lean_object* v___y_168_; lean_object* v___y_169_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
v_a_165_ = lean_ctor_get(v___x_163_, 1);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_163_, 2);
if (v_rawBody_157_ == 0)
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Fmt_fmt(v_body_156_, v_a_158_, v_a_165_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v_a_175_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
v_a_175_ = lean_ctor_get(v___x_173_, 1);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_173_, 2);
v_body_167_ = v_a_174_;
v___y_168_ = v_a_158_;
v___y_169_ = v_a_175_;
goto v___jp_166_;
}
else
{
lean_dec(v_a_164_);
lean_dec(v_a_161_);
lean_dec(v_attributes_x3f_147_);
lean_dec(v_docComment_x3f_146_);
return v___x_173_;
}
}
else
{
uint8_t v___x_176_; lean_object* v___x_177_; 
v___x_176_ = 0;
v___x_177_ = l_Lean_Fmt_fmtRaw(v___x_176_, v_body_156_, v_a_158_, v_a_165_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v_a_179_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
v_a_179_ = lean_ctor_get(v___x_177_, 1);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_177_, 2);
v_body_167_ = v_a_178_;
v___y_168_ = v_a_158_;
v___y_169_ = v_a_179_;
goto v___jp_166_;
}
else
{
lean_dec(v_a_164_);
lean_dec(v_a_161_);
lean_dec(v_attributes_x3f_147_);
lean_dec(v_docComment_x3f_146_);
return v___x_177_;
}
}
v___jp_166_:
{
uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = 0;
v___x_171_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_161_, v_a_164_, v_body_167_, v___x_170_);
v___x_172_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_146_, v_attributes_x3f_147_, v_mods_148_, v___x_171_, v___y_168_, v___y_169_);
return v___x_172_;
}
}
else
{
lean_dec(v_a_161_);
lean_dec(v_body_156_);
lean_dec(v_attributes_x3f_147_);
lean_dec(v_docComment_x3f_146_);
return v___x_163_;
}
}
else
{
lean_dec(v_body_156_);
lean_dec(v_sepTk_155_);
lean_dec(v_attributes_x3f_147_);
lean_dec(v_docComment_x3f_146_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaAssignmentDeclaration___boxed(lean_object* v_docComment_x3f_180_, lean_object* v_attributes_x3f_181_, lean_object* v_mods_182_, lean_object* v_declTk_183_, lean_object* v_declSuffix_x3f_184_, lean_object* v_declParams_185_, lean_object* v_metaSignature_186_, lean_object* v_colonTk_x3f_187_, lean_object* v_kind_x3f_188_, lean_object* v_sepTk_189_, lean_object* v_body_190_, lean_object* v_rawBody_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
uint8_t v_rawBody_boxed_194_; lean_object* v_res_195_; 
v_rawBody_boxed_194_ = lean_unbox(v_rawBody_191_);
v_res_195_ = l_Lean_Fmt_fmtMetaAssignmentDeclaration(v_docComment_x3f_180_, v_attributes_x3f_181_, v_mods_182_, v_declTk_183_, v_declSuffix_x3f_184_, v_declParams_185_, v_metaSignature_186_, v_colonTk_x3f_187_, v_kind_x3f_188_, v_sepTk_189_, v_body_190_, v_rawBody_boxed_194_, v_a_192_, v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec_ref(v_declParams_185_);
lean_dec_ref(v_mods_182_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaMatchDeclaration(lean_object* v_docComment_x3f_196_, lean_object* v_attributes_x3f_197_, lean_object* v_mods_198_, lean_object* v_declTk_199_, lean_object* v_declSuffix_x3f_200_, lean_object* v_declParams_201_, lean_object* v_metaSignature_202_, lean_object* v_colonTk_x3f_203_, lean_object* v_kind_x3f_204_, lean_object* v_matchAlts_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Fmt_fmtMetaDeclarationSignature(v_declTk_199_, v_declSuffix_x3f_200_, v_declParams_201_, v_metaSignature_202_, v_colonTk_x3f_203_, v_kind_x3f_204_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
v_a_210_ = lean_ctor_get(v___x_208_, 1);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_208_, 2);
v___x_211_ = l_Lean_Fmt_fmt(v_matchAlts_205_, v_a_206_, v_a_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v_a_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
v_a_213_ = lean_ctor_get(v___x_211_, 1);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_211_, 2);
v___x_214_ = l_Lean_Fmt_Layouts_matchDeclaration(v_a_209_, v_a_212_);
v___x_215_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_196_, v_attributes_x3f_197_, v_mods_198_, v___x_214_, v_a_206_, v_a_213_);
return v___x_215_;
}
else
{
lean_dec(v_a_209_);
lean_dec(v_attributes_x3f_197_);
lean_dec(v_docComment_x3f_196_);
return v___x_211_;
}
}
else
{
lean_dec(v_matchAlts_205_);
lean_dec(v_attributes_x3f_197_);
lean_dec(v_docComment_x3f_196_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMetaMatchDeclaration___boxed(lean_object* v_docComment_x3f_216_, lean_object* v_attributes_x3f_217_, lean_object* v_mods_218_, lean_object* v_declTk_219_, lean_object* v_declSuffix_x3f_220_, lean_object* v_declParams_221_, lean_object* v_metaSignature_222_, lean_object* v_colonTk_x3f_223_, lean_object* v_kind_x3f_224_, lean_object* v_matchAlts_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Fmt_fmtMetaMatchDeclaration(v_docComment_x3f_216_, v_attributes_x3f_217_, v_mods_218_, v_declTk_219_, v_declSuffix_x3f_220_, v_declParams_221_, v_metaSignature_222_, v_colonTk_x3f_223_, v_kind_x3f_224_, v_matchAlts_225_, v_a_226_, v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec_ref(v_declParams_221_);
lean_dec_ref(v_mods_218_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrecedence(lean_object* v_x_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__3));
lean_inc(v_x_236_);
v___x_240_ = l_Lean_Syntax_isOfKind(v_x_236_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v_x_236_);
v___x_241_ = l_Lean_Fmt_Error_partialFormatter;
v___x_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v_a_238_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; lean_object* v_colonTk_244_; lean_object* v___x_245_; 
v___x_243_ = lean_unsigned_to_nat(0u);
v_colonTk_244_ = l_Lean_Syntax_getArg(v_x_236_, v___x_243_);
v___x_245_ = l_Lean_Fmt_fmt(v_colonTk_244_, v_a_237_, v_a_238_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v_a_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
v_a_247_ = lean_ctor_get(v___x_245_, 1);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_245_, 2);
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = l_Lean_Syntax_getArg(v_x_236_, v___x_248_);
lean_dec(v_x_236_);
v___x_250_ = l_Lean_Fmt_fmt(v___x_249_, v_a_237_, v_a_247_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_261_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_a_252_ = lean_ctor_get(v___x_250_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_261_ == 0)
{
v___x_254_ = v___x_250_;
v_isShared_255_ = v_isSharedCheck_261_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_261_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = 0;
v___x_257_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_246_, v_a_251_, v___x_256_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_257_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_a_252_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
else
{
lean_dec(v_a_246_);
return v___x_250_;
}
}
else
{
lean_dec(v_x_236_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrecedence___boxed(lean_object* v_x_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Fmt_fmtPrecedence(v_x_262_, v_a_263_, v_a_264_);
lean_dec_ref(v_a_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1(){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_273_ = l_Lean_Fmt_fmtAttribute;
v___x_274_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__3));
v___x_275_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___closed__2));
v___x_276_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPrecedence___boxed), 3, 0);
v___x_277_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_273_, v___x_274_, v___x_275_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1___boxed(lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1();
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(size_t v_sz_280_, size_t v_i_281_, lean_object* v_bs_282_){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = lean_usize_dec_lt(v_i_281_, v_sz_280_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v_bs_282_);
return v___x_284_;
}
else
{
lean_object* v_v_285_; lean_object* v___x_286_; lean_object* v_bs_x27_287_; size_t v___x_288_; size_t v___x_289_; lean_object* v___x_290_; 
v_v_285_ = lean_array_uget(v_bs_282_, v_i_281_);
v___x_286_ = lean_unsigned_to_nat(0u);
v_bs_x27_287_ = lean_array_uset(v_bs_282_, v_i_281_, v___x_286_);
v___x_288_ = ((size_t)1ULL);
v___x_289_ = lean_usize_add(v_i_281_, v___x_288_);
v___x_290_ = lean_array_uset(v_bs_x27_287_, v_i_281_, v_v_285_);
v_i_281_ = v___x_289_;
v_bs_282_ = v___x_290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0___boxed(lean_object* v_sz_292_, lean_object* v_i_293_, lean_object* v_bs_294_){
_start:
{
size_t v_sz_boxed_295_; size_t v_i_boxed_296_; lean_object* v_res_297_; 
v_sz_boxed_295_ = lean_unbox_usize(v_sz_292_);
lean_dec(v_sz_292_);
v_i_boxed_296_ = lean_unbox_usize(v_i_293_);
lean_dec(v_i_293_);
v_res_297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(v_sz_boxed_295_, v_i_boxed_296_, v_bs_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxParen(lean_object* v_x_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxParen___closed__2));
lean_inc(v_x_305_);
v___x_309_ = l_Lean_Syntax_isOfKind(v_x_305_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_x_305_);
v___x_310_ = l_Lean_Fmt_Error_partialFormatter;
v___x_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_a_307_);
return v___x_311_;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; size_t v_sz_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = l_Lean_Syntax_getArg(v_x_305_, v___x_312_);
v___x_314_ = l_Lean_Syntax_getArgs(v___x_313_);
lean_dec(v___x_313_);
v_sz_315_ = lean_array_size(v___x_314_);
v___x_316_ = ((size_t)0ULL);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(v_sz_315_, v___x_316_, v___x_314_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_x_305_);
v___x_318_ = l_Lean_Fmt_Error_partialFormatter;
v___x_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_a_307_);
return v___x_319_;
}
else
{
lean_object* v_val_320_; lean_object* v___x_321_; lean_object* v_lbTk_322_; lean_object* v___x_323_; 
v_val_320_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v___x_317_, 1);
v___x_321_ = lean_unsigned_to_nat(0u);
v_lbTk_322_ = l_Lean_Syntax_getArg(v_x_305_, v___x_321_);
v___x_323_ = l_Lean_Fmt_fmt(v_lbTk_322_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v_a_325_; lean_object* v___x_326_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
v_a_325_ = lean_ctor_get(v___x_323_, 1);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_323_, 2);
v___x_326_ = l_Lean_Fmt_fmtArray___redArg(v_val_320_, v_a_306_, v_a_325_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v_a_328_; lean_object* v___x_329_; lean_object* v_rbTk_330_; lean_object* v___x_331_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
v_a_328_ = lean_ctor_get(v___x_326_, 1);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_326_, 2);
v___x_329_ = lean_unsigned_to_nat(2u);
v_rbTk_330_ = l_Lean_Syntax_getArg(v_x_305_, v___x_329_);
lean_dec(v_x_305_);
v___x_331_ = l_Lean_Fmt_fmt(v_rbTk_330_, v_a_306_, v_a_328_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_352_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_a_333_ = lean_ctor_get(v___x_331_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_352_ == 0)
{
v___x_335_ = v___x_331_;
v_isShared_336_ = v_isSharedCheck_352_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_352_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v_args_338_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_array_get_size(v_a_327_);
v___x_345_ = lean_nat_dec_lt(v___x_312_, v___x_344_);
if (v___x_345_ == 0)
{
v_args_338_ = v_a_327_;
goto v___jp_337_;
}
else
{
uint8_t v___x_346_; 
v___x_346_ = lean_nat_dec_lt(v___x_321_, v___x_344_);
if (v___x_346_ == 0)
{
v_args_338_ = v_a_327_;
goto v___jp_337_;
}
else
{
lean_object* v_v_347_; lean_object* v___x_348_; lean_object* v_xs_x27_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_v_347_ = lean_array_fget(v_a_327_, v___x_321_);
v___x_348_ = lean_box(0);
v_xs_x27_349_ = lean_array_fset(v_a_327_, v___x_321_, v___x_348_);
v___x_350_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_347_);
v___x_351_ = lean_array_fset(v_xs_x27_349_, v___x_321_, v___x_350_);
v_args_338_ = v___x_351_;
goto v___jp_337_;
}
}
v___jp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_339_ = l_Lean_Fmt_Layouts_fill(v_args_338_);
lean_dec_ref(v_args_338_);
v___x_340_ = l_Lean_Fmt_Layouts_parens(v_a_324_, v___x_339_, v_a_332_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_340_);
v___x_342_ = v___x_335_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_a_333_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_dec(v_a_327_);
lean_dec(v_a_324_);
return v___x_331_;
}
}
else
{
lean_object* v_a_353_; lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec(v_a_324_);
lean_dec(v_x_305_);
v_a_353_ = lean_ctor_get(v___x_326_, 0);
v_a_354_ = lean_ctor_get(v___x_326_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_326_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_inc(v_a_353_);
lean_dec(v___x_326_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_353_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_dec(v_val_320_);
lean_dec(v_x_305_);
return v___x_323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxParen___boxed(lean_object* v_x_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Fmt_fmtSyntaxParen(v_x_362_, v_a_363_, v_a_364_);
lean_dec_ref(v_a_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1(){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_372_ = l_Lean_Fmt_fmtAttribute;
v___x_373_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxParen___closed__2));
v___x_374_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___closed__1));
v___x_375_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntaxParen___boxed), 3, 0);
v___x_376_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_372_, v___x_373_, v___x_374_, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1___boxed(lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1();
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxCat(lean_object* v_x_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__1));
lean_inc(v_x_388_);
v___x_409_ = l_Lean_Syntax_isOfKind(v_x_388_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v_x_388_);
v___x_410_ = l_Lean_Fmt_Error_partialFormatter;
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_a_390_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v_prec_x3f_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = l_Lean_Syntax_getArg(v_x_388_, v___x_412_);
v___x_432_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v___x_413_);
v___x_433_ = l_Lean_Syntax_isOfKind(v___x_413_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v___x_413_);
lean_dec(v_x_388_);
v___x_434_ = l_Lean_Fmt_Error_partialFormatter;
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v_a_390_);
return v___x_435_;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = l_Lean_Syntax_getArg(v_x_388_, v___x_436_);
lean_dec(v_x_388_);
v___x_438_ = l_Lean_Syntax_isNone(v___x_437_);
if (v___x_438_ == 0)
{
uint8_t v___x_439_; 
lean_inc(v___x_437_);
v___x_439_ = l_Lean_Syntax_matchesNull(v___x_437_, v___x_436_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec(v___x_437_);
lean_dec(v___x_413_);
v___x_440_ = l_Lean_Fmt_Error_partialFormatter;
v___x_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v_a_390_);
return v___x_441_;
}
else
{
lean_object* v_prec_x3f_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_prec_x3f_442_ = l_Lean_Syntax_getArg(v___x_437_, v___x_412_);
lean_dec(v___x_437_);
v___x_443_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__3));
lean_inc(v_prec_x3f_442_);
v___x_444_ = l_Lean_Syntax_isOfKind(v_prec_x3f_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_prec_x3f_442_);
lean_dec(v___x_413_);
v___x_445_ = l_Lean_Fmt_Error_partialFormatter;
v___x_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v_a_390_);
return v___x_446_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v_prec_x3f_442_);
v_prec_x3f_415_ = v___x_447_;
v___y_416_ = v_a_389_;
v___y_417_ = v_a_390_;
goto v___jp_414_;
}
}
}
else
{
lean_object* v___x_448_; 
lean_dec(v___x_437_);
v___x_448_ = lean_box(0);
v_prec_x3f_415_ = v___x_448_;
v___y_416_ = v_a_389_;
v___y_417_ = v_a_390_;
goto v___jp_414_;
}
}
v___jp_414_:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Fmt_fmt(v___x_413_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
if (lean_obj_tag(v_prec_x3f_415_) == 0)
{
lean_object* v_a_419_; lean_object* v_a_420_; lean_object* v___x_421_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
v_a_420_ = lean_ctor_get(v___x_418_, 1);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_418_, 2);
v___x_421_ = lean_box(0);
v___y_392_ = v_a_420_;
v___y_393_ = v___y_416_;
v___y_394_ = v_a_419_;
v___y_395_ = v___x_421_;
goto v___jp_391_;
}
else
{
lean_object* v_a_422_; lean_object* v_a_423_; lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_a_422_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_422_);
v_a_423_ = lean_ctor_get(v___x_418_, 1);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_418_, 2);
v_val_424_ = lean_ctor_get(v_prec_x3f_415_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_prec_x3f_415_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v_prec_x3f_415_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_dec(v_prec_x3f_415_);
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
v___y_392_ = v_a_423_;
v___y_393_ = v___y_416_;
v___y_394_ = v_a_422_;
v___y_395_ = v___x_429_;
goto v___jp_391_;
}
}
}
}
else
{
lean_dec(v_prec_x3f_415_);
return v___x_418_;
}
}
}
v___jp_391_:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Fmt_fmt_x3f(v___y_395_, v___y_393_, v___y_392_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_407_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_a_398_ = lean_ctor_get(v___x_396_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_407_ == 0)
{
v___x_400_ = v___x_396_;
v_isShared_401_ = v_isSharedCheck_407_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_407_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_402_ = 0;
v___x_403_ = l_Lean_Fmt_Layouts_prefixOperator(v___y_394_, v_a_397_, v___x_402_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_403_);
v___x_405_ = v___x_400_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_a_398_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
else
{
lean_dec_ref(v___y_394_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxCat___boxed(lean_object* v_x_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Fmt_fmtSyntaxCat(v_x_449_, v_a_450_, v_a_451_);
lean_dec_ref(v_a_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1(){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_459_ = l_Lean_Fmt_fmtAttribute;
v___x_460_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__1));
v___x_461_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___closed__1));
v___x_462_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntaxCat___boxed), 3, 0);
v___x_463_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_459_, v___x_460_, v___x_461_, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1___boxed(lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1();
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxUnary(lean_object* v_x_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxUnary___closed__1));
lean_inc(v_x_472_);
v___x_476_ = l_Lean_Syntax_isOfKind(v_x_472_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_x_472_);
v___x_477_ = l_Lean_Fmt_Error_partialFormatter;
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_a_474_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = l_Lean_Syntax_getArg(v_x_472_, v___x_479_);
v___x_481_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v___x_480_);
v___x_482_ = l_Lean_Syntax_isOfKind(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v___x_480_);
lean_dec(v_x_472_);
v___x_483_ = l_Lean_Fmt_Error_partialFormatter;
v___x_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v_a_474_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; size_t v_sz_488_; size_t v___x_489_; lean_object* v___x_490_; 
v___x_485_ = lean_unsigned_to_nat(2u);
v___x_486_ = l_Lean_Syntax_getArg(v_x_472_, v___x_485_);
v___x_487_ = l_Lean_Syntax_getArgs(v___x_486_);
lean_dec(v___x_486_);
v_sz_488_ = lean_array_size(v___x_487_);
v___x_489_ = ((size_t)0ULL);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(v_sz_488_, v___x_489_, v___x_487_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v___x_480_);
lean_dec(v_x_472_);
v___x_491_ = l_Lean_Fmt_Error_partialFormatter;
v___x_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v_a_474_);
return v___x_492_;
}
else
{
lean_object* v_val_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_539_; 
v_val_493_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_539_ == 0)
{
v___x_495_ = v___x_490_;
v_isShared_496_ = v_isSharedCheck_539_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_val_493_);
lean_dec(v___x_490_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_539_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_Fmt_fmt(v___x_480_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v_a_499_; lean_object* v___x_500_; lean_object* v_lbTk_501_; lean_object* v___x_502_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
v_a_499_ = lean_ctor_get(v___x_497_, 1);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_497_, 2);
v___x_500_ = lean_unsigned_to_nat(1u);
v_lbTk_501_ = l_Lean_Syntax_getArg(v_x_472_, v___x_500_);
v___x_502_ = l_Lean_Fmt_fmt(v_lbTk_501_, v_a_473_, v_a_499_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
v_a_504_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_502_, 2);
v___x_505_ = l_Lean_Fmt_fmtArray___redArg(v_val_493_, v_a_473_, v_a_504_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v_a_507_; lean_object* v___x_508_; lean_object* v_rbTk_509_; lean_object* v___x_510_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
v_a_507_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_505_, 2);
v___x_508_ = lean_unsigned_to_nat(3u);
v_rbTk_509_ = l_Lean_Syntax_getArg(v_x_472_, v___x_508_);
lean_dec(v_x_472_);
v___x_510_ = l_Lean_Fmt_fmt(v_rbTk_509_, v_a_473_, v_a_507_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_529_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_a_512_ = lean_ctor_get(v___x_510_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_529_ == 0)
{
v___x_514_ = v___x_510_;
v_isShared_515_ = v_isSharedCheck_529_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_529_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_516_ = lean_mk_empty_array_with_capacity(v___x_485_);
v___x_517_ = lean_array_push(v___x_516_, v_a_498_);
v___x_518_ = lean_array_push(v___x_517_, v_a_503_);
v___x_519_ = l_Lean_Fmt_Layouts_atomic(v___x_518_);
lean_dec_ref(v___x_518_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v_a_506_);
v___x_521_ = v___x_495_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_506_);
v___x_521_ = v_reuseFailAlloc_528_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_522_ = lean_mk_empty_array_with_capacity(v___x_500_);
v___x_523_ = lean_array_push(v___x_522_, v___x_521_);
v___x_524_ = l_Lean_Fmt_Layouts_metaApplication(v___x_519_, v___x_523_, v_a_511_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_524_);
v___x_526_ = v___x_514_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_a_512_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_dec(v_a_506_);
lean_dec(v_a_503_);
lean_dec(v_a_498_);
lean_del_object(v___x_495_);
return v___x_510_;
}
}
else
{
lean_object* v_a_530_; lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_a_503_);
lean_dec(v_a_498_);
lean_del_object(v___x_495_);
lean_dec(v_x_472_);
v_a_530_ = lean_ctor_get(v___x_505_, 0);
v_a_531_ = lean_ctor_get(v___x_505_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_505_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_inc(v_a_530_);
lean_dec(v___x_505_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_530_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
else
{
lean_dec(v_a_498_);
lean_del_object(v___x_495_);
lean_dec(v_val_493_);
lean_dec(v_x_472_);
return v___x_502_;
}
}
else
{
lean_del_object(v___x_495_);
lean_dec(v_val_493_);
lean_dec(v_x_472_);
return v___x_497_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxUnary___boxed(lean_object* v_x_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Fmt_fmtSyntaxUnary(v_x_540_, v_a_541_, v_a_542_);
lean_dec_ref(v_a_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1(){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_550_ = l_Lean_Fmt_fmtAttribute;
v___x_551_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxUnary___closed__1));
v___x_552_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___closed__1));
v___x_553_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntaxUnary___boxed), 3, 0);
v___x_554_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_550_, v___x_551_, v___x_552_, v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1___boxed(lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1();
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxBinary(lean_object* v_x_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxBinary___closed__1));
lean_inc(v_x_563_);
v___x_567_ = l_Lean_Syntax_isOfKind(v_x_563_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v_x_563_);
v___x_568_ = l_Lean_Fmt_Error_partialFormatter;
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v_a_565_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = l_Lean_Syntax_getArg(v_x_563_, v___x_570_);
v___x_572_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v___x_571_);
v___x_573_ = l_Lean_Syntax_isOfKind(v___x_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v___x_571_);
lean_dec(v_x_563_);
v___x_574_ = l_Lean_Fmt_Error_partialFormatter;
v___x_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_a_565_);
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; size_t v_sz_579_; size_t v___x_580_; lean_object* v___x_581_; 
v___x_576_ = lean_unsigned_to_nat(2u);
v___x_577_ = l_Lean_Syntax_getArg(v_x_563_, v___x_576_);
v___x_578_ = l_Lean_Syntax_getArgs(v___x_577_);
lean_dec(v___x_577_);
v_sz_579_ = lean_array_size(v___x_578_);
v___x_580_ = ((size_t)0ULL);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(v_sz_579_, v___x_580_, v___x_578_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v___x_571_);
lean_dec(v_x_563_);
v___x_582_ = l_Lean_Fmt_Error_partialFormatter;
v___x_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v_a_565_);
return v___x_583_;
}
else
{
lean_object* v_val_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_665_; 
v_val_584_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_665_ == 0)
{
v___x_586_ = v___x_581_;
v_isShared_587_ = v_isSharedCheck_665_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_val_584_);
lean_dec(v___x_581_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_665_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; size_t v_sz_591_; lean_object* v___x_592_; 
v___x_588_ = lean_unsigned_to_nat(4u);
v___x_589_ = l_Lean_Syntax_getArg(v_x_563_, v___x_588_);
v___x_590_ = l_Lean_Syntax_getArgs(v___x_589_);
lean_dec(v___x_589_);
v_sz_591_ = lean_array_size(v___x_590_);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(v_sz_591_, v___x_580_, v___x_590_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_del_object(v___x_586_);
lean_dec(v_val_584_);
lean_dec(v___x_571_);
lean_dec(v_x_563_);
v___x_593_ = l_Lean_Fmt_Error_partialFormatter;
v___x_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v_a_565_);
return v___x_594_;
}
else
{
lean_object* v_val_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_664_; 
v_val_595_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_664_ == 0)
{
v___x_597_ = v___x_592_;
v_isShared_598_ = v_isSharedCheck_664_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_val_595_);
lean_dec(v___x_592_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_664_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Fmt_fmt(v___x_571_, v_a_564_, v_a_565_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v_a_601_; lean_object* v___x_602_; lean_object* v_lbTk_603_; lean_object* v___x_604_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
v_a_601_ = lean_ctor_get(v___x_599_, 1);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_599_, 2);
v___x_602_ = lean_unsigned_to_nat(1u);
v_lbTk_603_ = l_Lean_Syntax_getArg(v_x_563_, v___x_602_);
v___x_604_ = l_Lean_Fmt_fmt(v_lbTk_603_, v_a_564_, v_a_601_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v_a_606_; lean_object* v___x_607_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
v_a_606_ = lean_ctor_get(v___x_604_, 1);
lean_inc(v_a_606_);
lean_dec_ref_known(v___x_604_, 2);
v___x_607_ = l_Lean_Fmt_fmtArray___redArg(v_val_584_, v_a_564_, v_a_606_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v_a_609_; lean_object* v___x_610_; lean_object* v_commaTk_611_; lean_object* v___x_612_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
v_a_609_ = lean_ctor_get(v___x_607_, 1);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_607_, 2);
v___x_610_ = lean_unsigned_to_nat(3u);
v_commaTk_611_ = l_Lean_Syntax_getArg(v_x_563_, v___x_610_);
v___x_612_ = l_Lean_Fmt_fmt(v_commaTk_611_, v_a_564_, v_a_609_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v_a_614_; lean_object* v___x_615_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
v_a_614_ = lean_ctor_get(v___x_612_, 1);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_612_, 2);
v___x_615_ = l_Lean_Fmt_fmtArray___redArg(v_val_595_, v_a_564_, v_a_614_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v_a_617_; lean_object* v___x_618_; lean_object* v_rbTk_619_; lean_object* v___x_620_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
v_a_617_ = lean_ctor_get(v___x_615_, 1);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_615_, 2);
v___x_618_ = lean_unsigned_to_nat(5u);
v_rbTk_619_ = l_Lean_Syntax_getArg(v_x_563_, v___x_618_);
lean_dec(v_x_563_);
v___x_620_ = l_Lean_Fmt_fmt(v_rbTk_619_, v_a_564_, v_a_617_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_645_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_a_622_ = lean_ctor_get(v___x_620_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_645_ == 0)
{
v___x_624_ = v___x_620_;
v_isShared_625_ = v_isSharedCheck_645_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_645_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_626_ = lean_mk_empty_array_with_capacity(v___x_576_);
v___x_627_ = lean_array_push(v___x_626_, v_a_600_);
v___x_628_ = lean_array_push(v___x_627_, v_a_605_);
v___x_629_ = l_Lean_Fmt_Layouts_atomic(v___x_628_);
lean_dec_ref(v___x_628_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v_a_608_);
v___x_631_ = v___x_597_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_608_);
v___x_631_ = v_reuseFailAlloc_644_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 0);
lean_ctor_set(v___x_586_, 0, v_a_613_);
v___x_633_ = v___x_586_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_613_);
v___x_633_ = v_reuseFailAlloc_643_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v_a_616_);
v___x_635_ = lean_mk_empty_array_with_capacity(v___x_610_);
v___x_636_ = lean_array_push(v___x_635_, v___x_631_);
v___x_637_ = lean_array_push(v___x_636_, v___x_633_);
v___x_638_ = lean_array_push(v___x_637_, v___x_634_);
v___x_639_ = l_Lean_Fmt_Layouts_metaApplication(v___x_629_, v___x_638_, v_a_621_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_639_);
v___x_641_ = v___x_624_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_a_622_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
else
{
lean_dec(v_a_616_);
lean_dec(v_a_613_);
lean_dec(v_a_608_);
lean_dec(v_a_605_);
lean_dec(v_a_600_);
lean_del_object(v___x_597_);
lean_del_object(v___x_586_);
return v___x_620_;
}
}
else
{
lean_object* v_a_646_; lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_a_613_);
lean_dec(v_a_608_);
lean_dec(v_a_605_);
lean_dec(v_a_600_);
lean_del_object(v___x_597_);
lean_del_object(v___x_586_);
lean_dec(v_x_563_);
v_a_646_ = lean_ctor_get(v___x_615_, 0);
v_a_647_ = lean_ctor_get(v___x_615_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_615_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_inc(v_a_646_);
lean_dec(v___x_615_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_646_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_dec(v_a_608_);
lean_dec(v_a_605_);
lean_dec(v_a_600_);
lean_del_object(v___x_597_);
lean_dec(v_val_595_);
lean_del_object(v___x_586_);
lean_dec(v_x_563_);
return v___x_612_;
}
}
else
{
lean_object* v_a_655_; lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec(v_a_605_);
lean_dec(v_a_600_);
lean_del_object(v___x_597_);
lean_dec(v_val_595_);
lean_del_object(v___x_586_);
lean_dec(v_x_563_);
v_a_655_ = lean_ctor_get(v___x_607_, 0);
v_a_656_ = lean_ctor_get(v___x_607_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_607_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_inc(v_a_655_);
lean_dec(v___x_607_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_655_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_dec(v_a_600_);
lean_del_object(v___x_597_);
lean_dec(v_val_595_);
lean_del_object(v___x_586_);
lean_dec(v_val_584_);
lean_dec(v_x_563_);
return v___x_604_;
}
}
else
{
lean_del_object(v___x_597_);
lean_dec(v_val_595_);
lean_del_object(v___x_586_);
lean_dec(v_val_584_);
lean_dec(v_x_563_);
return v___x_599_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxBinary___boxed(lean_object* v_x_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Fmt_fmtSyntaxBinary(v_x_666_, v_a_667_, v_a_668_);
lean_dec_ref(v_a_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1(){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = l_Lean_Fmt_fmtAttribute;
v___x_677_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxBinary___closed__1));
v___x_678_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___closed__1));
v___x_679_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntaxBinary___boxed), 3, 0);
v___x_680_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_676_, v___x_677_, v___x_678_, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1___boxed(lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1();
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxSepBy(lean_object* v_x_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxSepBy___closed__1));
lean_inc(v_x_694_);
v___x_698_ = l_Lean_Syntax_isOfKind(v_x_694_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec(v_x_694_);
v___x_699_ = l_Lean_Fmt_Error_partialFormatter;
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v_a_696_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___x_762_; lean_object* v___x_763_; size_t v_sz_764_; size_t v___x_765_; lean_object* v___x_766_; 
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_762_ = l_Lean_Syntax_getArg(v_x_694_, v___x_701_);
v___x_763_ = l_Lean_Syntax_getArgs(v___x_762_);
lean_dec(v___x_762_);
v_sz_764_ = lean_array_size(v___x_763_);
v___x_765_ = ((size_t)0ULL);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(v_sz_764_, v___x_765_, v___x_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v_x_694_);
v___x_767_ = l_Lean_Fmt_Error_partialFormatter;
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v_a_696_);
return v___x_768_;
}
else
{
lean_object* v_val_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_851_; 
v_val_769_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_851_ == 0)
{
v___x_771_ = v___x_766_;
v_isShared_772_ = v_isSharedCheck_851_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_val_769_);
lean_dec(v___x_766_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_851_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_773_ = lean_unsigned_to_nat(3u);
v___x_774_ = l_Lean_Syntax_getArg(v_x_694_, v___x_773_);
v___x_775_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxSepBy___closed__3));
lean_inc(v___x_774_);
v___x_776_ = l_Lean_Syntax_isOfKind(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec(v___x_774_);
lean_del_object(v___x_771_);
lean_dec(v_val_769_);
lean_dec(v_x_694_);
v___x_777_ = l_Lean_Fmt_Error_partialFormatter;
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v_a_696_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; lean_object* v_lbTk_780_; lean_object* v___x_781_; lean_object* v_comma_u2081Tk_782_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v_comma_u2083Tk_x3f_786_; lean_object* v_allowTrailingSepTk_x3f_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v_comma_u2082Tk_x3f_819_; lean_object* v_sepParserArgs_x3f_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_779_ = lean_unsigned_to_nat(0u);
v_lbTk_780_ = l_Lean_Syntax_getArg(v_x_694_, v___x_779_);
v___x_781_ = lean_unsigned_to_nat(2u);
v_comma_u2081Tk_782_ = l_Lean_Syntax_getArg(v_x_694_, v___x_781_);
v___x_836_ = lean_unsigned_to_nat(4u);
v___x_837_ = l_Lean_Syntax_getArg(v_x_694_, v___x_836_);
v___x_838_ = l_Lean_Syntax_isNone(v___x_837_);
if (v___x_838_ == 0)
{
uint8_t v___x_839_; 
lean_inc(v___x_837_);
v___x_839_ = l_Lean_Syntax_matchesNull(v___x_837_, v___x_781_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec(v___x_837_);
lean_dec(v_comma_u2081Tk_782_);
lean_dec(v_lbTk_780_);
lean_dec(v___x_774_);
lean_del_object(v___x_771_);
lean_dec(v_val_769_);
lean_dec(v_x_694_);
v___x_840_ = l_Lean_Fmt_Error_partialFormatter;
v___x_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v_a_696_);
return v___x_841_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; size_t v_sz_844_; lean_object* v___x_845_; 
v___x_842_ = l_Lean_Syntax_getArg(v___x_837_, v___x_701_);
v___x_843_ = l_Lean_Syntax_getArgs(v___x_842_);
lean_dec(v___x_842_);
v_sz_844_ = lean_array_size(v___x_843_);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(v_sz_844_, v___x_765_, v___x_843_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v___x_837_);
lean_dec(v_comma_u2081Tk_782_);
lean_dec(v_lbTk_780_);
lean_dec(v___x_774_);
lean_del_object(v___x_771_);
lean_dec(v_val_769_);
lean_dec(v_x_694_);
v___x_846_ = l_Lean_Fmt_Error_partialFormatter;
v___x_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v_a_696_);
return v___x_847_;
}
else
{
lean_object* v_comma_u2082Tk_x3f_848_; lean_object* v___x_849_; 
v_comma_u2082Tk_x3f_848_ = l_Lean_Syntax_getArg(v___x_837_, v___x_779_);
lean_dec(v___x_837_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v_comma_u2082Tk_x3f_848_);
v_comma_u2082Tk_x3f_819_ = v___x_849_;
v_sepParserArgs_x3f_820_ = v___x_845_;
v___y_821_ = v_a_695_;
v___y_822_ = v_a_696_;
goto v___jp_818_;
}
}
}
else
{
lean_object* v___x_850_; 
lean_dec(v___x_837_);
v___x_850_ = lean_box(0);
v_comma_u2082Tk_x3f_819_ = v___x_850_;
v_sepParserArgs_x3f_820_ = v___x_850_;
v___y_821_ = v_a_695_;
v___y_822_ = v_a_696_;
goto v___jp_818_;
}
v___jp_783_:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_Fmt_fmt(v_lbTk_780_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v_a_792_; lean_object* v___x_793_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
v_a_792_ = lean_ctor_get(v___x_790_, 1);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_790_, 2);
v___x_793_ = l_Lean_Fmt_fmtArray___redArg(v_val_769_, v___y_788_, v_a_792_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v_a_795_; lean_object* v___x_796_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
v_a_795_ = lean_ctor_get(v___x_793_, 1);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_793_, 2);
v___x_796_ = l_Lean_Fmt_fmt(v_comma_u2081Tk_782_, v___y_788_, v_a_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v_a_798_; lean_object* v___x_799_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
v_a_798_ = lean_ctor_get(v___x_796_, 1);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_796_, 2);
v___x_799_ = l_Lean_Fmt_fmt(v___x_774_, v___y_788_, v_a_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v_a_801_; lean_object* v___x_802_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
v_a_801_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_799_, 2);
v___x_802_ = l_Lean_Fmt_fmt_x3f(v___y_785_, v___y_788_, v_a_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v_a_804_; lean_object* v___x_805_; lean_object* v_rbTk_806_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
v_a_804_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_802_, 2);
v___x_805_ = lean_unsigned_to_nat(6u);
v_rbTk_806_ = l_Lean_Syntax_getArg(v_x_694_, v___x_805_);
lean_dec(v_x_694_);
if (lean_obj_tag(v___y_784_) == 0)
{
lean_object* v___x_807_; 
v___x_807_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxSepBy___closed__4));
v___y_703_ = v_allowTrailingSepTk_x3f_787_;
v___y_704_ = v_a_794_;
v___y_705_ = v_a_791_;
v___y_706_ = v_a_800_;
v___y_707_ = v_rbTk_806_;
v___y_708_ = v_a_797_;
v___y_709_ = v___y_788_;
v___y_710_ = v_a_804_;
v___y_711_ = v_a_803_;
v___y_712_ = v_comma_u2083Tk_x3f_786_;
v___y_713_ = v___x_807_;
goto v___jp_702_;
}
else
{
lean_object* v_val_808_; 
v_val_808_ = lean_ctor_get(v___y_784_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v___y_784_, 1);
v___y_703_ = v_allowTrailingSepTk_x3f_787_;
v___y_704_ = v_a_794_;
v___y_705_ = v_a_791_;
v___y_706_ = v_a_800_;
v___y_707_ = v_rbTk_806_;
v___y_708_ = v_a_797_;
v___y_709_ = v___y_788_;
v___y_710_ = v_a_804_;
v___y_711_ = v_a_803_;
v___y_712_ = v_comma_u2083Tk_x3f_786_;
v___y_713_ = v_val_808_;
goto v___jp_702_;
}
}
else
{
lean_dec(v_a_800_);
lean_dec(v_a_797_);
lean_dec(v_a_794_);
lean_dec(v_a_791_);
lean_dec(v_allowTrailingSepTk_x3f_787_);
lean_dec(v_comma_u2083Tk_x3f_786_);
lean_dec(v___y_784_);
lean_dec(v_x_694_);
return v___x_802_;
}
}
else
{
lean_dec(v_a_797_);
lean_dec(v_a_794_);
lean_dec(v_a_791_);
lean_dec(v_allowTrailingSepTk_x3f_787_);
lean_dec(v_comma_u2083Tk_x3f_786_);
lean_dec(v___y_785_);
lean_dec(v___y_784_);
lean_dec(v_x_694_);
return v___x_799_;
}
}
else
{
lean_dec(v_a_794_);
lean_dec(v_a_791_);
lean_dec(v_allowTrailingSepTk_x3f_787_);
lean_dec(v_comma_u2083Tk_x3f_786_);
lean_dec(v___y_785_);
lean_dec(v___y_784_);
lean_dec(v___x_774_);
lean_dec(v_x_694_);
return v___x_796_;
}
}
else
{
lean_object* v_a_809_; lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_a_791_);
lean_dec(v_allowTrailingSepTk_x3f_787_);
lean_dec(v_comma_u2083Tk_x3f_786_);
lean_dec(v___y_785_);
lean_dec(v___y_784_);
lean_dec(v_comma_u2081Tk_782_);
lean_dec(v___x_774_);
lean_dec(v_x_694_);
v_a_809_ = lean_ctor_get(v___x_793_, 0);
v_a_810_ = lean_ctor_get(v___x_793_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_793_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_inc(v_a_809_);
lean_dec(v___x_793_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_809_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_dec(v_allowTrailingSepTk_x3f_787_);
lean_dec(v_comma_u2083Tk_x3f_786_);
lean_dec(v___y_785_);
lean_dec(v___y_784_);
lean_dec(v_comma_u2081Tk_782_);
lean_dec(v___x_774_);
lean_dec(v_val_769_);
lean_dec(v_x_694_);
return v___x_790_;
}
}
v___jp_818_:
{
lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_823_ = lean_unsigned_to_nat(5u);
v___x_824_ = l_Lean_Syntax_getArg(v_x_694_, v___x_823_);
v___x_825_ = l_Lean_Syntax_isNone(v___x_824_);
if (v___x_825_ == 0)
{
uint8_t v___x_826_; 
lean_inc(v___x_824_);
v___x_826_ = l_Lean_Syntax_matchesNull(v___x_824_, v___x_781_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec(v___x_824_);
lean_dec(v_sepParserArgs_x3f_820_);
lean_dec(v_comma_u2082Tk_x3f_819_);
lean_dec(v_comma_u2081Tk_782_);
lean_dec(v_lbTk_780_);
lean_dec(v___x_774_);
lean_del_object(v___x_771_);
lean_dec(v_val_769_);
lean_dec(v_x_694_);
v___x_827_ = l_Lean_Fmt_Error_partialFormatter;
v___x_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___y_822_);
return v___x_828_;
}
else
{
lean_object* v_comma_u2083Tk_x3f_829_; lean_object* v_allowTrailingSepTk_x3f_830_; lean_object* v___x_832_; 
v_comma_u2083Tk_x3f_829_ = l_Lean_Syntax_getArg(v___x_824_, v___x_779_);
v_allowTrailingSepTk_x3f_830_ = l_Lean_Syntax_getArg(v___x_824_, v___x_701_);
lean_dec(v___x_824_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v_comma_u2083Tk_x3f_829_);
v___x_832_ = v___x_771_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_comma_u2083Tk_x3f_829_);
v___x_832_ = v_reuseFailAlloc_834_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; 
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v_allowTrailingSepTk_x3f_830_);
v___y_784_ = v_sepParserArgs_x3f_820_;
v___y_785_ = v_comma_u2082Tk_x3f_819_;
v_comma_u2083Tk_x3f_786_ = v___x_832_;
v_allowTrailingSepTk_x3f_787_ = v___x_833_;
v___y_788_ = v___y_821_;
v___y_789_ = v___y_822_;
goto v___jp_783_;
}
}
}
else
{
lean_object* v___x_835_; 
lean_dec(v___x_824_);
lean_del_object(v___x_771_);
v___x_835_ = lean_box(0);
v___y_784_ = v_sepParserArgs_x3f_820_;
v___y_785_ = v_comma_u2082Tk_x3f_819_;
v_comma_u2083Tk_x3f_786_ = v___x_835_;
v_allowTrailingSepTk_x3f_787_ = v___x_835_;
v___y_788_ = v___y_821_;
v___y_789_ = v___y_822_;
goto v___jp_783_;
}
}
}
}
}
v___jp_702_:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Fmt_fmtArray___redArg(v___y_713_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
v_a_716_ = lean_ctor_get(v___x_714_, 1);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_714_, 2);
v___x_717_ = l_Lean_Fmt_fmt_x3f(v___y_712_, v___y_709_, v_a_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_a_719_; lean_object* v___x_720_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
v_a_719_ = lean_ctor_get(v___x_717_, 1);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_717_, 2);
v___x_720_ = l_Lean_Fmt_fmt_x3f(v___y_703_, v___y_709_, v_a_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v_a_722_; lean_object* v___x_723_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
v_a_722_ = lean_ctor_get(v___x_720_, 1);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_720_, 2);
v___x_723_ = l_Lean_Fmt_fmt(v___y_707_, v___y_709_, v_a_722_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_752_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_a_725_ = lean_ctor_get(v___x_723_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_752_ == 0)
{
v___x_727_ = v___x_723_;
v_isShared_728_ = v_isSharedCheck_752_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_752_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v___y_704_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___y_708_);
v___x_731_ = lean_mk_empty_array_with_capacity(v___x_701_);
lean_inc_ref(v___x_731_);
v___x_732_ = lean_array_push(v___x_731_, v___y_706_);
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___y_711_);
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v_a_715_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v_a_718_);
v___x_737_ = lean_array_push(v___x_731_, v_a_721_);
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
v___x_739_ = lean_unsigned_to_nat(7u);
v___x_740_ = lean_mk_empty_array_with_capacity(v___x_739_);
v___x_741_ = lean_array_push(v___x_740_, v___x_729_);
v___x_742_ = lean_array_push(v___x_741_, v___x_730_);
v___x_743_ = lean_array_push(v___x_742_, v___x_733_);
v___x_744_ = lean_array_push(v___x_743_, v___x_734_);
v___x_745_ = lean_array_push(v___x_744_, v___x_735_);
v___x_746_ = lean_array_push(v___x_745_, v___x_736_);
v___x_747_ = lean_array_push(v___x_746_, v___x_738_);
v___x_748_ = l_Lean_Fmt_Layouts_metaApplication(v___y_705_, v___x_747_, v_a_724_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_748_);
v___x_750_ = v___x_727_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_a_725_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
else
{
lean_dec(v_a_721_);
lean_dec(v_a_718_);
lean_dec(v_a_715_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v___y_704_);
return v___x_723_;
}
}
else
{
lean_dec(v_a_718_);
lean_dec(v_a_715_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v___y_704_);
return v___x_720_;
}
}
else
{
lean_dec(v_a_715_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
return v___x_717_;
}
}
else
{
lean_object* v_a_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
v_a_753_ = lean_ctor_get(v___x_714_, 0);
v_a_754_ = lean_ctor_get(v___x_714_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_714_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_inc(v_a_753_);
lean_dec(v___x_714_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_753_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxSepBy___boxed(lean_object* v_x_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Fmt_fmtSyntaxSepBy(v_x_852_, v_a_853_, v_a_854_);
lean_dec_ref(v_a_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1(){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_862_ = l_Lean_Fmt_fmtAttribute;
v___x_863_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxSepBy___closed__1));
v___x_864_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___closed__1));
v___x_865_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntaxSepBy___boxed), 3, 0);
v___x_866_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_862_, v___x_863_, v___x_864_, v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1___boxed(lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1();
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxSepBy1(lean_object* v_x_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxSepBy1___closed__1));
lean_inc(v_x_875_);
v___x_879_ = l_Lean_Syntax_isOfKind(v_x_875_, v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec(v_x_875_);
v___x_880_ = l_Lean_Fmt_Error_partialFormatter;
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_a_877_);
return v___x_881_;
}
else
{
lean_object* v___x_882_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___x_943_; lean_object* v___x_944_; size_t v_sz_945_; size_t v___x_946_; lean_object* v___x_947_; 
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_943_ = l_Lean_Syntax_getArg(v_x_875_, v___x_882_);
v___x_944_ = l_Lean_Syntax_getArgs(v___x_943_);
lean_dec(v___x_943_);
v_sz_945_ = lean_array_size(v___x_944_);
v___x_946_ = ((size_t)0ULL);
v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(v_sz_945_, v___x_946_, v___x_944_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_x_875_);
v___x_948_ = l_Lean_Fmt_Error_partialFormatter;
v___x_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v_a_877_);
return v___x_949_;
}
else
{
lean_object* v_val_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_1032_; 
v_val_950_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_952_ = v___x_947_;
v_isShared_953_ = v_isSharedCheck_1032_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_val_950_);
lean_dec(v___x_947_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_1032_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_954_ = lean_unsigned_to_nat(3u);
v___x_955_ = l_Lean_Syntax_getArg(v_x_875_, v___x_954_);
v___x_956_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxSepBy___closed__3));
lean_inc(v___x_955_);
v___x_957_ = l_Lean_Syntax_isOfKind(v___x_955_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v___x_955_);
lean_del_object(v___x_952_);
lean_dec(v_val_950_);
lean_dec(v_x_875_);
v___x_958_ = l_Lean_Fmt_Error_partialFormatter;
v___x_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v_a_877_);
return v___x_959_;
}
else
{
lean_object* v___x_960_; lean_object* v_lbTk_961_; lean_object* v___x_962_; lean_object* v_comma_u2081Tk_963_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v_comma_u2083Tk_x3f_967_; lean_object* v_allowTrailingSepTk_x3f_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v_comma_u2082Tk_x3f_1000_; lean_object* v_sepParserArgs_x3f_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v_lbTk_961_ = l_Lean_Syntax_getArg(v_x_875_, v___x_960_);
v___x_962_ = lean_unsigned_to_nat(2u);
v_comma_u2081Tk_963_ = l_Lean_Syntax_getArg(v_x_875_, v___x_962_);
v___x_1017_ = lean_unsigned_to_nat(4u);
v___x_1018_ = l_Lean_Syntax_getArg(v_x_875_, v___x_1017_);
v___x_1019_ = l_Lean_Syntax_isNone(v___x_1018_);
if (v___x_1019_ == 0)
{
uint8_t v___x_1020_; 
lean_inc(v___x_1018_);
v___x_1020_ = l_Lean_Syntax_matchesNull(v___x_1018_, v___x_962_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec(v___x_1018_);
lean_dec(v_comma_u2081Tk_963_);
lean_dec(v_lbTk_961_);
lean_dec(v___x_955_);
lean_del_object(v___x_952_);
lean_dec(v_val_950_);
lean_dec(v_x_875_);
v___x_1021_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v_a_877_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; size_t v_sz_1025_; lean_object* v___x_1026_; 
v___x_1023_ = l_Lean_Syntax_getArg(v___x_1018_, v___x_882_);
v___x_1024_ = l_Lean_Syntax_getArgs(v___x_1023_);
lean_dec(v___x_1023_);
v_sz_1025_ = lean_array_size(v___x_1024_);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(v_sz_1025_, v___x_946_, v___x_1024_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v___x_1018_);
lean_dec(v_comma_u2081Tk_963_);
lean_dec(v_lbTk_961_);
lean_dec(v___x_955_);
lean_del_object(v___x_952_);
lean_dec(v_val_950_);
lean_dec(v_x_875_);
v___x_1027_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v_a_877_);
return v___x_1028_;
}
else
{
lean_object* v_comma_u2082Tk_x3f_1029_; lean_object* v___x_1030_; 
v_comma_u2082Tk_x3f_1029_ = l_Lean_Syntax_getArg(v___x_1018_, v___x_960_);
lean_dec(v___x_1018_);
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v_comma_u2082Tk_x3f_1029_);
v_comma_u2082Tk_x3f_1000_ = v___x_1030_;
v_sepParserArgs_x3f_1001_ = v___x_1026_;
v___y_1002_ = v_a_876_;
v___y_1003_ = v_a_877_;
goto v___jp_999_;
}
}
}
else
{
lean_object* v___x_1031_; 
lean_dec(v___x_1018_);
v___x_1031_ = lean_box(0);
v_comma_u2082Tk_x3f_1000_ = v___x_1031_;
v_sepParserArgs_x3f_1001_ = v___x_1031_;
v___y_1002_ = v_a_876_;
v___y_1003_ = v_a_877_;
goto v___jp_999_;
}
v___jp_964_:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_Fmt_fmt(v_lbTk_961_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v_a_973_; lean_object* v___x_974_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
v_a_973_ = lean_ctor_get(v___x_971_, 1);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_971_, 2);
v___x_974_ = l_Lean_Fmt_fmtArray___redArg(v_val_950_, v___y_969_, v_a_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v_a_976_; lean_object* v___x_977_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
v_a_976_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_974_, 2);
v___x_977_ = l_Lean_Fmt_fmt(v_comma_u2081Tk_963_, v___y_969_, v_a_976_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
v_a_979_ = lean_ctor_get(v___x_977_, 1);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_977_, 2);
v___x_980_ = l_Lean_Fmt_fmt(v___x_955_, v___y_969_, v_a_979_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
v_a_982_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_980_, 2);
v___x_983_ = l_Lean_Fmt_fmt_x3f(v___y_965_, v___y_969_, v_a_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_a_985_; lean_object* v___x_986_; lean_object* v_rbTk_987_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
v_a_985_ = lean_ctor_get(v___x_983_, 1);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_983_, 2);
v___x_986_ = lean_unsigned_to_nat(6u);
v_rbTk_987_ = l_Lean_Syntax_getArg(v_x_875_, v___x_986_);
lean_dec(v_x_875_);
if (lean_obj_tag(v___y_966_) == 0)
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxSepBy___closed__4));
v___y_884_ = v_a_978_;
v___y_885_ = v_a_984_;
v___y_886_ = v_a_981_;
v___y_887_ = v_comma_u2083Tk_x3f_967_;
v___y_888_ = v_a_972_;
v___y_889_ = v_rbTk_987_;
v___y_890_ = v_a_975_;
v___y_891_ = v___y_969_;
v___y_892_ = v_allowTrailingSepTk_x3f_968_;
v___y_893_ = v_a_985_;
v___y_894_ = v___x_988_;
goto v___jp_883_;
}
else
{
lean_object* v_val_989_; 
v_val_989_ = lean_ctor_get(v___y_966_, 0);
lean_inc(v_val_989_);
lean_dec_ref_known(v___y_966_, 1);
v___y_884_ = v_a_978_;
v___y_885_ = v_a_984_;
v___y_886_ = v_a_981_;
v___y_887_ = v_comma_u2083Tk_x3f_967_;
v___y_888_ = v_a_972_;
v___y_889_ = v_rbTk_987_;
v___y_890_ = v_a_975_;
v___y_891_ = v___y_969_;
v___y_892_ = v_allowTrailingSepTk_x3f_968_;
v___y_893_ = v_a_985_;
v___y_894_ = v_val_989_;
goto v___jp_883_;
}
}
else
{
lean_dec(v_a_981_);
lean_dec(v_a_978_);
lean_dec(v_a_975_);
lean_dec(v_a_972_);
lean_dec(v_allowTrailingSepTk_x3f_968_);
lean_dec(v_comma_u2083Tk_x3f_967_);
lean_dec(v___y_966_);
lean_dec(v_x_875_);
return v___x_983_;
}
}
else
{
lean_dec(v_a_978_);
lean_dec(v_a_975_);
lean_dec(v_a_972_);
lean_dec(v_allowTrailingSepTk_x3f_968_);
lean_dec(v_comma_u2083Tk_x3f_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v_x_875_);
return v___x_980_;
}
}
else
{
lean_dec(v_a_975_);
lean_dec(v_a_972_);
lean_dec(v_allowTrailingSepTk_x3f_968_);
lean_dec(v_comma_u2083Tk_x3f_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v___x_955_);
lean_dec(v_x_875_);
return v___x_977_;
}
}
else
{
lean_object* v_a_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_a_972_);
lean_dec(v_allowTrailingSepTk_x3f_968_);
lean_dec(v_comma_u2083Tk_x3f_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v_comma_u2081Tk_963_);
lean_dec(v___x_955_);
lean_dec(v_x_875_);
v_a_990_ = lean_ctor_get(v___x_974_, 0);
v_a_991_ = lean_ctor_get(v___x_974_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_974_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_inc(v_a_990_);
lean_dec(v___x_974_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_990_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
else
{
lean_dec(v_allowTrailingSepTk_x3f_968_);
lean_dec(v_comma_u2083Tk_x3f_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v_comma_u2081Tk_963_);
lean_dec(v___x_955_);
lean_dec(v_val_950_);
lean_dec(v_x_875_);
return v___x_971_;
}
}
v___jp_999_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = lean_unsigned_to_nat(5u);
v___x_1005_ = l_Lean_Syntax_getArg(v_x_875_, v___x_1004_);
v___x_1006_ = l_Lean_Syntax_isNone(v___x_1005_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; 
lean_inc(v___x_1005_);
v___x_1007_ = l_Lean_Syntax_matchesNull(v___x_1005_, v___x_962_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec(v___x_1005_);
lean_dec(v_sepParserArgs_x3f_1001_);
lean_dec(v_comma_u2082Tk_x3f_1000_);
lean_dec(v_comma_u2081Tk_963_);
lean_dec(v_lbTk_961_);
lean_dec(v___x_955_);
lean_del_object(v___x_952_);
lean_dec(v_val_950_);
lean_dec(v_x_875_);
v___x_1008_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___y_1003_);
return v___x_1009_;
}
else
{
lean_object* v_comma_u2083Tk_x3f_1010_; lean_object* v_allowTrailingSepTk_x3f_1011_; lean_object* v___x_1013_; 
v_comma_u2083Tk_x3f_1010_ = l_Lean_Syntax_getArg(v___x_1005_, v___x_960_);
v_allowTrailingSepTk_x3f_1011_ = l_Lean_Syntax_getArg(v___x_1005_, v___x_882_);
lean_dec(v___x_1005_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_comma_u2083Tk_x3f_1010_);
v___x_1013_ = v___x_952_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_comma_u2083Tk_x3f_1010_);
v___x_1013_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_allowTrailingSepTk_x3f_1011_);
v___y_965_ = v_comma_u2082Tk_x3f_1000_;
v___y_966_ = v_sepParserArgs_x3f_1001_;
v_comma_u2083Tk_x3f_967_ = v___x_1013_;
v_allowTrailingSepTk_x3f_968_ = v___x_1014_;
v___y_969_ = v___y_1002_;
v___y_970_ = v___y_1003_;
goto v___jp_964_;
}
}
}
else
{
lean_object* v___x_1016_; 
lean_dec(v___x_1005_);
lean_del_object(v___x_952_);
v___x_1016_ = lean_box(0);
v___y_965_ = v_comma_u2082Tk_x3f_1000_;
v___y_966_ = v_sepParserArgs_x3f_1001_;
v_comma_u2083Tk_x3f_967_ = v___x_1016_;
v_allowTrailingSepTk_x3f_968_ = v___x_1016_;
v___y_969_ = v___y_1002_;
v___y_970_ = v___y_1003_;
goto v___jp_964_;
}
}
}
}
}
v___jp_883_:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_Fmt_fmtArray___redArg(v___y_894_, v___y_891_, v___y_893_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v_a_897_; lean_object* v___x_898_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
v_a_897_ = lean_ctor_get(v___x_895_, 1);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_895_, 2);
v___x_898_ = l_Lean_Fmt_fmt_x3f(v___y_887_, v___y_891_, v_a_897_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v_a_900_; lean_object* v___x_901_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
v_a_900_ = lean_ctor_get(v___x_898_, 1);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_898_, 2);
v___x_901_ = l_Lean_Fmt_fmt_x3f(v___y_892_, v___y_891_, v_a_900_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v_a_903_; lean_object* v___x_904_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
v_a_903_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_901_, 2);
v___x_904_ = l_Lean_Fmt_fmt(v___y_889_, v___y_891_, v_a_903_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_933_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_a_906_ = lean_ctor_get(v___x_904_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_933_ == 0)
{
v___x_908_ = v___x_904_;
v_isShared_909_ = v_isSharedCheck_933_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_933_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v___y_890_);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___y_884_);
v___x_912_ = lean_mk_empty_array_with_capacity(v___x_882_);
lean_inc_ref(v___x_912_);
v___x_913_ = lean_array_push(v___x_912_, v___y_886_);
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___y_885_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v_a_896_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v_a_899_);
v___x_918_ = lean_array_push(v___x_912_, v_a_902_);
v___x_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
v___x_920_ = lean_unsigned_to_nat(7u);
v___x_921_ = lean_mk_empty_array_with_capacity(v___x_920_);
v___x_922_ = lean_array_push(v___x_921_, v___x_910_);
v___x_923_ = lean_array_push(v___x_922_, v___x_911_);
v___x_924_ = lean_array_push(v___x_923_, v___x_914_);
v___x_925_ = lean_array_push(v___x_924_, v___x_915_);
v___x_926_ = lean_array_push(v___x_925_, v___x_916_);
v___x_927_ = lean_array_push(v___x_926_, v___x_917_);
v___x_928_ = lean_array_push(v___x_927_, v___x_919_);
v___x_929_ = l_Lean_Fmt_Layouts_metaApplication(v___y_888_, v___x_928_, v_a_905_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_929_);
v___x_931_ = v___x_908_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_a_906_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
else
{
lean_dec(v_a_902_);
lean_dec(v_a_899_);
lean_dec(v_a_896_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v___y_888_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v___y_884_);
return v___x_904_;
}
}
else
{
lean_dec(v_a_899_);
lean_dec(v_a_896_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v___y_884_);
return v___x_901_;
}
}
else
{
lean_dec(v_a_896_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v___y_884_);
return v___x_898_;
}
}
else
{
lean_object* v_a_934_; lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v___y_892_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v___y_884_);
v_a_934_ = lean_ctor_get(v___x_895_, 0);
v_a_935_ = lean_ctor_get(v___x_895_, 1);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_895_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_inc(v_a_934_);
lean_dec(v___x_895_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_934_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxSepBy1___boxed(lean_object* v_x_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Fmt_fmtSyntaxSepBy1(v_x_1033_, v_a_1034_, v_a_1035_);
lean_dec_ref(v_a_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1(){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1043_ = l_Lean_Fmt_fmtAttribute;
v___x_1044_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxSepBy1___closed__1));
v___x_1045_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___closed__1));
v___x_1046_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntaxSepBy1___boxed), 3, 0);
v___x_1047_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1043_, v___x_1044_, v___x_1045_, v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1___boxed(lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1();
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxAtom(lean_object* v_x_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxAtom___closed__1));
lean_inc(v_x_1056_);
v___x_1060_ = l_Lean_Syntax_isOfKind(v_x_1056_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_dec(v_x_1056_);
v___x_1061_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v_a_1058_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = l_Lean_Syntax_getArg(v_x_1056_, v___x_1063_);
lean_dec(v_x_1056_);
v___x_1065_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxSepBy___closed__3));
lean_inc(v___x_1064_);
v___x_1066_ = l_Lean_Syntax_isOfKind(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_dec(v___x_1064_);
v___x_1067_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v_a_1058_);
return v___x_1068_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Fmt_fmt(v___x_1064_, v_a_1057_, v_a_1058_);
return v___x_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxAtom___boxed(lean_object* v_x_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_Fmt_fmtSyntaxAtom(v_x_1070_, v_a_1071_, v_a_1072_);
lean_dec_ref(v_a_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1(){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1080_ = l_Lean_Fmt_fmtAttribute;
v___x_1081_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxAtom___closed__1));
v___x_1082_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___closed__1));
v___x_1083_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntaxAtom___boxed), 3, 0);
v___x_1084_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1080_, v___x_1081_, v___x_1082_, v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1___boxed(lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1();
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxNonReserved(lean_object* v_x_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxNonReserved___closed__1));
lean_inc(v_x_1093_);
v___x_1097_ = l_Lean_Syntax_isOfKind(v_x_1093_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec(v_x_1093_);
v___x_1098_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_a_1095_);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1100_ = lean_unsigned_to_nat(1u);
v___x_1101_ = l_Lean_Syntax_getArg(v_x_1093_, v___x_1100_);
v___x_1102_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxSepBy___closed__3));
lean_inc(v___x_1101_);
v___x_1103_ = l_Lean_Syntax_isOfKind(v___x_1101_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v___x_1101_);
lean_dec(v_x_1093_);
v___x_1104_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_a_1095_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; lean_object* v_ampTk_1107_; lean_object* v___x_1108_; 
v___x_1106_ = lean_unsigned_to_nat(0u);
v_ampTk_1107_ = l_Lean_Syntax_getArg(v_x_1093_, v___x_1106_);
lean_dec(v_x_1093_);
v___x_1108_ = l_Lean_Fmt_fmt(v_ampTk_1107_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v_a_1110_; lean_object* v___x_1111_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
v_a_1110_ = lean_ctor_get(v___x_1108_, 1);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1108_, 2);
v___x_1111_ = l_Lean_Fmt_fmt(v___x_1101_, v_a_1094_, v_a_1110_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1125_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_a_1113_ = lean_ctor_get(v___x_1111_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1115_ = v___x_1111_;
v_isShared_1116_ = v_isSharedCheck_1125_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1125_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1117_ = lean_unsigned_to_nat(2u);
v___x_1118_ = lean_mk_empty_array_with_capacity(v___x_1117_);
v___x_1119_ = lean_array_push(v___x_1118_, v_a_1109_);
v___x_1120_ = lean_array_push(v___x_1119_, v_a_1112_);
v___x_1121_ = l_Lean_Fmt_Layouts_atomic(v___x_1120_);
lean_dec_ref(v___x_1120_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1121_);
v___x_1123_ = v___x_1115_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_a_1113_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_dec(v_a_1109_);
return v___x_1111_;
}
}
else
{
lean_dec(v___x_1101_);
return v___x_1108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxNonReserved___boxed(lean_object* v_x_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Fmt_fmtSyntaxNonReserved(v_x_1126_, v_a_1127_, v_a_1128_);
lean_dec_ref(v_a_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1(){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1136_ = l_Lean_Fmt_fmtAttribute;
v___x_1137_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxNonReserved___closed__1));
v___x_1138_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___closed__1));
v___x_1139_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntaxNonReserved___boxed), 3, 0);
v___x_1140_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1136_, v___x_1137_, v___x_1138_, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1___boxed(lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1();
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxUnicodeAtom(lean_object* v_x_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__1));
lean_inc(v_x_1149_);
v___x_1153_ = l_Lean_Syntax_isOfKind(v_x_1149_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v_x_1149_);
v___x_1154_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v_a_1151_);
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = l_Lean_Syntax_getArg(v_x_1149_, v___x_1156_);
v___x_1158_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxSepBy___closed__3));
lean_inc(v___x_1157_);
v___x_1159_ = l_Lean_Syntax_isOfKind(v___x_1157_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v___x_1157_);
lean_dec(v_x_1149_);
v___x_1160_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v_a_1151_);
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1162_ = lean_unsigned_to_nat(3u);
v___x_1163_ = l_Lean_Syntax_getArg(v_x_1149_, v___x_1162_);
lean_inc(v___x_1163_);
v___x_1164_ = l_Lean_Syntax_isOfKind(v___x_1163_, v___x_1158_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec(v___x_1163_);
lean_dec(v___x_1157_);
lean_dec(v_x_1149_);
v___x_1165_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v_a_1151_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; lean_object* v_lbTk_1168_; lean_object* v___x_1169_; lean_object* v_comma_u2081Tk_1170_; lean_object* v_comma_u2082Tk_x3f_1172_; lean_object* v_preserveForPPTk_x3f_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1167_ = lean_unsigned_to_nat(0u);
v_lbTk_1168_ = l_Lean_Syntax_getArg(v_x_1149_, v___x_1167_);
v___x_1169_ = lean_unsigned_to_nat(2u);
v_comma_u2081Tk_1170_ = l_Lean_Syntax_getArg(v_x_1149_, v___x_1169_);
v___x_1222_ = lean_unsigned_to_nat(4u);
v___x_1223_ = l_Lean_Syntax_getArg(v_x_1149_, v___x_1222_);
v___x_1224_ = l_Lean_Syntax_isNone(v___x_1223_);
if (v___x_1224_ == 0)
{
uint8_t v___x_1225_; 
lean_inc(v___x_1223_);
v___x_1225_ = l_Lean_Syntax_matchesNull(v___x_1223_, v___x_1169_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec(v___x_1223_);
lean_dec(v_comma_u2081Tk_1170_);
lean_dec(v_lbTk_1168_);
lean_dec(v___x_1163_);
lean_dec(v___x_1157_);
lean_dec(v_x_1149_);
v___x_1226_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_a_1151_);
return v___x_1227_;
}
else
{
lean_object* v_comma_u2082Tk_x3f_1228_; lean_object* v_preserveForPPTk_x3f_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_comma_u2082Tk_x3f_1228_ = l_Lean_Syntax_getArg(v___x_1223_, v___x_1167_);
v_preserveForPPTk_x3f_1229_ = l_Lean_Syntax_getArg(v___x_1223_, v___x_1156_);
lean_dec(v___x_1223_);
v___x_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1230_, 0, v_comma_u2082Tk_x3f_1228_);
v___x_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_preserveForPPTk_x3f_1229_);
v_comma_u2082Tk_x3f_1172_ = v___x_1230_;
v_preserveForPPTk_x3f_1173_ = v___x_1231_;
v___y_1174_ = v_a_1150_;
v___y_1175_ = v_a_1151_;
goto v___jp_1171_;
}
}
else
{
lean_object* v___x_1232_; 
lean_dec(v___x_1223_);
v___x_1232_ = lean_box(0);
v_comma_u2082Tk_x3f_1172_ = v___x_1232_;
v_preserveForPPTk_x3f_1173_ = v___x_1232_;
v___y_1174_ = v_a_1150_;
v___y_1175_ = v_a_1151_;
goto v___jp_1171_;
}
v___jp_1171_:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_Fmt_fmt(v_lbTk_1168_, v___y_1174_, v___y_1175_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v_a_1178_; lean_object* v___x_1179_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
v_a_1178_ = lean_ctor_get(v___x_1176_, 1);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1176_, 2);
v___x_1179_ = l_Lean_Fmt_fmt(v___x_1157_, v___y_1174_, v_a_1178_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v_a_1181_; lean_object* v___x_1182_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
v_a_1181_ = lean_ctor_get(v___x_1179_, 1);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1179_, 2);
v___x_1182_ = l_Lean_Fmt_fmt(v_comma_u2081Tk_1170_, v___y_1174_, v_a_1181_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v_a_1184_; lean_object* v___x_1185_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
v_a_1184_ = lean_ctor_get(v___x_1182_, 1);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1182_, 2);
v___x_1185_ = l_Lean_Fmt_fmt(v___x_1163_, v___y_1174_, v_a_1184_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v_a_1187_; lean_object* v___x_1188_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
v_a_1187_ = lean_ctor_get(v___x_1185_, 1);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1185_, 2);
v___x_1188_ = l_Lean_Fmt_fmt_x3f(v_comma_u2082Tk_x3f_1172_, v___y_1174_, v_a_1187_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v_a_1190_; lean_object* v___x_1191_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
v_a_1190_ = lean_ctor_get(v___x_1188_, 1);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1188_, 2);
v___x_1191_ = l_Lean_Fmt_fmt_x3f(v_preserveForPPTk_x3f_1173_, v___y_1174_, v_a_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v_a_1193_; lean_object* v___x_1194_; lean_object* v_rbTk_1195_; lean_object* v___x_1196_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
v_a_1193_ = lean_ctor_get(v___x_1191_, 1);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1191_, 2);
v___x_1194_ = lean_unsigned_to_nat(5u);
v_rbTk_1195_ = l_Lean_Syntax_getArg(v_x_1149_, v___x_1194_);
lean_dec(v_x_1149_);
v___x_1196_ = l_Lean_Fmt_fmt(v_rbTk_1195_, v___y_1174_, v_a_1193_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1221_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_a_1198_ = lean_ctor_get(v___x_1196_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1200_ = v___x_1196_;
v_isShared_1201_ = v_isSharedCheck_1221_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1221_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1202_ = lean_mk_empty_array_with_capacity(v___x_1156_);
lean_inc_ref_n(v___x_1202_, 2);
v___x_1203_ = lean_array_push(v___x_1202_, v_a_1180_);
v___x_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_a_1183_);
v___x_1206_ = lean_array_push(v___x_1202_, v_a_1186_);
v___x_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_a_1189_);
v___x_1209_ = lean_array_push(v___x_1202_, v_a_1192_);
v___x_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
v___x_1211_ = lean_mk_empty_array_with_capacity(v___x_1194_);
v___x_1212_ = lean_array_push(v___x_1211_, v___x_1204_);
v___x_1213_ = lean_array_push(v___x_1212_, v___x_1205_);
v___x_1214_ = lean_array_push(v___x_1213_, v___x_1207_);
v___x_1215_ = lean_array_push(v___x_1214_, v___x_1208_);
v___x_1216_ = lean_array_push(v___x_1215_, v___x_1210_);
v___x_1217_ = l_Lean_Fmt_Layouts_metaApplication(v_a_1177_, v___x_1216_, v_a_1197_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1217_);
v___x_1219_ = v___x_1200_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_a_1198_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_dec(v_a_1192_);
lean_dec(v_a_1189_);
lean_dec(v_a_1186_);
lean_dec(v_a_1183_);
lean_dec(v_a_1180_);
lean_dec(v_a_1177_);
return v___x_1196_;
}
}
else
{
lean_dec(v_a_1189_);
lean_dec(v_a_1186_);
lean_dec(v_a_1183_);
lean_dec(v_a_1180_);
lean_dec(v_a_1177_);
lean_dec(v_x_1149_);
return v___x_1191_;
}
}
else
{
lean_dec(v_a_1186_);
lean_dec(v_a_1183_);
lean_dec(v_a_1180_);
lean_dec(v_a_1177_);
lean_dec(v_preserveForPPTk_x3f_1173_);
lean_dec(v_x_1149_);
return v___x_1188_;
}
}
else
{
lean_dec(v_a_1183_);
lean_dec(v_a_1180_);
lean_dec(v_a_1177_);
lean_dec(v_preserveForPPTk_x3f_1173_);
lean_dec(v_comma_u2082Tk_x3f_1172_);
lean_dec(v_x_1149_);
return v___x_1185_;
}
}
else
{
lean_dec(v_a_1180_);
lean_dec(v_a_1177_);
lean_dec(v_preserveForPPTk_x3f_1173_);
lean_dec(v_comma_u2082Tk_x3f_1172_);
lean_dec(v___x_1163_);
lean_dec(v_x_1149_);
return v___x_1182_;
}
}
else
{
lean_dec(v_a_1177_);
lean_dec(v_preserveForPPTk_x3f_1173_);
lean_dec(v_comma_u2082Tk_x3f_1172_);
lean_dec(v_comma_u2081Tk_1170_);
lean_dec(v___x_1163_);
lean_dec(v_x_1149_);
return v___x_1179_;
}
}
else
{
lean_dec(v_preserveForPPTk_x3f_1173_);
lean_dec(v_comma_u2082Tk_x3f_1172_);
lean_dec(v_comma_u2081Tk_1170_);
lean_dec(v___x_1163_);
lean_dec(v___x_1157_);
lean_dec(v_x_1149_);
return v___x_1176_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxUnicodeAtom___boxed(lean_object* v_x_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Fmt_fmtSyntaxUnicodeAtom(v_x_1233_, v_a_1234_, v_a_1235_);
lean_dec_ref(v_a_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1(){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1243_ = l_Lean_Fmt_fmtAttribute;
v___x_1244_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxUnicodeAtom___closed__1));
v___x_1245_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___closed__1));
v___x_1246_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntaxUnicodeAtom___boxed), 3, 0);
v___x_1247_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1243_, v___x_1244_, v___x_1245_, v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1___boxed(lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1();
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNamedName(lean_object* v_x_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Lean_Fmt_fmtNamedName___closed__2));
lean_inc(v_x_1257_);
v___x_1261_ = l_Lean_Syntax_isOfKind(v_x_1257_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec(v_x_1257_);
v___x_1262_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v_a_1259_);
return v___x_1263_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1264_ = lean_unsigned_to_nat(3u);
v___x_1265_ = l_Lean_Syntax_getArg(v_x_1257_, v___x_1264_);
v___x_1266_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v___x_1265_);
v___x_1267_ = l_Lean_Syntax_isOfKind(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec(v___x_1265_);
lean_dec(v_x_1257_);
v___x_1268_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v_a_1259_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; lean_object* v_lbTk_1271_; lean_object* v___x_1272_; lean_object* v_nameTk_1273_; lean_object* v___x_1274_; lean_object* v_colonEqTk_1275_; lean_object* v___x_1276_; lean_object* v_rbTk_1277_; lean_object* v___x_1278_; 
v___x_1270_ = lean_unsigned_to_nat(0u);
v_lbTk_1271_ = l_Lean_Syntax_getArg(v_x_1257_, v___x_1270_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v_nameTk_1273_ = l_Lean_Syntax_getArg(v_x_1257_, v___x_1272_);
v___x_1274_ = lean_unsigned_to_nat(2u);
v_colonEqTk_1275_ = l_Lean_Syntax_getArg(v_x_1257_, v___x_1274_);
v___x_1276_ = lean_unsigned_to_nat(4u);
v_rbTk_1277_ = l_Lean_Syntax_getArg(v_x_1257_, v___x_1276_);
lean_dec(v_x_1257_);
v___x_1278_ = l_Lean_Fmt_fmtNamedArgumentTerm(v_lbTk_1271_, v_nameTk_1273_, v_colonEqTk_1275_, v___x_1265_, v_rbTk_1277_, v_a_1258_, v_a_1259_);
return v___x_1278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNamedName___boxed(lean_object* v_x_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_Fmt_fmtNamedName(v_x_1279_, v_a_1280_, v_a_1281_);
lean_dec_ref(v_a_1280_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1(){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1289_ = l_Lean_Fmt_fmtAttribute;
v___x_1290_ = ((lean_object*)(l_Lean_Fmt_fmtNamedName___closed__2));
v___x_1291_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___closed__1));
v___x_1292_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtNamedName___boxed), 3, 0);
v___x_1293_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1289_, v___x_1290_, v___x_1291_, v___x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1___boxed(lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1();
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIdentPrec(lean_object* v_x_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = ((lean_object*)(l_Lean_Fmt_fmtIdentPrec___closed__1));
lean_inc(v_x_1302_);
v___x_1323_ = l_Lean_Syntax_isOfKind(v_x_1302_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec(v_x_1302_);
v___x_1324_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v_a_1304_);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_prec_x3f_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1326_ = lean_unsigned_to_nat(0u);
v___x_1327_ = l_Lean_Syntax_getArg(v_x_1302_, v___x_1326_);
v___x_1346_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v___x_1327_);
v___x_1347_ = l_Lean_Syntax_isOfKind(v___x_1327_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec(v___x_1327_);
lean_dec(v_x_1302_);
v___x_1348_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v_a_1304_);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = l_Lean_Syntax_getArg(v_x_1302_, v___x_1350_);
lean_dec(v_x_1302_);
v___x_1352_ = l_Lean_Syntax_isNone(v___x_1351_);
if (v___x_1352_ == 0)
{
uint8_t v___x_1353_; 
lean_inc(v___x_1351_);
v___x_1353_ = l_Lean_Syntax_matchesNull(v___x_1351_, v___x_1350_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v___x_1351_);
lean_dec(v___x_1327_);
v___x_1354_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v_a_1304_);
return v___x_1355_;
}
else
{
lean_object* v_prec_x3f_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_prec_x3f_1356_ = l_Lean_Syntax_getArg(v___x_1351_, v___x_1326_);
lean_dec(v___x_1351_);
v___x_1357_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__3));
lean_inc(v_prec_x3f_1356_);
v___x_1358_ = l_Lean_Syntax_isOfKind(v_prec_x3f_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec(v_prec_x3f_1356_);
lean_dec(v___x_1327_);
v___x_1359_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v_a_1304_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1361_, 0, v_prec_x3f_1356_);
v_prec_x3f_1329_ = v___x_1361_;
v___y_1330_ = v_a_1303_;
v___y_1331_ = v_a_1304_;
goto v___jp_1328_;
}
}
}
else
{
lean_object* v___x_1362_; 
lean_dec(v___x_1351_);
v___x_1362_ = lean_box(0);
v_prec_x3f_1329_ = v___x_1362_;
v___y_1330_ = v_a_1303_;
v___y_1331_ = v_a_1304_;
goto v___jp_1328_;
}
}
v___jp_1328_:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Fmt_fmt(v___x_1327_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1332_) == 0)
{
if (lean_obj_tag(v_prec_x3f_1329_) == 0)
{
lean_object* v_a_1333_; lean_object* v_a_1334_; lean_object* v___x_1335_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
v_a_1334_ = lean_ctor_get(v___x_1332_, 1);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1332_, 2);
v___x_1335_ = lean_box(0);
v___y_1306_ = v_a_1334_;
v___y_1307_ = v___y_1330_;
v___y_1308_ = v_a_1333_;
v___y_1309_ = v___x_1335_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1336_; lean_object* v_a_1337_; lean_object* v_val_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
v_a_1336_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1336_);
v_a_1337_ = lean_ctor_get(v___x_1332_, 1);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1332_, 2);
v_val_1338_ = lean_ctor_get(v_prec_x3f_1329_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_prec_x3f_1329_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v_prec_x3f_1329_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_val_1338_);
lean_dec(v_prec_x3f_1329_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_val_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
v___y_1306_ = v_a_1337_;
v___y_1307_ = v___y_1330_;
v___y_1308_ = v_a_1336_;
v___y_1309_ = v___x_1343_;
goto v___jp_1305_;
}
}
}
}
else
{
lean_dec(v_prec_x3f_1329_);
return v___x_1332_;
}
}
}
v___jp_1305_:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_Fmt_fmt_x3f(v___y_1309_, v___y_1307_, v___y_1306_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1321_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_a_1312_ = lean_ctor_get(v___x_1310_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1314_ = v___x_1310_;
v_isShared_1315_ = v_isSharedCheck_1321_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1321_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1316_ = 0;
v___x_1317_ = l_Lean_Fmt_Layouts_prefixOperator(v___y_1308_, v_a_1311_, v___x_1316_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1317_);
v___x_1319_ = v___x_1314_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_a_1312_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
else
{
lean_dec_ref(v___y_1308_);
return v___x_1310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIdentPrec___boxed(lean_object* v_x_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Fmt_fmtIdentPrec(v_x_1363_, v_a_1364_, v_a_1365_);
lean_dec_ref(v_a_1364_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1(){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1373_ = l_Lean_Fmt_fmtAttribute;
v___x_1374_ = ((lean_object*)(l_Lean_Fmt_fmtIdentPrec___closed__1));
v___x_1375_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___closed__1));
v___x_1376_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtIdentPrec___boxed), 3, 0);
v___x_1377_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1373_, v___x_1374_, v___x_1375_, v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1___boxed(lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1();
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefix(lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Fmt_fmtAtomic(v_a_1380_, v_a_1381_, v_a_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefix___boxed(lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Fmt_fmtPrefix(v_a_1384_, v_a_1385_, v_a_1386_);
lean_dec_ref(v_a_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1(){
_start:
{
lean_object* v___f_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___f_1401_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__0));
v___x_1402_ = l_Lean_Fmt_fmtAttribute;
v___x_1403_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__2));
v___x_1404_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__4));
v___x_1405_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1402_, v___x_1403_, v___x_1404_, v___f_1401_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___boxed(lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1();
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfix(lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_Fmt_fmtAtomic(v_a_1408_, v_a_1409_, v_a_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfix___boxed(lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Fmt_fmtInfix(v_a_1412_, v_a_1413_, v_a_1414_);
lean_dec_ref(v_a_1413_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1(){
_start:
{
lean_object* v___f_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___f_1428_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__0));
v___x_1429_ = l_Lean_Fmt_fmtAttribute;
v___x_1430_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__1));
v___x_1431_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___closed__3));
v___x_1432_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1429_, v___x_1430_, v___x_1431_, v___f_1428_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1___boxed(lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1();
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixl(lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Fmt_fmtAtomic(v_a_1435_, v_a_1436_, v_a_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixl___boxed(lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_Fmt_fmtInfixl(v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec_ref(v_a_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1(){
_start:
{
lean_object* v___f_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___f_1455_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__0));
v___x_1456_ = l_Lean_Fmt_fmtAttribute;
v___x_1457_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__1));
v___x_1458_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___closed__3));
v___x_1459_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1456_, v___x_1457_, v___x_1458_, v___f_1455_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1___boxed(lean_object* v_a_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1();
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixr(lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_Fmt_fmtAtomic(v_a_1462_, v_a_1463_, v_a_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixr___boxed(lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Fmt_fmtInfixr(v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec_ref(v_a_1467_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1(){
_start:
{
lean_object* v___f_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___f_1482_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__0));
v___x_1483_ = l_Lean_Fmt_fmtAttribute;
v___x_1484_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__1));
v___x_1485_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___closed__3));
v___x_1486_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1483_, v___x_1484_, v___x_1485_, v___f_1482_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1___boxed(lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1();
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfix(lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_Fmt_fmtAtomic(v_a_1489_, v_a_1490_, v_a_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfix___boxed(lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Fmt_fmtPostfix(v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec_ref(v_a_1494_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1(){
_start:
{
lean_object* v___f_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___f_1509_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__0));
v___x_1510_ = l_Lean_Fmt_fmtAttribute;
v___x_1511_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__1));
v___x_1512_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___closed__3));
v___x_1513_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1510_, v___x_1511_, v___x_1512_, v___f_1509_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1___boxed(lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1();
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMixfix(lean_object* v_x_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v_namedPrio_x3f_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; 
v___x_1550_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__1));
lean_inc(v_x_1547_);
v___x_1551_ = l_Lean_Syntax_isOfKind(v_x_1547_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec(v_x_1547_);
v___x_1640_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v_a_1549_);
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v_namedName_x3f_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v_attributes_x3f_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v_docComment_x3f_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1642_ = lean_unsigned_to_nat(0u);
v___x_1717_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1642_);
v___x_1718_ = l_Lean_Syntax_isNone(v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1717_);
v___x_1720_ = l_Lean_Syntax_matchesNull(v___x_1717_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec(v___x_1717_);
lean_dec(v_x_1547_);
v___x_1721_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v_a_1549_);
return v___x_1722_;
}
else
{
lean_object* v_docComment_x3f_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v_docComment_x3f_1723_ = l_Lean_Syntax_getArg(v___x_1717_, v___x_1642_);
lean_dec(v___x_1717_);
v___x_1724_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__10));
lean_inc(v_docComment_x3f_1723_);
v___x_1725_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_1723_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec(v_docComment_x3f_1723_);
lean_dec(v_x_1547_);
v___x_1726_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v_a_1549_);
return v___x_1727_;
}
else
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_docComment_x3f_1723_);
v_docComment_x3f_1701_ = v___x_1728_;
v___y_1702_ = v_a_1548_;
v___y_1703_ = v_a_1549_;
goto v___jp_1700_;
}
}
}
else
{
lean_object* v___x_1729_; 
lean_dec(v___x_1717_);
v___x_1729_ = lean_box(0);
v_docComment_x3f_1701_ = v___x_1729_;
v___y_1702_ = v_a_1548_;
v___y_1703_ = v_a_1549_;
goto v___jp_1700_;
}
v___jp_1643_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1654_ = lean_unsigned_to_nat(6u);
v___x_1655_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1654_);
v___x_1656_ = l_Lean_Syntax_isNone(v___x_1655_);
if (v___x_1656_ == 0)
{
uint8_t v___x_1657_; 
lean_inc(v___x_1655_);
v___x_1657_ = l_Lean_Syntax_matchesNull(v___x_1655_, v___y_1646_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec(v___x_1655_);
lean_dec(v_namedName_x3f_1651_);
lean_dec(v___y_1650_);
lean_dec(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec(v_x_1547_);
v___x_1658_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v___y_1653_);
return v___x_1659_;
}
else
{
lean_object* v_namedPrio_x3f_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_namedPrio_x3f_1660_ = l_Lean_Syntax_getArg(v___x_1655_, v___x_1642_);
lean_dec(v___x_1655_);
v___x_1661_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__3));
lean_inc(v_namedPrio_x3f_1660_);
v___x_1662_ = l_Lean_Syntax_isOfKind(v_namedPrio_x3f_1660_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec(v_namedPrio_x3f_1660_);
lean_dec(v_namedName_x3f_1651_);
lean_dec(v___y_1650_);
lean_dec(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec(v_x_1547_);
v___x_1663_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v___y_1653_);
return v___x_1664_;
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1665_, 0, v_namedPrio_x3f_1660_);
v___y_1614_ = v___y_1644_;
v___y_1615_ = v___y_1645_;
v___y_1616_ = v_namedName_x3f_1651_;
v___y_1617_ = v___y_1646_;
v___y_1618_ = v___y_1647_;
v___y_1619_ = v___y_1648_;
v___y_1620_ = v___y_1649_;
v___y_1621_ = v___y_1650_;
v_namedPrio_x3f_1622_ = v___x_1665_;
v___y_1623_ = v___y_1652_;
v___y_1624_ = v___y_1653_;
goto v___jp_1613_;
}
}
}
else
{
lean_object* v___x_1666_; 
lean_dec(v___x_1655_);
v___x_1666_ = lean_box(0);
v___y_1614_ = v___y_1644_;
v___y_1615_ = v___y_1645_;
v___y_1616_ = v_namedName_x3f_1651_;
v___y_1617_ = v___y_1646_;
v___y_1618_ = v___y_1647_;
v___y_1619_ = v___y_1648_;
v___y_1620_ = v___y_1649_;
v___y_1621_ = v___y_1650_;
v_namedPrio_x3f_1622_ = v___x_1666_;
v___y_1623_ = v___y_1652_;
v___y_1624_ = v___y_1653_;
goto v___jp_1613_;
}
}
v___jp_1667_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1673_ = lean_unsigned_to_nat(2u);
v___x_1674_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1673_);
v___x_1675_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__6));
lean_inc(v___x_1674_);
v___x_1676_ = l_Lean_Syntax_isOfKind(v___x_1674_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v___x_1674_);
lean_dec(v_attributes_x3f_1670_);
lean_dec(v___y_1669_);
lean_dec(v_x_1547_);
v___x_1677_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v___y_1672_);
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1679_ = lean_unsigned_to_nat(4u);
v___x_1680_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1679_);
v___x_1681_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__3));
lean_inc(v___x_1680_);
v___x_1682_ = l_Lean_Syntax_isOfKind(v___x_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec(v___x_1680_);
lean_dec(v___x_1674_);
lean_dec(v_attributes_x3f_1670_);
lean_dec(v___y_1669_);
lean_dec(v_x_1547_);
v___x_1683_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
lean_ctor_set(v___x_1684_, 1, v___y_1672_);
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1685_ = lean_unsigned_to_nat(3u);
v___x_1686_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1685_);
v___x_1687_ = lean_unsigned_to_nat(5u);
v___x_1688_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1687_);
v___x_1689_ = l_Lean_Syntax_isNone(v___x_1688_);
if (v___x_1689_ == 0)
{
uint8_t v___x_1690_; 
lean_inc(v___x_1688_);
v___x_1690_ = l_Lean_Syntax_matchesNull(v___x_1688_, v___y_1668_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v___x_1688_);
lean_dec(v___x_1686_);
lean_dec(v___x_1680_);
lean_dec(v___x_1674_);
lean_dec(v_attributes_x3f_1670_);
lean_dec(v___y_1669_);
lean_dec(v_x_1547_);
v___x_1691_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v___y_1672_);
return v___x_1692_;
}
else
{
lean_object* v_namedName_x3f_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v_namedName_x3f_1693_ = l_Lean_Syntax_getArg(v___x_1688_, v___x_1642_);
lean_dec(v___x_1688_);
v___x_1694_ = ((lean_object*)(l_Lean_Fmt_fmtNamedName___closed__2));
lean_inc(v_namedName_x3f_1693_);
v___x_1695_ = l_Lean_Syntax_isOfKind(v_namedName_x3f_1693_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec(v_namedName_x3f_1693_);
lean_dec(v___x_1686_);
lean_dec(v___x_1680_);
lean_dec(v___x_1674_);
lean_dec(v_attributes_x3f_1670_);
lean_dec(v___y_1669_);
lean_dec(v_x_1547_);
v___x_1696_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v___y_1672_);
return v___x_1697_;
}
else
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1698_, 0, v_namedName_x3f_1693_);
v___y_1644_ = v___x_1686_;
v___y_1645_ = v___x_1680_;
v___y_1646_ = v___y_1668_;
v___y_1647_ = v___y_1669_;
v___y_1648_ = v___x_1674_;
v___y_1649_ = v___x_1673_;
v___y_1650_ = v_attributes_x3f_1670_;
v_namedName_x3f_1651_ = v___x_1698_;
v___y_1652_ = v___y_1671_;
v___y_1653_ = v___y_1672_;
goto v___jp_1643_;
}
}
}
else
{
lean_object* v___x_1699_; 
lean_dec(v___x_1688_);
v___x_1699_ = lean_box(0);
v___y_1644_ = v___x_1686_;
v___y_1645_ = v___x_1680_;
v___y_1646_ = v___y_1668_;
v___y_1647_ = v___y_1669_;
v___y_1648_ = v___x_1674_;
v___y_1649_ = v___x_1673_;
v___y_1650_ = v_attributes_x3f_1670_;
v_namedName_x3f_1651_ = v___x_1699_;
v___y_1652_ = v___y_1671_;
v___y_1653_ = v___y_1672_;
goto v___jp_1643_;
}
}
}
}
v___jp_1700_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1704_ = lean_unsigned_to_nat(1u);
v___x_1705_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1704_);
v___x_1706_ = l_Lean_Syntax_isNone(v___x_1705_);
if (v___x_1706_ == 0)
{
uint8_t v___x_1707_; 
lean_inc(v___x_1705_);
v___x_1707_ = l_Lean_Syntax_matchesNull(v___x_1705_, v___x_1704_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec(v___x_1705_);
lean_dec(v_docComment_x3f_1701_);
lean_dec(v_x_1547_);
v___x_1708_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
lean_ctor_set(v___x_1709_, 1, v___y_1703_);
return v___x_1709_;
}
else
{
lean_object* v_attributes_x3f_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_attributes_x3f_1710_ = l_Lean_Syntax_getArg(v___x_1705_, v___x_1642_);
lean_dec(v___x_1705_);
v___x_1711_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__8));
lean_inc(v_attributes_x3f_1710_);
v___x_1712_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec(v_attributes_x3f_1710_);
lean_dec(v_docComment_x3f_1701_);
lean_dec(v_x_1547_);
v___x_1713_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set(v___x_1714_, 1, v___y_1703_);
return v___x_1714_;
}
else
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v_attributes_x3f_1710_);
v___y_1668_ = v___x_1704_;
v___y_1669_ = v_docComment_x3f_1701_;
v_attributes_x3f_1670_ = v___x_1715_;
v___y_1671_ = v___y_1702_;
v___y_1672_ = v___y_1703_;
goto v___jp_1667_;
}
}
}
else
{
lean_object* v___x_1716_; 
lean_dec(v___x_1705_);
v___x_1716_ = lean_box(0);
v___y_1668_ = v___x_1704_;
v___y_1669_ = v_docComment_x3f_1701_;
v_attributes_x3f_1670_ = v___x_1716_;
v___y_1671_ = v___y_1702_;
v___y_1672_ = v___y_1703_;
goto v___jp_1667_;
}
}
}
v___jp_1552_:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Fmt_fmt_x3f(v___y_1566_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v_a_1569_; lean_object* v___x_1570_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
v_a_1569_ = lean_ctor_get(v___x_1567_, 1);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1567_, 2);
v___x_1570_ = l_Lean_Fmt_fmt(v___y_1553_, v___y_1555_, v_a_1569_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v_a_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
v_a_1572_ = lean_ctor_get(v___x_1570_, 1);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1570_, 2);
v___x_1573_ = lean_mk_empty_array_with_capacity(v___y_1561_);
lean_inc_ref(v___x_1573_);
v___x_1574_ = lean_array_push(v___x_1573_, v_a_1571_);
v___x_1575_ = l_Lean_Fmt_Layouts_fill(v___x_1574_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___y_1557_);
v___x_1577_ = lean_array_push(v___x_1573_, v___x_1576_);
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___y_1554_);
v___x_1579_ = lean_mk_empty_array_with_capacity(v___y_1564_);
v___x_1580_ = lean_array_push(v___x_1579_, v___y_1559_);
v___x_1581_ = lean_array_push(v___x_1580_, v_a_1568_);
v___x_1582_ = lean_box(0);
v___x_1583_ = l_Lean_Fmt_fmtMetaAssignmentDeclaration(v___y_1562_, v___y_1565_, v___x_1577_, v___y_1560_, v___x_1578_, v___x_1581_, v___x_1575_, v___x_1582_, v___x_1582_, v___y_1558_, v___y_1563_, v___x_1551_, v___y_1555_, v_a_1572_);
lean_dec_ref(v___x_1581_);
lean_dec_ref(v___x_1577_);
return v___x_1583_;
}
else
{
lean_dec(v_a_1568_);
lean_dec(v___y_1565_);
lean_dec(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec(v___y_1554_);
return v___x_1570_;
}
}
else
{
lean_dec(v___y_1565_);
lean_dec(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec(v___y_1554_);
lean_dec(v___y_1553_);
return v___x_1567_;
}
}
v___jp_1584_:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Fmt_fmt_x3f(v___y_1598_, v___y_1587_, v___y_1592_);
if (lean_obj_tag(v___x_1599_) == 0)
{
if (lean_obj_tag(v___y_1595_) == 0)
{
lean_object* v_a_1600_; lean_object* v_a_1601_; lean_object* v___x_1602_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
v_a_1601_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1599_, 2);
v___x_1602_ = lean_box(0);
v___y_1553_ = v___y_1585_;
v___y_1554_ = v___y_1586_;
v___y_1555_ = v___y_1587_;
v___y_1556_ = v_a_1601_;
v___y_1557_ = v___y_1588_;
v___y_1558_ = v___y_1589_;
v___y_1559_ = v_a_1600_;
v___y_1560_ = v___y_1590_;
v___y_1561_ = v___y_1591_;
v___y_1562_ = v___y_1593_;
v___y_1563_ = v___y_1594_;
v___y_1564_ = v___y_1596_;
v___y_1565_ = v___y_1597_;
v___y_1566_ = v___x_1602_;
goto v___jp_1552_;
}
else
{
lean_object* v_a_1603_; lean_object* v_a_1604_; lean_object* v_val_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_a_1603_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1603_);
v_a_1604_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1599_, 2);
v_val_1605_ = lean_ctor_get(v___y_1595_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___y_1595_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___y_1595_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_val_1605_);
lean_dec(v___y_1595_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_val_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
v___y_1553_ = v___y_1585_;
v___y_1554_ = v___y_1586_;
v___y_1555_ = v___y_1587_;
v___y_1556_ = v_a_1604_;
v___y_1557_ = v___y_1588_;
v___y_1558_ = v___y_1589_;
v___y_1559_ = v_a_1603_;
v___y_1560_ = v___y_1590_;
v___y_1561_ = v___y_1591_;
v___y_1562_ = v___y_1593_;
v___y_1563_ = v___y_1594_;
v___y_1564_ = v___y_1596_;
v___y_1565_ = v___y_1597_;
v___y_1566_ = v___x_1610_;
goto v___jp_1552_;
}
}
}
}
else
{
lean_dec(v___y_1597_);
lean_dec(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec(v___y_1586_);
lean_dec(v___y_1585_);
return v___x_1599_;
}
}
v___jp_1613_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v_darrowTk_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1625_ = lean_unsigned_to_nat(7u);
v___x_1626_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1625_);
v___x_1627_ = lean_unsigned_to_nat(8u);
v_darrowTk_1628_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1627_);
v___x_1629_ = lean_unsigned_to_nat(9u);
v___x_1630_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1629_);
lean_dec(v_x_1547_);
if (lean_obj_tag(v___y_1616_) == 0)
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_box(0);
v___y_1585_ = v___x_1626_;
v___y_1586_ = v___y_1615_;
v___y_1587_ = v___y_1623_;
v___y_1588_ = v___y_1619_;
v___y_1589_ = v_darrowTk_1628_;
v___y_1590_ = v___y_1614_;
v___y_1591_ = v___y_1617_;
v___y_1592_ = v___y_1624_;
v___y_1593_ = v___y_1618_;
v___y_1594_ = v___x_1630_;
v___y_1595_ = v_namedPrio_x3f_1622_;
v___y_1596_ = v___y_1620_;
v___y_1597_ = v___y_1621_;
v___y_1598_ = v___x_1631_;
goto v___jp_1584_;
}
else
{
lean_object* v_val_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_val_1632_ = lean_ctor_get(v___y_1616_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___y_1616_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___y_1616_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_val_1632_);
lean_dec(v___y_1616_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_val_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
v___y_1585_ = v___x_1626_;
v___y_1586_ = v___y_1615_;
v___y_1587_ = v___y_1623_;
v___y_1588_ = v___y_1619_;
v___y_1589_ = v_darrowTk_1628_;
v___y_1590_ = v___y_1614_;
v___y_1591_ = v___y_1617_;
v___y_1592_ = v___y_1624_;
v___y_1593_ = v___y_1618_;
v___y_1594_ = v___x_1630_;
v___y_1595_ = v_namedPrio_x3f_1622_;
v___y_1596_ = v___y_1620_;
v___y_1597_ = v___y_1621_;
v___y_1598_ = v___x_1637_;
goto v___jp_1584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMixfix___boxed(lean_object* v_x_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_Fmt_fmtMixfix(v_x_1730_, v_a_1731_, v_a_1732_);
lean_dec_ref(v_a_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1(){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1740_ = l_Lean_Fmt_fmtAttribute;
v___x_1741_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__1));
v___x_1742_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___closed__1));
v___x_1743_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMixfix___boxed), 3, 0);
v___x_1744_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1740_, v___x_1741_, v___x_1742_, v___x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1___boxed(lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1();
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtNotation_spec__0(size_t v_sz_1747_, size_t v_i_1748_, lean_object* v_bs_1749_){
_start:
{
uint8_t v___x_1750_; 
v___x_1750_ = lean_usize_dec_lt(v_i_1748_, v_sz_1747_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_bs_1749_);
return v___x_1751_;
}
else
{
lean_object* v_v_1752_; lean_object* v___x_1753_; lean_object* v_bs_x27_1754_; size_t v___x_1755_; size_t v___x_1756_; lean_object* v___x_1757_; 
v_v_1752_ = lean_array_uget(v_bs_1749_, v_i_1748_);
v___x_1753_ = lean_unsigned_to_nat(0u);
v_bs_x27_1754_ = lean_array_uset(v_bs_1749_, v_i_1748_, v___x_1753_);
v___x_1755_ = ((size_t)1ULL);
v___x_1756_ = lean_usize_add(v_i_1748_, v___x_1755_);
v___x_1757_ = lean_array_uset(v_bs_x27_1754_, v_i_1748_, v_v_1752_);
v_i_1748_ = v___x_1756_;
v_bs_1749_ = v___x_1757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtNotation_spec__0___boxed(lean_object* v_sz_1759_, lean_object* v_i_1760_, lean_object* v_bs_1761_){
_start:
{
size_t v_sz_boxed_1762_; size_t v_i_boxed_1763_; lean_object* v_res_1764_; 
v_sz_boxed_1762_ = lean_unbox_usize(v_sz_1759_);
lean_dec(v_sz_1759_);
v_i_boxed_1763_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_res_1764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtNotation_spec__0(v_sz_boxed_1762_, v_i_boxed_1763_, v_bs_1761_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNotation(lean_object* v_x_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v___x_1774_; uint8_t v___x_1775_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v_namedPrio_x3f_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; 
v___x_1774_ = ((lean_object*)(l_Lean_Fmt_fmtNotation___closed__1));
lean_inc(v_x_1771_);
v___x_1775_ = l_Lean_Syntax_isOfKind(v_x_1771_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec(v_x_1771_);
v___x_1901_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v_a_1773_);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v_namedName_x3f_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v_prec_x3f_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v_attributes_x3f_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v_docComment_x3f_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1903_ = lean_unsigned_to_nat(0u);
v___x_1995_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1903_);
v___x_1996_ = l_Lean_Syntax_isNone(v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1995_);
v___x_1998_ = l_Lean_Syntax_matchesNull(v___x_1995_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_dec(v___x_1995_);
lean_dec(v_x_1771_);
v___x_1999_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set(v___x_2000_, 1, v_a_1773_);
return v___x_2000_;
}
else
{
lean_object* v_docComment_x3f_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_docComment_x3f_2001_ = l_Lean_Syntax_getArg(v___x_1995_, v___x_1903_);
lean_dec(v___x_1995_);
v___x_2002_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__10));
lean_inc(v_docComment_x3f_2001_);
v___x_2003_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
lean_dec(v_docComment_x3f_2001_);
lean_dec(v_x_1771_);
v___x_2004_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
lean_ctor_set(v___x_2005_, 1, v_a_1773_);
return v___x_2005_;
}
else
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_docComment_x3f_2001_);
v_docComment_x3f_1979_ = v___x_2006_;
v___y_1980_ = v_a_1772_;
v___y_1981_ = v_a_1773_;
goto v___jp_1978_;
}
}
}
else
{
lean_object* v___x_2007_; 
lean_dec(v___x_1995_);
v___x_2007_ = lean_box(0);
v_docComment_x3f_1979_ = v___x_2007_;
v___y_1980_ = v_a_1772_;
v___y_1981_ = v_a_1773_;
goto v___jp_1978_;
}
v___jp_1904_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1915_ = lean_unsigned_to_nat(6u);
v___x_1916_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1915_);
v___x_1917_ = l_Lean_Syntax_isNone(v___x_1916_);
if (v___x_1917_ == 0)
{
uint8_t v___x_1918_; 
lean_inc(v___x_1916_);
v___x_1918_ = l_Lean_Syntax_matchesNull(v___x_1916_, v___y_1909_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec(v___x_1916_);
lean_dec(v_namedName_x3f_1912_);
lean_dec(v___y_1910_);
lean_dec(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec(v_x_1771_);
v___x_1919_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___y_1914_);
return v___x_1920_;
}
else
{
lean_object* v_namedPrio_x3f_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v_namedPrio_x3f_1921_ = l_Lean_Syntax_getArg(v___x_1916_, v___x_1903_);
lean_dec(v___x_1916_);
v___x_1922_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__3));
lean_inc(v_namedPrio_x3f_1921_);
v___x_1923_ = l_Lean_Syntax_isOfKind(v_namedPrio_x3f_1921_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_dec(v_namedPrio_x3f_1921_);
lean_dec(v_namedName_x3f_1912_);
lean_dec(v___y_1910_);
lean_dec(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec(v_x_1771_);
v___x_1924_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v___y_1914_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_namedPrio_x3f_1921_);
v___y_1868_ = v___y_1906_;
v___y_1869_ = v___y_1905_;
v___y_1870_ = v___y_1907_;
v___y_1871_ = v_namedName_x3f_1912_;
v___y_1872_ = v___y_1908_;
v___y_1873_ = v___y_1910_;
v___y_1874_ = v___y_1909_;
v___y_1875_ = v___y_1911_;
v_namedPrio_x3f_1876_ = v___x_1926_;
v___y_1877_ = v___y_1913_;
v___y_1878_ = v___y_1914_;
goto v___jp_1867_;
}
}
}
else
{
lean_object* v___x_1927_; 
lean_dec(v___x_1916_);
v___x_1927_ = lean_box(0);
v___y_1868_ = v___y_1906_;
v___y_1869_ = v___y_1905_;
v___y_1870_ = v___y_1907_;
v___y_1871_ = v_namedName_x3f_1912_;
v___y_1872_ = v___y_1908_;
v___y_1873_ = v___y_1910_;
v___y_1874_ = v___y_1909_;
v___y_1875_ = v___y_1911_;
v_namedPrio_x3f_1876_ = v___x_1927_;
v___y_1877_ = v___y_1913_;
v___y_1878_ = v___y_1914_;
goto v___jp_1867_;
}
}
v___jp_1928_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1938_ = lean_unsigned_to_nat(5u);
v___x_1939_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1938_);
v___x_1940_ = l_Lean_Syntax_isNone(v___x_1939_);
if (v___x_1940_ == 0)
{
uint8_t v___x_1941_; 
lean_inc(v___x_1939_);
v___x_1941_ = l_Lean_Syntax_matchesNull(v___x_1939_, v___y_1933_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_dec(v___x_1939_);
lean_dec(v_prec_x3f_1935_);
lean_dec(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v_x_1771_);
v___x_1942_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v___y_1937_);
return v___x_1943_;
}
else
{
lean_object* v_namedName_x3f_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v_namedName_x3f_1944_ = l_Lean_Syntax_getArg(v___x_1939_, v___x_1903_);
lean_dec(v___x_1939_);
v___x_1945_ = ((lean_object*)(l_Lean_Fmt_fmtNamedName___closed__2));
lean_inc(v_namedName_x3f_1944_);
v___x_1946_ = l_Lean_Syntax_isOfKind(v_namedName_x3f_1944_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
lean_dec(v_namedName_x3f_1944_);
lean_dec(v_prec_x3f_1935_);
lean_dec(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v_x_1771_);
v___x_1947_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___y_1937_);
return v___x_1948_;
}
else
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1949_, 0, v_namedName_x3f_1944_);
v___y_1905_ = v___y_1930_;
v___y_1906_ = v___y_1929_;
v___y_1907_ = v___y_1931_;
v___y_1908_ = v___y_1932_;
v___y_1909_ = v___y_1933_;
v___y_1910_ = v_prec_x3f_1935_;
v___y_1911_ = v___y_1934_;
v_namedName_x3f_1912_ = v___x_1949_;
v___y_1913_ = v___y_1936_;
v___y_1914_ = v___y_1937_;
goto v___jp_1904_;
}
}
}
else
{
lean_object* v___x_1950_; 
lean_dec(v___x_1939_);
v___x_1950_ = lean_box(0);
v___y_1905_ = v___y_1930_;
v___y_1906_ = v___y_1929_;
v___y_1907_ = v___y_1931_;
v___y_1908_ = v___y_1932_;
v___y_1909_ = v___y_1933_;
v___y_1910_ = v_prec_x3f_1935_;
v___y_1911_ = v___y_1934_;
v_namedName_x3f_1912_ = v___x_1950_;
v___y_1913_ = v___y_1936_;
v___y_1914_ = v___y_1937_;
goto v___jp_1904_;
}
}
v___jp_1951_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1957_ = lean_unsigned_to_nat(2u);
v___x_1958_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1957_);
v___x_1959_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__6));
lean_inc(v___x_1958_);
v___x_1960_ = l_Lean_Syntax_isOfKind(v___x_1958_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec(v___x_1958_);
lean_dec(v_attributes_x3f_1954_);
lean_dec(v___y_1952_);
lean_dec(v_x_1771_);
v___x_1961_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
lean_ctor_set(v___x_1962_, 1, v___y_1956_);
return v___x_1962_;
}
else
{
lean_object* v___x_1963_; lean_object* v_notationTk_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1963_ = lean_unsigned_to_nat(3u);
v_notationTk_1964_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1963_);
v___x_1965_ = lean_unsigned_to_nat(4u);
v___x_1966_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1965_);
v___x_1967_ = l_Lean_Syntax_isNone(v___x_1966_);
if (v___x_1967_ == 0)
{
uint8_t v___x_1968_; 
lean_inc(v___x_1966_);
v___x_1968_ = l_Lean_Syntax_matchesNull(v___x_1966_, v___y_1953_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec(v___x_1966_);
lean_dec(v_notationTk_1964_);
lean_dec(v___x_1958_);
lean_dec(v_attributes_x3f_1954_);
lean_dec(v___y_1952_);
lean_dec(v_x_1771_);
v___x_1969_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v___y_1956_);
return v___x_1970_;
}
else
{
lean_object* v_prec_x3f_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v_prec_x3f_1971_ = l_Lean_Syntax_getArg(v___x_1966_, v___x_1903_);
lean_dec(v___x_1966_);
v___x_1972_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__3));
lean_inc(v_prec_x3f_1971_);
v___x_1973_ = l_Lean_Syntax_isOfKind(v_prec_x3f_1971_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_dec(v_prec_x3f_1971_);
lean_dec(v_notationTk_1964_);
lean_dec(v___x_1958_);
lean_dec(v_attributes_x3f_1954_);
lean_dec(v___y_1952_);
lean_dec(v_x_1771_);
v___x_1974_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
lean_ctor_set(v___x_1975_, 1, v___y_1956_);
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_prec_x3f_1971_);
v___y_1929_ = v___y_1952_;
v___y_1930_ = v_attributes_x3f_1954_;
v___y_1931_ = v_notationTk_1964_;
v___y_1932_ = v___x_1958_;
v___y_1933_ = v___y_1953_;
v___y_1934_ = v___x_1957_;
v_prec_x3f_1935_ = v___x_1976_;
v___y_1936_ = v___y_1955_;
v___y_1937_ = v___y_1956_;
goto v___jp_1928_;
}
}
}
else
{
lean_object* v___x_1977_; 
lean_dec(v___x_1966_);
v___x_1977_ = lean_box(0);
v___y_1929_ = v___y_1952_;
v___y_1930_ = v_attributes_x3f_1954_;
v___y_1931_ = v_notationTk_1964_;
v___y_1932_ = v___x_1958_;
v___y_1933_ = v___y_1953_;
v___y_1934_ = v___x_1957_;
v_prec_x3f_1935_ = v___x_1977_;
v___y_1936_ = v___y_1955_;
v___y_1937_ = v___y_1956_;
goto v___jp_1928_;
}
}
}
v___jp_1978_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1982_);
v___x_1984_ = l_Lean_Syntax_isNone(v___x_1983_);
if (v___x_1984_ == 0)
{
uint8_t v___x_1985_; 
lean_inc(v___x_1983_);
v___x_1985_ = l_Lean_Syntax_matchesNull(v___x_1983_, v___x_1982_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
lean_dec(v___x_1983_);
lean_dec(v_docComment_x3f_1979_);
lean_dec(v_x_1771_);
v___x_1986_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
lean_ctor_set(v___x_1987_, 1, v___y_1981_);
return v___x_1987_;
}
else
{
lean_object* v_attributes_x3f_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v_attributes_x3f_1988_ = l_Lean_Syntax_getArg(v___x_1983_, v___x_1903_);
lean_dec(v___x_1983_);
v___x_1989_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__8));
lean_inc(v_attributes_x3f_1988_);
v___x_1990_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_1988_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_dec(v_attributes_x3f_1988_);
lean_dec(v_docComment_x3f_1979_);
lean_dec(v_x_1771_);
v___x_1991_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
lean_ctor_set(v___x_1992_, 1, v___y_1981_);
return v___x_1992_;
}
else
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_attributes_x3f_1988_);
v___y_1952_ = v_docComment_x3f_1979_;
v___y_1953_ = v___x_1982_;
v_attributes_x3f_1954_ = v___x_1993_;
v___y_1955_ = v___y_1980_;
v___y_1956_ = v___y_1981_;
goto v___jp_1951_;
}
}
}
else
{
lean_object* v___x_1994_; 
lean_dec(v___x_1983_);
v___x_1994_ = lean_box(0);
v___y_1952_ = v_docComment_x3f_1979_;
v___y_1953_ = v___x_1982_;
v_attributes_x3f_1954_ = v___x_1994_;
v___y_1955_ = v___y_1980_;
v___y_1956_ = v___y_1981_;
goto v___jp_1951_;
}
}
}
v___jp_1776_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1790_ = lean_mk_empty_array_with_capacity(v___y_1788_);
v___x_1791_ = lean_array_push(v___x_1790_, v___y_1787_);
v___x_1792_ = lean_array_push(v___x_1791_, v___y_1778_);
v___x_1793_ = lean_box(0);
v___x_1794_ = l_Lean_Fmt_fmtMetaAssignmentDeclaration(v___y_1782_, v___y_1781_, v___y_1786_, v___y_1783_, v___y_1789_, v___x_1792_, v___y_1779_, v___x_1793_, v___x_1793_, v___y_1785_, v___y_1784_, v___x_1775_, v___y_1780_, v___y_1777_);
lean_dec_ref(v___x_1792_);
lean_dec_ref(v___y_1786_);
return v___x_1794_;
}
v___jp_1795_:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_Fmt_fmt_x3f(v___y_1809_, v___y_1801_, v___y_1805_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v_a_1812_; lean_object* v___x_1813_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
v_a_1812_ = lean_ctor_get(v___x_1810_, 1);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1810_, 2);
v___x_1813_ = l_Lean_Fmt_fmtArray___redArg(v___y_1796_, v___y_1801_, v_a_1812_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v_a_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
v_a_1815_ = lean_ctor_get(v___x_1813_, 1);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1813_, 2);
v___x_1816_ = l_Lean_Fmt_Layouts_fill(v_a_1814_);
lean_dec(v_a_1814_);
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___y_1798_);
v___x_1818_ = lean_mk_empty_array_with_capacity(v___y_1800_);
v___x_1819_ = lean_array_push(v___x_1818_, v___x_1817_);
if (lean_obj_tag(v___y_1806_) == 0)
{
lean_object* v___x_1820_; 
v___x_1820_ = lean_box(0);
v___y_1777_ = v_a_1815_;
v___y_1778_ = v_a_1811_;
v___y_1779_ = v___x_1816_;
v___y_1780_ = v___y_1801_;
v___y_1781_ = v___y_1802_;
v___y_1782_ = v___y_1803_;
v___y_1783_ = v___y_1797_;
v___y_1784_ = v___y_1804_;
v___y_1785_ = v___y_1799_;
v___y_1786_ = v___x_1819_;
v___y_1787_ = v___y_1807_;
v___y_1788_ = v___y_1808_;
v___y_1789_ = v___x_1820_;
goto v___jp_1776_;
}
else
{
lean_object* v_val_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_val_1821_ = lean_ctor_get(v___y_1806_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___y_1806_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___y_1806_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_val_1821_);
lean_dec(v___y_1806_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_val_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
v___y_1777_ = v_a_1815_;
v___y_1778_ = v_a_1811_;
v___y_1779_ = v___x_1816_;
v___y_1780_ = v___y_1801_;
v___y_1781_ = v___y_1802_;
v___y_1782_ = v___y_1803_;
v___y_1783_ = v___y_1797_;
v___y_1784_ = v___y_1804_;
v___y_1785_ = v___y_1799_;
v___y_1786_ = v___x_1819_;
v___y_1787_ = v___y_1807_;
v___y_1788_ = v___y_1808_;
v___y_1789_ = v___x_1826_;
goto v___jp_1776_;
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec(v_a_1811_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec(v___y_1797_);
v_a_1829_ = lean_ctor_get(v___x_1813_, 0);
v_a_1830_ = lean_ctor_get(v___x_1813_, 1);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1813_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_inc(v_a_1829_);
lean_dec(v___x_1813_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1829_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v___x_1810_;
}
}
v___jp_1838_:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_Fmt_fmt_x3f(v___y_1852_, v___y_1845_, v___y_1844_);
if (lean_obj_tag(v___x_1853_) == 0)
{
if (lean_obj_tag(v___y_1850_) == 0)
{
lean_object* v_a_1854_; lean_object* v_a_1855_; lean_object* v___x_1856_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
v_a_1855_ = lean_ctor_get(v___x_1853_, 1);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1853_, 2);
v___x_1856_ = lean_box(0);
v___y_1796_ = v___y_1839_;
v___y_1797_ = v___y_1840_;
v___y_1798_ = v___y_1841_;
v___y_1799_ = v___y_1842_;
v___y_1800_ = v___y_1843_;
v___y_1801_ = v___y_1845_;
v___y_1802_ = v___y_1846_;
v___y_1803_ = v___y_1847_;
v___y_1804_ = v___y_1848_;
v___y_1805_ = v_a_1855_;
v___y_1806_ = v___y_1849_;
v___y_1807_ = v_a_1854_;
v___y_1808_ = v___y_1851_;
v___y_1809_ = v___x_1856_;
goto v___jp_1795_;
}
else
{
lean_object* v_a_1857_; lean_object* v_a_1858_; lean_object* v_val_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_a_1857_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1857_);
v_a_1858_ = lean_ctor_get(v___x_1853_, 1);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1853_, 2);
v_val_1859_ = lean_ctor_get(v___y_1850_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___y_1850_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___y_1850_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_val_1859_);
lean_dec(v___y_1850_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_val_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
v___y_1796_ = v___y_1839_;
v___y_1797_ = v___y_1840_;
v___y_1798_ = v___y_1841_;
v___y_1799_ = v___y_1842_;
v___y_1800_ = v___y_1843_;
v___y_1801_ = v___y_1845_;
v___y_1802_ = v___y_1846_;
v___y_1803_ = v___y_1847_;
v___y_1804_ = v___y_1848_;
v___y_1805_ = v_a_1858_;
v___y_1806_ = v___y_1849_;
v___y_1807_ = v_a_1857_;
v___y_1808_ = v___y_1851_;
v___y_1809_ = v___x_1864_;
goto v___jp_1795_;
}
}
}
}
else
{
lean_dec(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
return v___x_1853_;
}
}
v___jp_1867_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; size_t v_sz_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1879_ = lean_unsigned_to_nat(7u);
v___x_1880_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1879_);
v___x_1881_ = l_Lean_Syntax_getArgs(v___x_1880_);
lean_dec(v___x_1880_);
v_sz_1882_ = lean_array_size(v___x_1881_);
v___x_1883_ = ((size_t)0ULL);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtNotation_spec__0(v_sz_1882_, v___x_1883_, v___x_1881_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec(v_namedPrio_x3f_1876_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec(v_x_1771_);
v___x_1885_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v___y_1878_);
return v___x_1886_;
}
else
{
lean_object* v_val_1887_; lean_object* v___x_1888_; lean_object* v_darrowTk_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v_val_1887_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_val_1887_);
lean_dec_ref_known(v___x_1884_, 1);
v___x_1888_ = lean_unsigned_to_nat(8u);
v_darrowTk_1889_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1888_);
v___x_1890_ = lean_unsigned_to_nat(9u);
v___x_1891_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1890_);
lean_dec(v_x_1771_);
if (lean_obj_tag(v___y_1871_) == 0)
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_box(0);
v___y_1839_ = v_val_1887_;
v___y_1840_ = v___y_1870_;
v___y_1841_ = v___y_1872_;
v___y_1842_ = v_darrowTk_1889_;
v___y_1843_ = v___y_1874_;
v___y_1844_ = v___y_1878_;
v___y_1845_ = v___y_1877_;
v___y_1846_ = v___y_1869_;
v___y_1847_ = v___y_1868_;
v___y_1848_ = v___x_1891_;
v___y_1849_ = v___y_1873_;
v___y_1850_ = v_namedPrio_x3f_1876_;
v___y_1851_ = v___y_1875_;
v___y_1852_ = v___x_1892_;
goto v___jp_1838_;
}
else
{
lean_object* v_val_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_val_1893_ = lean_ctor_get(v___y_1871_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___y_1871_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___y_1871_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_val_1893_);
lean_dec(v___y_1871_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_val_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
v___y_1839_ = v_val_1887_;
v___y_1840_ = v___y_1870_;
v___y_1841_ = v___y_1872_;
v___y_1842_ = v_darrowTk_1889_;
v___y_1843_ = v___y_1874_;
v___y_1844_ = v___y_1878_;
v___y_1845_ = v___y_1877_;
v___y_1846_ = v___y_1869_;
v___y_1847_ = v___y_1868_;
v___y_1848_ = v___x_1891_;
v___y_1849_ = v___y_1873_;
v___y_1850_ = v_namedPrio_x3f_1876_;
v___y_1851_ = v___y_1875_;
v___y_1852_ = v___x_1898_;
goto v___jp_1838_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtNotation___boxed(lean_object* v_x_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_Fmt_fmtNotation(v_x_2008_, v_a_2009_, v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1(){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2018_ = l_Lean_Fmt_fmtAttribute;
v___x_2019_ = ((lean_object*)(l_Lean_Fmt_fmtNotation___closed__1));
v___x_2020_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___closed__1));
v___x_2021_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtNotation___boxed), 3, 0);
v___x_2022_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2018_, v___x_2019_, v___x_2020_, v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1___boxed(lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1();
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroRules(lean_object* v_x_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v_lbTk_x3f_2068_; lean_object* v_kindTk_x3f_2069_; lean_object* v_colonEqTk_x3f_2070_; lean_object* v_kindId_x3f_2071_; lean_object* v_rbTk_x3f_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2059_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__0));
v___x_2060_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__1));
v___x_2091_ = ((lean_object*)(l_Lean_Fmt_fmtMacroRules___closed__2));
lean_inc(v_x_2032_);
v___x_2092_ = l_Lean_Syntax_isOfKind(v_x_2032_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_dec(v_x_2032_);
v___x_2093_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v_a_2034_);
return v___x_2094_;
}
else
{
lean_object* v___x_2095_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v_attributes_x3f_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v_docComment_x3f_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2150_ = l_Lean_Syntax_getArg(v_x_2032_, v___x_2095_);
v___x_2151_ = l_Lean_Syntax_isNone(v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2150_);
v___x_2153_ = l_Lean_Syntax_matchesNull(v___x_2150_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec(v___x_2150_);
lean_dec(v_x_2032_);
v___x_2154_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v_a_2034_);
return v___x_2155_;
}
else
{
lean_object* v_docComment_x3f_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v_docComment_x3f_2156_ = l_Lean_Syntax_getArg(v___x_2150_, v___x_2095_);
lean_dec(v___x_2150_);
v___x_2157_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__10));
lean_inc(v_docComment_x3f_2156_);
v___x_2158_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_2156_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v_docComment_x3f_2156_);
lean_dec(v_x_2032_);
v___x_2159_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v_a_2034_);
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v_docComment_x3f_2156_);
v_docComment_x3f_2134_ = v___x_2161_;
v___y_2135_ = v_a_2033_;
v___y_2136_ = v_a_2034_;
goto v___jp_2133_;
}
}
}
else
{
lean_object* v___x_2162_; 
lean_dec(v___x_2150_);
v___x_2162_ = lean_box(0);
v_docComment_x3f_2134_ = v___x_2162_;
v___y_2135_ = v_a_2033_;
v___y_2136_ = v_a_2034_;
goto v___jp_2133_;
}
v___jp_2096_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2102_ = lean_unsigned_to_nat(2u);
v___x_2103_ = l_Lean_Syntax_getArg(v_x_2032_, v___x_2102_);
v___x_2104_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__4));
v___x_2105_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__6));
lean_inc(v___x_2103_);
v___x_2106_ = l_Lean_Syntax_isOfKind(v___x_2103_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec(v___x_2103_);
lean_dec(v_attributes_x3f_2099_);
lean_dec(v___y_2097_);
lean_dec(v_x_2032_);
v___x_2107_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v___y_2101_);
return v___x_2108_;
}
else
{
lean_object* v___x_2109_; lean_object* v_macroRulesTk_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2109_ = lean_unsigned_to_nat(3u);
v_macroRulesTk_2110_ = l_Lean_Syntax_getArg(v_x_2032_, v___x_2109_);
v___x_2111_ = lean_unsigned_to_nat(4u);
v___x_2112_ = l_Lean_Syntax_getArg(v_x_2032_, v___x_2111_);
v___x_2113_ = l_Lean_Syntax_isNone(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2112_);
v___x_2115_ = l_Lean_Syntax_matchesNull(v___x_2112_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec(v___x_2112_);
lean_dec(v_macroRulesTk_2110_);
lean_dec(v___x_2103_);
lean_dec(v_attributes_x3f_2099_);
lean_dec(v___y_2097_);
lean_dec(v_x_2032_);
v___x_2116_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v___y_2101_);
return v___x_2117_;
}
else
{
lean_object* v_kindId_x3f_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v_kindId_x3f_2118_ = l_Lean_Syntax_getArg(v___x_2112_, v___x_2109_);
v___x_2119_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v_kindId_x3f_2118_);
v___x_2120_ = l_Lean_Syntax_isOfKind(v_kindId_x3f_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec(v_kindId_x3f_2118_);
lean_dec(v___x_2112_);
lean_dec(v_macroRulesTk_2110_);
lean_dec(v___x_2103_);
lean_dec(v_attributes_x3f_2099_);
lean_dec(v___y_2097_);
lean_dec(v_x_2032_);
v___x_2121_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v___y_2101_);
return v___x_2122_;
}
else
{
lean_object* v_lbTk_x3f_2123_; lean_object* v_kindTk_x3f_2124_; lean_object* v_colonEqTk_x3f_2125_; lean_object* v_rbTk_x3f_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_lbTk_x3f_2123_ = l_Lean_Syntax_getArg(v___x_2112_, v___x_2095_);
v_kindTk_x3f_2124_ = l_Lean_Syntax_getArg(v___x_2112_, v___y_2098_);
v_colonEqTk_x3f_2125_ = l_Lean_Syntax_getArg(v___x_2112_, v___x_2102_);
v_rbTk_x3f_2126_ = l_Lean_Syntax_getArg(v___x_2112_, v___x_2111_);
lean_dec(v___x_2112_);
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v_lbTk_x3f_2123_);
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v_kindTk_x3f_2124_);
v___x_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2129_, 0, v_colonEqTk_x3f_2125_);
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v_kindId_x3f_2118_);
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_rbTk_x3f_2126_);
v___y_2062_ = v___x_2104_;
v___y_2063_ = v___y_2097_;
v___y_2064_ = v___y_2098_;
v___y_2065_ = v_attributes_x3f_2099_;
v___y_2066_ = v___x_2103_;
v___y_2067_ = v_macroRulesTk_2110_;
v_lbTk_x3f_2068_ = v___x_2127_;
v_kindTk_x3f_2069_ = v___x_2128_;
v_colonEqTk_x3f_2070_ = v___x_2129_;
v_kindId_x3f_2071_ = v___x_2130_;
v_rbTk_x3f_2072_ = v___x_2131_;
v___y_2073_ = v___y_2100_;
v___y_2074_ = v___y_2101_;
goto v___jp_2061_;
}
}
}
else
{
lean_object* v___x_2132_; 
lean_dec(v___x_2112_);
v___x_2132_ = lean_box(0);
v___y_2062_ = v___x_2104_;
v___y_2063_ = v___y_2097_;
v___y_2064_ = v___y_2098_;
v___y_2065_ = v_attributes_x3f_2099_;
v___y_2066_ = v___x_2103_;
v___y_2067_ = v_macroRulesTk_2110_;
v_lbTk_x3f_2068_ = v___x_2132_;
v_kindTk_x3f_2069_ = v___x_2132_;
v_colonEqTk_x3f_2070_ = v___x_2132_;
v_kindId_x3f_2071_ = v___x_2132_;
v_rbTk_x3f_2072_ = v___x_2132_;
v___y_2073_ = v___y_2100_;
v___y_2074_ = v___y_2101_;
goto v___jp_2061_;
}
}
}
v___jp_2133_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2137_ = lean_unsigned_to_nat(1u);
v___x_2138_ = l_Lean_Syntax_getArg(v_x_2032_, v___x_2137_);
v___x_2139_ = l_Lean_Syntax_isNone(v___x_2138_);
if (v___x_2139_ == 0)
{
uint8_t v___x_2140_; 
lean_inc(v___x_2138_);
v___x_2140_ = l_Lean_Syntax_matchesNull(v___x_2138_, v___x_2137_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec(v___x_2138_);
lean_dec(v_docComment_x3f_2134_);
lean_dec(v_x_2032_);
v___x_2141_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v___y_2136_);
return v___x_2142_;
}
else
{
lean_object* v_attributes_x3f_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v_attributes_x3f_2143_ = l_Lean_Syntax_getArg(v___x_2138_, v___x_2095_);
lean_dec(v___x_2138_);
v___x_2144_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__8));
lean_inc(v_attributes_x3f_2143_);
v___x_2145_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_2143_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec(v_attributes_x3f_2143_);
lean_dec(v_docComment_x3f_2134_);
lean_dec(v_x_2032_);
v___x_2146_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v___y_2136_);
return v___x_2147_;
}
else
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_attributes_x3f_2143_);
v___y_2097_ = v_docComment_x3f_2134_;
v___y_2098_ = v___x_2137_;
v_attributes_x3f_2099_ = v___x_2148_;
v___y_2100_ = v___y_2135_;
v___y_2101_ = v___y_2136_;
goto v___jp_2096_;
}
}
}
else
{
lean_object* v___x_2149_; 
lean_dec(v___x_2138_);
v___x_2149_ = lean_box(0);
v___y_2097_ = v_docComment_x3f_2134_;
v___y_2098_ = v___x_2137_;
v_attributes_x3f_2099_ = v___x_2149_;
v___y_2100_ = v___y_2135_;
v___y_2101_ = v___y_2136_;
goto v___jp_2096_;
}
}
}
v___jp_2035_:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v___y_2037_, v___y_2041_, v___y_2043_, v___y_2048_, v___y_2045_, v___y_2044_, v___y_2042_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v_a_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
v_a_2051_ = lean_ctor_get(v___x_2049_, 1);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2049_, 2);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___y_2047_);
v___x_2053_ = lean_mk_empty_array_with_capacity(v___y_2039_);
lean_inc_ref(v___x_2053_);
v___x_2054_ = lean_array_push(v___x_2053_, v___x_2052_);
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_array_push(v___x_2053_, v_a_2050_);
v___x_2057_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_2058_ = l_Lean_Fmt_fmtMetaMatchDeclaration(v___y_2036_, v___y_2038_, v___x_2054_, v___y_2046_, v___x_2055_, v___x_2056_, v___x_2057_, v___x_2055_, v___x_2055_, v___y_2040_, v___y_2044_, v_a_2051_);
lean_dec_ref(v___x_2056_);
lean_dec_ref(v___x_2054_);
return v___x_2058_;
}
else
{
lean_dec(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec(v___y_2040_);
lean_dec(v___y_2038_);
lean_dec(v___y_2036_);
return v___x_2049_;
}
}
v___jp_2061_:
{
lean_object* v___x_2075_; lean_object* v_alts_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2075_ = lean_unsigned_to_nat(5u);
v_alts_2076_ = l_Lean_Syntax_getArg(v_x_2032_, v___x_2075_);
lean_dec(v_x_2032_);
v___x_2077_ = ((lean_object*)(l_Lean_Fmt_fmtMacroRules___closed__0));
lean_inc_ref(v___y_2062_);
v___x_2078_ = l_Lean_Name_mkStr4(v___x_2059_, v___x_2060_, v___y_2062_, v___x_2077_);
lean_inc(v_alts_2076_);
v___x_2079_ = l_Lean_Syntax_isOfKind(v_alts_2076_, v___x_2078_);
lean_dec(v___x_2078_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_dec(v_alts_2076_);
lean_dec(v_rbTk_x3f_2072_);
lean_dec(v_kindId_x3f_2071_);
lean_dec(v_colonEqTk_x3f_2070_);
lean_dec(v_kindTk_x3f_2069_);
lean_dec(v_lbTk_x3f_2068_);
lean_dec(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec(v___y_2063_);
v___x_2080_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v___y_2074_);
return v___x_2081_;
}
else
{
if (lean_obj_tag(v_kindId_x3f_2071_) == 0)
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_box(0);
v___y_2036_ = v___y_2063_;
v___y_2037_ = v_lbTk_x3f_2068_;
v___y_2038_ = v___y_2065_;
v___y_2039_ = v___y_2064_;
v___y_2040_ = v_alts_2076_;
v___y_2041_ = v_kindTk_x3f_2069_;
v___y_2042_ = v___y_2074_;
v___y_2043_ = v_colonEqTk_x3f_2070_;
v___y_2044_ = v___y_2073_;
v___y_2045_ = v_rbTk_x3f_2072_;
v___y_2046_ = v___y_2067_;
v___y_2047_ = v___y_2066_;
v___y_2048_ = v___x_2082_;
goto v___jp_2035_;
}
else
{
lean_object* v_val_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
v_val_2083_ = lean_ctor_get(v_kindId_x3f_2071_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_kindId_x3f_2071_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v_kindId_x3f_2071_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_val_2083_);
lean_dec(v_kindId_x3f_2071_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_val_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
v___y_2036_ = v___y_2063_;
v___y_2037_ = v_lbTk_x3f_2068_;
v___y_2038_ = v___y_2065_;
v___y_2039_ = v___y_2064_;
v___y_2040_ = v_alts_2076_;
v___y_2041_ = v_kindTk_x3f_2069_;
v___y_2042_ = v___y_2074_;
v___y_2043_ = v_colonEqTk_x3f_2070_;
v___y_2044_ = v___y_2073_;
v___y_2045_ = v_rbTk_x3f_2072_;
v___y_2046_ = v___y_2067_;
v___y_2047_ = v___y_2066_;
v___y_2048_ = v___x_2088_;
goto v___jp_2035_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroRules___boxed(lean_object* v_x_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Fmt_fmtMacroRules(v_x_2163_, v_a_2164_, v_a_2165_);
lean_dec_ref(v_a_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1(){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2173_ = l_Lean_Fmt_fmtAttribute;
v___x_2174_ = ((lean_object*)(l_Lean_Fmt_fmtMacroRules___closed__2));
v___x_2175_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___closed__1));
v___x_2176_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMacroRules___boxed), 3, 0);
v___x_2177_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2173_, v___x_2174_, v___x_2175_, v___x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1___boxed(lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1();
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxCmd(lean_object* v_x_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v_namedPrio_x3f_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2323_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCmd___closed__1));
lean_inc(v_x_2186_);
v___x_2324_ = l_Lean_Syntax_isOfKind(v_x_2186_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec(v_x_2186_);
v___x_2325_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v_a_2188_);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v_namedName_x3f_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v_prec_x3f_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v_attributes_x3f_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v_docComment_x3f_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2327_ = lean_unsigned_to_nat(0u);
v___x_2419_ = l_Lean_Syntax_getArg(v_x_2186_, v___x_2327_);
v___x_2420_ = l_Lean_Syntax_isNone(v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2419_);
v___x_2422_ = l_Lean_Syntax_matchesNull(v___x_2419_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_dec(v___x_2419_);
lean_dec(v_x_2186_);
v___x_2423_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v_a_2188_);
return v___x_2424_;
}
else
{
lean_object* v_docComment_x3f_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v_docComment_x3f_2425_ = l_Lean_Syntax_getArg(v___x_2419_, v___x_2327_);
lean_dec(v___x_2419_);
v___x_2426_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__10));
lean_inc(v_docComment_x3f_2425_);
v___x_2427_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_2425_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_dec(v_docComment_x3f_2425_);
lean_dec(v_x_2186_);
v___x_2428_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v_a_2188_);
return v___x_2429_;
}
else
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_docComment_x3f_2425_);
v_docComment_x3f_2403_ = v___x_2430_;
v___y_2404_ = v_a_2187_;
v___y_2405_ = v_a_2188_;
goto v___jp_2402_;
}
}
}
else
{
lean_object* v___x_2431_; 
lean_dec(v___x_2419_);
v___x_2431_ = lean_box(0);
v_docComment_x3f_2403_ = v___x_2431_;
v___y_2404_ = v_a_2187_;
v___y_2405_ = v_a_2188_;
goto v___jp_2402_;
}
v___jp_2328_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2339_ = lean_unsigned_to_nat(6u);
v___x_2340_ = l_Lean_Syntax_getArg(v_x_2186_, v___x_2339_);
v___x_2341_ = l_Lean_Syntax_isNone(v___x_2340_);
if (v___x_2341_ == 0)
{
uint8_t v___x_2342_; 
lean_inc(v___x_2340_);
v___x_2342_ = l_Lean_Syntax_matchesNull(v___x_2340_, v___y_2331_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_dec(v___x_2340_);
lean_dec(v_namedName_x3f_2336_);
lean_dec(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec(v_x_2186_);
v___x_2343_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
lean_ctor_set(v___x_2344_, 1, v___y_2338_);
return v___x_2344_;
}
else
{
lean_object* v_namedPrio_x3f_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v_namedPrio_x3f_2345_ = l_Lean_Syntax_getArg(v___x_2340_, v___x_2327_);
lean_dec(v___x_2340_);
v___x_2346_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__3));
lean_inc(v_namedPrio_x3f_2345_);
v___x_2347_ = l_Lean_Syntax_isOfKind(v_namedPrio_x3f_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
lean_dec(v_namedPrio_x3f_2345_);
lean_dec(v_namedName_x3f_2336_);
lean_dec(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec(v_x_2186_);
v___x_2348_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
lean_ctor_set(v___x_2349_, 1, v___y_2338_);
return v___x_2349_;
}
else
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2350_, 0, v_namedPrio_x3f_2345_);
v___y_2286_ = v___y_2329_;
v___y_2287_ = v_namedName_x3f_2336_;
v___y_2288_ = v___y_2330_;
v___y_2289_ = v___y_2331_;
v___y_2290_ = v___y_2332_;
v___y_2291_ = v___y_2334_;
v___y_2292_ = v___y_2333_;
v___y_2293_ = v___y_2335_;
v_namedPrio_x3f_2294_ = v___x_2350_;
v___y_2295_ = v___y_2337_;
v___y_2296_ = v___y_2338_;
goto v___jp_2285_;
}
}
}
else
{
lean_object* v___x_2351_; 
lean_dec(v___x_2340_);
v___x_2351_ = lean_box(0);
v___y_2286_ = v___y_2329_;
v___y_2287_ = v_namedName_x3f_2336_;
v___y_2288_ = v___y_2330_;
v___y_2289_ = v___y_2331_;
v___y_2290_ = v___y_2332_;
v___y_2291_ = v___y_2334_;
v___y_2292_ = v___y_2333_;
v___y_2293_ = v___y_2335_;
v_namedPrio_x3f_2294_ = v___x_2351_;
v___y_2295_ = v___y_2337_;
v___y_2296_ = v___y_2338_;
goto v___jp_2285_;
}
}
v___jp_2352_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2362_ = lean_unsigned_to_nat(5u);
v___x_2363_ = l_Lean_Syntax_getArg(v_x_2186_, v___x_2362_);
v___x_2364_ = l_Lean_Syntax_isNone(v___x_2363_);
if (v___x_2364_ == 0)
{
uint8_t v___x_2365_; 
lean_inc(v___x_2363_);
v___x_2365_ = l_Lean_Syntax_matchesNull(v___x_2363_, v___y_2355_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_dec(v___x_2363_);
lean_dec(v_prec_x3f_2359_);
lean_dec(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec(v_x_2186_);
v___x_2366_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
lean_ctor_set(v___x_2367_, 1, v___y_2361_);
return v___x_2367_;
}
else
{
lean_object* v_namedName_x3f_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v_namedName_x3f_2368_ = l_Lean_Syntax_getArg(v___x_2363_, v___x_2327_);
lean_dec(v___x_2363_);
v___x_2369_ = ((lean_object*)(l_Lean_Fmt_fmtNamedName___closed__2));
lean_inc(v_namedName_x3f_2368_);
v___x_2370_ = l_Lean_Syntax_isOfKind(v_namedName_x3f_2368_, v___x_2369_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_dec(v_namedName_x3f_2368_);
lean_dec(v_prec_x3f_2359_);
lean_dec(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec(v_x_2186_);
v___x_2371_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
lean_ctor_set(v___x_2372_, 1, v___y_2361_);
return v___x_2372_;
}
else
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2373_, 0, v_namedName_x3f_2368_);
v___y_2329_ = v___y_2353_;
v___y_2330_ = v___y_2354_;
v___y_2331_ = v___y_2355_;
v___y_2332_ = v___y_2356_;
v___y_2333_ = v___y_2357_;
v___y_2334_ = v_prec_x3f_2359_;
v___y_2335_ = v___y_2358_;
v_namedName_x3f_2336_ = v___x_2373_;
v___y_2337_ = v___y_2360_;
v___y_2338_ = v___y_2361_;
goto v___jp_2328_;
}
}
}
else
{
lean_object* v___x_2374_; 
lean_dec(v___x_2363_);
v___x_2374_ = lean_box(0);
v___y_2329_ = v___y_2353_;
v___y_2330_ = v___y_2354_;
v___y_2331_ = v___y_2355_;
v___y_2332_ = v___y_2356_;
v___y_2333_ = v___y_2357_;
v___y_2334_ = v_prec_x3f_2359_;
v___y_2335_ = v___y_2358_;
v_namedName_x3f_2336_ = v___x_2374_;
v___y_2337_ = v___y_2360_;
v___y_2338_ = v___y_2361_;
goto v___jp_2328_;
}
}
v___jp_2375_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v___x_2381_ = lean_unsigned_to_nat(2u);
v___x_2382_ = l_Lean_Syntax_getArg(v_x_2186_, v___x_2381_);
v___x_2383_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__6));
lean_inc(v___x_2382_);
v___x_2384_ = l_Lean_Syntax_isOfKind(v___x_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec(v___x_2382_);
lean_dec(v_attributes_x3f_2378_);
lean_dec(v___y_2377_);
lean_dec(v_x_2186_);
v___x_2385_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v___y_2380_);
return v___x_2386_;
}
else
{
lean_object* v___x_2387_; lean_object* v_syntaxTk_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2387_ = lean_unsigned_to_nat(3u);
v_syntaxTk_2388_ = l_Lean_Syntax_getArg(v_x_2186_, v___x_2387_);
v___x_2389_ = lean_unsigned_to_nat(4u);
v___x_2390_ = l_Lean_Syntax_getArg(v_x_2186_, v___x_2389_);
v___x_2391_ = l_Lean_Syntax_isNone(v___x_2390_);
if (v___x_2391_ == 0)
{
uint8_t v___x_2392_; 
lean_inc(v___x_2390_);
v___x_2392_ = l_Lean_Syntax_matchesNull(v___x_2390_, v___y_2376_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec(v___x_2390_);
lean_dec(v_syntaxTk_2388_);
lean_dec(v___x_2382_);
lean_dec(v_attributes_x3f_2378_);
lean_dec(v___y_2377_);
lean_dec(v_x_2186_);
v___x_2393_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
lean_ctor_set(v___x_2394_, 1, v___y_2380_);
return v___x_2394_;
}
else
{
lean_object* v_prec_x3f_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v_prec_x3f_2395_ = l_Lean_Syntax_getArg(v___x_2390_, v___x_2327_);
lean_dec(v___x_2390_);
v___x_2396_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__3));
lean_inc(v_prec_x3f_2395_);
v___x_2397_ = l_Lean_Syntax_isOfKind(v_prec_x3f_2395_, v___x_2396_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_dec(v_prec_x3f_2395_);
lean_dec(v_syntaxTk_2388_);
lean_dec(v___x_2382_);
lean_dec(v_attributes_x3f_2378_);
lean_dec(v___y_2377_);
lean_dec(v_x_2186_);
v___x_2398_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
lean_ctor_set(v___x_2399_, 1, v___y_2380_);
return v___x_2399_;
}
else
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_prec_x3f_2395_);
v___y_2353_ = v___x_2382_;
v___y_2354_ = v_attributes_x3f_2378_;
v___y_2355_ = v___y_2376_;
v___y_2356_ = v___x_2381_;
v___y_2357_ = v___y_2377_;
v___y_2358_ = v_syntaxTk_2388_;
v_prec_x3f_2359_ = v___x_2400_;
v___y_2360_ = v___y_2379_;
v___y_2361_ = v___y_2380_;
goto v___jp_2352_;
}
}
}
else
{
lean_object* v___x_2401_; 
lean_dec(v___x_2390_);
v___x_2401_ = lean_box(0);
v___y_2353_ = v___x_2382_;
v___y_2354_ = v_attributes_x3f_2378_;
v___y_2355_ = v___y_2376_;
v___y_2356_ = v___x_2381_;
v___y_2357_ = v___y_2377_;
v___y_2358_ = v_syntaxTk_2388_;
v_prec_x3f_2359_ = v___x_2401_;
v___y_2360_ = v___y_2379_;
v___y_2361_ = v___y_2380_;
goto v___jp_2352_;
}
}
}
v___jp_2402_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2406_ = lean_unsigned_to_nat(1u);
v___x_2407_ = l_Lean_Syntax_getArg(v_x_2186_, v___x_2406_);
v___x_2408_ = l_Lean_Syntax_isNone(v___x_2407_);
if (v___x_2408_ == 0)
{
uint8_t v___x_2409_; 
lean_inc(v___x_2407_);
v___x_2409_ = l_Lean_Syntax_matchesNull(v___x_2407_, v___x_2406_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_dec(v___x_2407_);
lean_dec(v_docComment_x3f_2403_);
lean_dec(v_x_2186_);
v___x_2410_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v___y_2405_);
return v___x_2411_;
}
else
{
lean_object* v_attributes_x3f_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v_attributes_x3f_2412_ = l_Lean_Syntax_getArg(v___x_2407_, v___x_2327_);
lean_dec(v___x_2407_);
v___x_2413_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__8));
lean_inc(v_attributes_x3f_2412_);
v___x_2414_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
lean_dec(v_attributes_x3f_2412_);
lean_dec(v_docComment_x3f_2403_);
lean_dec(v_x_2186_);
v___x_2415_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v___y_2405_);
return v___x_2416_;
}
else
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v_attributes_x3f_2412_);
v___y_2376_ = v___x_2406_;
v___y_2377_ = v_docComment_x3f_2403_;
v_attributes_x3f_2378_ = v___x_2417_;
v___y_2379_ = v___y_2404_;
v___y_2380_ = v___y_2405_;
goto v___jp_2375_;
}
}
}
else
{
lean_object* v___x_2418_; 
lean_dec(v___x_2407_);
v___x_2418_ = lean_box(0);
v___y_2376_ = v___x_2406_;
v___y_2377_ = v_docComment_x3f_2403_;
v_attributes_x3f_2378_ = v___x_2418_;
v___y_2379_ = v___y_2404_;
v___y_2380_ = v___y_2405_;
goto v___jp_2375_;
}
}
}
v___jp_2189_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2204_ = lean_mk_empty_array_with_capacity(v___y_2193_);
v___x_2205_ = lean_array_push(v___x_2204_, v___y_2200_);
v___x_2206_ = lean_array_push(v___x_2205_, v___y_2196_);
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___y_2190_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___y_2201_);
v___x_2209_ = l_Lean_Fmt_fmtMetaDeclarationSignature(v___y_2197_, v___y_2203_, v___x_2206_, v___y_2202_, v___x_2207_, v___x_2208_, v___y_2194_, v___y_2198_);
lean_dec_ref(v___x_2206_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v_a_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
v_a_2211_ = lean_ctor_get(v___x_2209_, 1);
lean_inc(v_a_2211_);
lean_dec_ref_known(v___x_2209_, 2);
v___x_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___y_2191_);
v___x_2213_ = lean_mk_empty_array_with_capacity(v___y_2199_);
v___x_2214_ = lean_array_push(v___x_2213_, v___x_2212_);
v___x_2215_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_2195_, v___y_2192_, v___x_2214_, v_a_2210_, v___y_2194_, v_a_2211_);
lean_dec_ref(v___x_2214_);
return v___x_2215_;
}
else
{
lean_dec(v___y_2195_);
lean_dec(v___y_2192_);
lean_dec(v___y_2191_);
return v___x_2209_;
}
}
v___jp_2216_:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_Fmt_fmt_x3f(v___y_2230_, v___y_2221_, v___y_2228_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v_a_2233_; lean_object* v___x_2234_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
v_a_2233_ = lean_ctor_get(v___x_2231_, 1);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2231_, 2);
v___x_2234_ = l_Lean_Fmt_fmtArray___redArg(v___y_2226_, v___y_2221_, v_a_2233_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v_a_2236_; lean_object* v___x_2237_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
v_a_2236_ = lean_ctor_get(v___x_2234_, 1);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2234_, 2);
v___x_2237_ = l_Lean_Fmt_Layouts_fill(v_a_2235_);
lean_dec(v_a_2235_);
if (lean_obj_tag(v___y_2223_) == 0)
{
lean_object* v___x_2238_; 
v___x_2238_ = lean_box(0);
v___y_2190_ = v___y_2217_;
v___y_2191_ = v___y_2218_;
v___y_2192_ = v___y_2219_;
v___y_2193_ = v___y_2220_;
v___y_2194_ = v___y_2221_;
v___y_2195_ = v___y_2222_;
v___y_2196_ = v_a_2232_;
v___y_2197_ = v___y_2224_;
v___y_2198_ = v_a_2236_;
v___y_2199_ = v___y_2225_;
v___y_2200_ = v___y_2227_;
v___y_2201_ = v___y_2229_;
v___y_2202_ = v___x_2237_;
v___y_2203_ = v___x_2238_;
goto v___jp_2189_;
}
else
{
lean_object* v_val_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
v_val_2239_ = lean_ctor_get(v___y_2223_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___y_2223_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___y_2223_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_val_2239_);
lean_dec(v___y_2223_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_val_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
v___y_2190_ = v___y_2217_;
v___y_2191_ = v___y_2218_;
v___y_2192_ = v___y_2219_;
v___y_2193_ = v___y_2220_;
v___y_2194_ = v___y_2221_;
v___y_2195_ = v___y_2222_;
v___y_2196_ = v_a_2232_;
v___y_2197_ = v___y_2224_;
v___y_2198_ = v_a_2236_;
v___y_2199_ = v___y_2225_;
v___y_2200_ = v___y_2227_;
v___y_2201_ = v___y_2229_;
v___y_2202_ = v___x_2237_;
v___y_2203_ = v___x_2244_;
goto v___jp_2189_;
}
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v_a_2232_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec(v___y_2217_);
v_a_2247_ = lean_ctor_get(v___x_2234_, 0);
v_a_2248_ = lean_ctor_get(v___x_2234_, 1);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2234_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_inc(v_a_2247_);
lean_dec(v___x_2234_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2247_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
else
{
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec(v___y_2217_);
return v___x_2231_;
}
}
v___jp_2256_:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Fmt_fmt_x3f(v___y_2270_, v___y_2261_, v___y_2268_);
if (lean_obj_tag(v___x_2271_) == 0)
{
if (lean_obj_tag(v___y_2264_) == 0)
{
lean_object* v_a_2272_; lean_object* v_a_2273_; lean_object* v___x_2274_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
v_a_2273_ = lean_ctor_get(v___x_2271_, 1);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2271_, 2);
v___x_2274_ = lean_box(0);
v___y_2217_ = v___y_2257_;
v___y_2218_ = v___y_2258_;
v___y_2219_ = v___y_2259_;
v___y_2220_ = v___y_2260_;
v___y_2221_ = v___y_2261_;
v___y_2222_ = v___y_2262_;
v___y_2223_ = v___y_2263_;
v___y_2224_ = v___y_2265_;
v___y_2225_ = v___y_2266_;
v___y_2226_ = v___y_2267_;
v___y_2227_ = v_a_2272_;
v___y_2228_ = v_a_2273_;
v___y_2229_ = v___y_2269_;
v___y_2230_ = v___x_2274_;
goto v___jp_2216_;
}
else
{
lean_object* v_a_2275_; lean_object* v_a_2276_; lean_object* v_val_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
v_a_2275_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2275_);
v_a_2276_ = lean_ctor_get(v___x_2271_, 1);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2271_, 2);
v_val_2277_ = lean_ctor_get(v___y_2264_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___y_2264_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___y_2264_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_val_2277_);
lean_dec(v___y_2264_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_val_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
v___y_2217_ = v___y_2257_;
v___y_2218_ = v___y_2258_;
v___y_2219_ = v___y_2259_;
v___y_2220_ = v___y_2260_;
v___y_2221_ = v___y_2261_;
v___y_2222_ = v___y_2262_;
v___y_2223_ = v___y_2263_;
v___y_2224_ = v___y_2265_;
v___y_2225_ = v___y_2266_;
v___y_2226_ = v___y_2267_;
v___y_2227_ = v_a_2275_;
v___y_2228_ = v_a_2276_;
v___y_2229_ = v___y_2269_;
v___y_2230_ = v___x_2282_;
goto v___jp_2216_;
}
}
}
}
else
{
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec(v___y_2257_);
return v___x_2271_;
}
}
v___jp_2285_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; size_t v_sz_2300_; size_t v___x_2301_; lean_object* v___x_2302_; 
v___x_2297_ = lean_unsigned_to_nat(7u);
v___x_2298_ = l_Lean_Syntax_getArg(v_x_2186_, v___x_2297_);
v___x_2299_ = l_Lean_Syntax_getArgs(v___x_2298_);
lean_dec(v___x_2298_);
v_sz_2300_ = lean_array_size(v___x_2299_);
v___x_2301_ = ((size_t)0ULL);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(v_sz_2300_, v___x_2301_, v___x_2299_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec(v_namedPrio_x3f_2294_);
lean_dec(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec(v_x_2186_);
v___x_2303_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v___y_2296_);
return v___x_2304_;
}
else
{
lean_object* v_val_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v_val_2305_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_val_2305_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2306_ = lean_unsigned_to_nat(9u);
v___x_2307_ = l_Lean_Syntax_getArg(v_x_2186_, v___x_2306_);
v___x_2308_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v___x_2307_);
v___x_2309_ = l_Lean_Syntax_isOfKind(v___x_2307_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_dec(v___x_2307_);
lean_dec(v_val_2305_);
lean_dec(v_namedPrio_x3f_2294_);
lean_dec(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec(v_x_2186_);
v___x_2310_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v___y_2296_);
return v___x_2311_;
}
else
{
lean_object* v___x_2312_; lean_object* v_colonTk_2313_; 
v___x_2312_ = lean_unsigned_to_nat(8u);
v_colonTk_2313_ = l_Lean_Syntax_getArg(v_x_2186_, v___x_2312_);
lean_dec(v_x_2186_);
if (lean_obj_tag(v___y_2287_) == 0)
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_box(0);
v___y_2257_ = v_colonTk_2313_;
v___y_2258_ = v___y_2286_;
v___y_2259_ = v___y_2288_;
v___y_2260_ = v___y_2290_;
v___y_2261_ = v___y_2295_;
v___y_2262_ = v___y_2292_;
v___y_2263_ = v___y_2291_;
v___y_2264_ = v_namedPrio_x3f_2294_;
v___y_2265_ = v___y_2293_;
v___y_2266_ = v___y_2289_;
v___y_2267_ = v_val_2305_;
v___y_2268_ = v___y_2296_;
v___y_2269_ = v___x_2307_;
v___y_2270_ = v___x_2314_;
goto v___jp_2256_;
}
else
{
lean_object* v_val_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
v_val_2315_ = lean_ctor_get(v___y_2287_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___y_2287_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___y_2287_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_val_2315_);
lean_dec(v___y_2287_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_val_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
v___y_2257_ = v_colonTk_2313_;
v___y_2258_ = v___y_2286_;
v___y_2259_ = v___y_2288_;
v___y_2260_ = v___y_2290_;
v___y_2261_ = v___y_2295_;
v___y_2262_ = v___y_2292_;
v___y_2263_ = v___y_2291_;
v___y_2264_ = v_namedPrio_x3f_2294_;
v___y_2265_ = v___y_2293_;
v___y_2266_ = v___y_2289_;
v___y_2267_ = v_val_2305_;
v___y_2268_ = v___y_2296_;
v___y_2269_ = v___x_2307_;
v___y_2270_ = v___x_2320_;
goto v___jp_2256_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxCmd___boxed(lean_object* v_x_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_Fmt_fmtSyntaxCmd(v_x_2432_, v_a_2433_, v_a_2434_);
lean_dec_ref(v_a_2433_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1(){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2442_ = l_Lean_Fmt_fmtAttribute;
v___x_2443_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCmd___closed__1));
v___x_2444_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___closed__1));
v___x_2445_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntaxCmd___boxed), 3, 0);
v___x_2446_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2442_, v___x_2443_, v___x_2444_, v___x_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1___boxed(lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1();
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxAbbrev(lean_object* v_x_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___x_2469_; uint8_t v___x_2470_; lean_object* v___y_2472_; lean_object* v_visibility_x3f_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; 
v___x_2469_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxAbbrev___closed__1));
lean_inc(v_x_2455_);
v___x_2470_ = l_Lean_Syntax_isOfKind(v_x_2455_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_dec(v_x_2455_);
v___x_2534_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
lean_ctor_set(v___x_2535_, 1, v_a_2457_);
return v___x_2535_;
}
else
{
lean_object* v___x_2536_; lean_object* v_docComment_x3f_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2536_ = lean_unsigned_to_nat(0u);
v___x_2550_ = l_Lean_Syntax_getArg(v_x_2455_, v___x_2536_);
v___x_2551_ = l_Lean_Syntax_isNone(v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2552_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2550_);
v___x_2553_ = l_Lean_Syntax_matchesNull(v___x_2550_, v___x_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec(v___x_2550_);
lean_dec(v_x_2455_);
v___x_2554_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v_a_2457_);
return v___x_2555_;
}
else
{
lean_object* v_docComment_x3f_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v_docComment_x3f_2556_ = l_Lean_Syntax_getArg(v___x_2550_, v___x_2536_);
lean_dec(v___x_2550_);
v___x_2557_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__10));
lean_inc(v_docComment_x3f_2556_);
v___x_2558_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_2556_, v___x_2557_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_dec(v_docComment_x3f_2556_);
lean_dec(v_x_2455_);
v___x_2559_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
lean_ctor_set(v___x_2560_, 1, v_a_2457_);
return v___x_2560_;
}
else
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_docComment_x3f_2556_);
v_docComment_x3f_2538_ = v___x_2561_;
v___y_2539_ = v_a_2456_;
v___y_2540_ = v_a_2457_;
goto v___jp_2537_;
}
}
}
else
{
lean_object* v___x_2562_; 
lean_dec(v___x_2550_);
v___x_2562_ = lean_box(0);
v_docComment_x3f_2538_ = v___x_2562_;
v___y_2539_ = v_a_2456_;
v___y_2540_ = v_a_2457_;
goto v___jp_2537_;
}
v___jp_2537_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2541_ = lean_unsigned_to_nat(1u);
v___x_2542_ = l_Lean_Syntax_getArg(v_x_2455_, v___x_2541_);
v___x_2543_ = l_Lean_Syntax_isNone(v___x_2542_);
if (v___x_2543_ == 0)
{
uint8_t v___x_2544_; 
lean_inc(v___x_2542_);
v___x_2544_ = l_Lean_Syntax_matchesNull(v___x_2542_, v___x_2541_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec(v___x_2542_);
lean_dec(v_docComment_x3f_2538_);
lean_dec(v_x_2455_);
v___x_2545_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
lean_ctor_set(v___x_2546_, 1, v___y_2540_);
return v___x_2546_;
}
else
{
lean_object* v_visibility_x3f_2547_; lean_object* v___x_2548_; 
v_visibility_x3f_2547_ = l_Lean_Syntax_getArg(v___x_2542_, v___x_2536_);
lean_dec(v___x_2542_);
v___x_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_visibility_x3f_2547_);
v___y_2472_ = v_docComment_x3f_2538_;
v_visibility_x3f_2473_ = v___x_2548_;
v___y_2474_ = v___y_2539_;
v___y_2475_ = v___y_2540_;
goto v___jp_2471_;
}
}
else
{
lean_object* v___x_2549_; 
lean_dec(v___x_2542_);
v___x_2549_ = lean_box(0);
v___y_2472_ = v_docComment_x3f_2538_;
v_visibility_x3f_2473_ = v___x_2549_;
v___y_2474_ = v___y_2539_;
v___y_2475_ = v___y_2540_;
goto v___jp_2471_;
}
}
}
v___jp_2458_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2465_ = lean_unsigned_to_nat(1u);
v___x_2466_ = lean_mk_empty_array_with_capacity(v___x_2465_);
v___x_2467_ = lean_array_push(v___x_2466_, v___y_2464_);
v___x_2468_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_2459_, v___y_2463_, v___x_2467_, v___y_2461_, v___y_2460_, v___y_2462_);
lean_dec_ref(v___x_2467_);
return v___x_2468_;
}
v___jp_2471_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2476_ = lean_unsigned_to_nat(3u);
v___x_2477_ = l_Lean_Syntax_getArg(v_x_2455_, v___x_2476_);
v___x_2478_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v___x_2477_);
v___x_2479_ = l_Lean_Syntax_isOfKind(v___x_2477_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec(v___x_2477_);
lean_dec(v_visibility_x3f_2473_);
lean_dec(v___y_2472_);
lean_dec(v_x_2455_);
v___x_2480_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v___y_2475_);
return v___x_2481_;
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; size_t v_sz_2485_; size_t v___x_2486_; lean_object* v___x_2487_; 
v___x_2482_ = lean_unsigned_to_nat(5u);
v___x_2483_ = l_Lean_Syntax_getArg(v_x_2455_, v___x_2482_);
v___x_2484_ = l_Lean_Syntax_getArgs(v___x_2483_);
lean_dec(v___x_2483_);
v_sz_2485_ = lean_array_size(v___x_2484_);
v___x_2486_ = ((size_t)0ULL);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtSyntaxParen_spec__0(v_sz_2485_, v___x_2486_, v___x_2484_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
lean_dec(v___x_2477_);
lean_dec(v_visibility_x3f_2473_);
lean_dec(v___y_2472_);
lean_dec(v_x_2455_);
v___x_2488_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
lean_ctor_set(v___x_2489_, 1, v___y_2475_);
return v___x_2489_;
}
else
{
lean_object* v_val_2490_; lean_object* v___x_2491_; lean_object* v_syntaxTk_2492_; lean_object* v___x_2493_; 
v_val_2490_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_val_2490_);
lean_dec_ref_known(v___x_2487_, 1);
v___x_2491_ = lean_unsigned_to_nat(2u);
v_syntaxTk_2492_ = l_Lean_Syntax_getArg(v_x_2455_, v___x_2491_);
v___x_2493_ = l_Lean_Fmt_fmt(v_syntaxTk_2492_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v_a_2495_; lean_object* v___x_2496_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
v_a_2495_ = lean_ctor_get(v___x_2493_, 1);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2493_, 2);
v___x_2496_ = l_Lean_Fmt_fmt(v___x_2477_, v___y_2474_, v_a_2495_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v_a_2498_; lean_object* v___x_2499_; lean_object* v_colonEqTk_2500_; uint8_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
v_a_2498_ = lean_ctor_get(v___x_2496_, 1);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2496_, 2);
v___x_2499_ = lean_unsigned_to_nat(4u);
v_colonEqTk_2500_ = l_Lean_Syntax_getArg(v_x_2455_, v___x_2499_);
lean_dec(v_x_2455_);
v___x_2501_ = 0;
v___x_2502_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2502_, 0, v___x_2470_);
lean_ctor_set_uint8(v___x_2502_, 1, v___x_2501_);
lean_ctor_set_uint8(v___x_2502_, 2, v___x_2501_);
lean_ctor_set_uint8(v___x_2502_, 3, v___x_2501_);
v___x_2503_ = l_Lean_Fmt_fmt(v_colonEqTk_2500_, v___y_2474_, v_a_2498_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v_a_2505_; lean_object* v___x_2506_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
v_a_2505_ = lean_ctor_get(v___x_2503_, 1);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2503_, 2);
v___x_2506_ = l_Lean_Fmt_fmtArray___redArg(v_val_2490_, v___y_2474_, v_a_2505_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v_a_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
v_a_2508_ = lean_ctor_get(v___x_2506_, 1);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2506_, 2);
v___x_2509_ = lean_mk_empty_array_with_capacity(v___x_2491_);
v___x_2510_ = lean_array_push(v___x_2509_, v_a_2494_);
v___x_2511_ = lean_array_push(v___x_2510_, v_a_2497_);
v___x_2512_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2511_, v___x_2502_);
v___x_2513_ = l_Lean_Fmt_Layouts_fill(v_a_2507_);
lean_dec(v_a_2507_);
v___x_2514_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_2513_);
v___x_2515_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_2512_, v_a_2504_, v___x_2514_, v___x_2501_);
v___x_2516_ = lean_box(0);
if (lean_obj_tag(v_visibility_x3f_2473_) == 0)
{
v___y_2459_ = v___y_2472_;
v___y_2460_ = v___y_2474_;
v___y_2461_ = v___x_2515_;
v___y_2462_ = v_a_2508_;
v___y_2463_ = v___x_2516_;
v___y_2464_ = v___x_2516_;
goto v___jp_2458_;
}
else
{
lean_object* v_val_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
v_val_2517_ = lean_ctor_get(v_visibility_x3f_2473_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_visibility_x3f_2473_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v_visibility_x3f_2473_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_val_2517_);
lean_dec(v_visibility_x3f_2473_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_val_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
v___y_2459_ = v___y_2472_;
v___y_2460_ = v___y_2474_;
v___y_2461_ = v___x_2515_;
v___y_2462_ = v_a_2508_;
v___y_2463_ = v___x_2516_;
v___y_2464_ = v___x_2522_;
goto v___jp_2458_;
}
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_a_2504_);
lean_dec_ref_known(v___x_2502_, 0);
lean_dec(v_a_2497_);
lean_dec(v_a_2494_);
lean_dec(v_visibility_x3f_2473_);
lean_dec(v___y_2472_);
v_a_2525_ = lean_ctor_get(v___x_2506_, 0);
v_a_2526_ = lean_ctor_get(v___x_2506_, 1);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2506_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_inc(v_a_2525_);
lean_dec(v___x_2506_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2525_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2502_, 0);
lean_dec(v_a_2497_);
lean_dec(v_a_2494_);
lean_dec(v_val_2490_);
lean_dec(v_visibility_x3f_2473_);
lean_dec(v___y_2472_);
return v___x_2503_;
}
}
else
{
lean_dec(v_a_2494_);
lean_dec(v_val_2490_);
lean_dec(v_visibility_x3f_2473_);
lean_dec(v___y_2472_);
lean_dec(v_x_2455_);
return v___x_2496_;
}
}
else
{
lean_dec(v_val_2490_);
lean_dec(v___x_2477_);
lean_dec(v_visibility_x3f_2473_);
lean_dec(v___y_2472_);
lean_dec(v_x_2455_);
return v___x_2493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSyntaxAbbrev___boxed(lean_object* v_x_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Fmt_fmtSyntaxAbbrev(v_x_2563_, v_a_2564_, v_a_2565_);
lean_dec_ref(v_a_2564_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1(){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2573_ = l_Lean_Fmt_fmtAttribute;
v___x_2574_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxAbbrev___closed__1));
v___x_2575_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___closed__1));
v___x_2576_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSyntaxAbbrev___boxed), 3, 0);
v___x_2577_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2573_, v___x_2574_, v___x_2575_, v___x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1___boxed(lean_object* v_a_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1();
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCatBehaviorBoth(lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_Fmt_fmtAtomic(v_a_2580_, v_a_2581_, v_a_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCatBehaviorBoth___boxed(lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_Fmt_fmtCatBehaviorBoth(v_a_2584_, v_a_2585_, v_a_2586_);
lean_dec_ref(v_a_2585_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1(){
_start:
{
lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___f_2600_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__0));
v___x_2601_ = l_Lean_Fmt_fmtAttribute;
v___x_2602_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__1));
v___x_2603_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___closed__3));
v___x_2604_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2601_, v___x_2602_, v___x_2603_, v___f_2600_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1___boxed(lean_object* v_a_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1();
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCatBehaviorSymbol(lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_Fmt_fmtAtomic(v_a_2607_, v_a_2608_, v_a_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCatBehaviorSymbol___boxed(lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_Fmt_fmtCatBehaviorSymbol(v_a_2611_, v_a_2612_, v_a_2613_);
lean_dec_ref(v_a_2612_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1(){
_start:
{
lean_object* v___f_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___f_2627_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1___closed__0));
v___x_2628_ = l_Lean_Fmt_fmtAttribute;
v___x_2629_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__1));
v___x_2630_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___closed__3));
v___x_2631_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2628_, v___x_2629_, v___x_2630_, v___f_2627_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1___boxed(lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1();
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareSyntaxCat(lean_object* v_x_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___x_2643_; uint8_t v___x_2644_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v_lbTk_x3f_2716_; lean_object* v_behaviorTk_x3f_2717_; lean_object* v_colonEqTk_x3f_2718_; lean_object* v_behavior_x3f_2719_; lean_object* v_rbTk_x3f_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; 
v___x_2643_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareSyntaxCat___closed__1));
lean_inc(v_x_2640_);
v___x_2644_ = l_Lean_Syntax_isOfKind(v_x_2640_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_dec(v_x_2640_);
v___x_2732_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v_a_2642_);
return v___x_2733_;
}
else
{
lean_object* v___x_2734_; lean_object* v_docComment_x3f_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2734_ = lean_unsigned_to_nat(0u);
v___x_2766_ = l_Lean_Syntax_getArg(v_x_2640_, v___x_2734_);
v___x_2767_ = l_Lean_Syntax_isNone(v___x_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2766_);
v___x_2769_ = l_Lean_Syntax_matchesNull(v___x_2766_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_dec(v___x_2766_);
lean_dec(v_x_2640_);
v___x_2770_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
lean_ctor_set(v___x_2771_, 1, v_a_2642_);
return v___x_2771_;
}
else
{
lean_object* v_docComment_x3f_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v_docComment_x3f_2772_ = l_Lean_Syntax_getArg(v___x_2766_, v___x_2734_);
lean_dec(v___x_2766_);
v___x_2773_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__10));
lean_inc(v_docComment_x3f_2772_);
v___x_2774_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_2772_, v___x_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_dec(v_docComment_x3f_2772_);
lean_dec(v_x_2640_);
v___x_2775_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
lean_ctor_set(v___x_2776_, 1, v_a_2642_);
return v___x_2776_;
}
else
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2777_, 0, v_docComment_x3f_2772_);
v_docComment_x3f_2736_ = v___x_2777_;
v___y_2737_ = v_a_2641_;
v___y_2738_ = v_a_2642_;
goto v___jp_2735_;
}
}
}
else
{
lean_object* v___x_2778_; 
lean_dec(v___x_2766_);
v___x_2778_ = lean_box(0);
v_docComment_x3f_2736_ = v___x_2778_;
v___y_2737_ = v_a_2641_;
v___y_2738_ = v_a_2642_;
goto v___jp_2735_;
}
v___jp_2735_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v___x_2739_ = lean_unsigned_to_nat(2u);
v___x_2740_ = l_Lean_Syntax_getArg(v_x_2640_, v___x_2739_);
v___x_2741_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v___x_2740_);
v___x_2742_ = l_Lean_Syntax_isOfKind(v___x_2740_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec(v___x_2740_);
lean_dec(v_docComment_x3f_2736_);
lean_dec(v_x_2640_);
v___x_2743_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v___y_2738_);
return v___x_2744_;
}
else
{
lean_object* v___x_2745_; lean_object* v_declareSyntaxCatTk_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2745_ = lean_unsigned_to_nat(1u);
v_declareSyntaxCatTk_2746_ = l_Lean_Syntax_getArg(v_x_2640_, v___x_2745_);
v___x_2747_ = lean_unsigned_to_nat(3u);
v___x_2748_ = l_Lean_Syntax_getArg(v_x_2640_, v___x_2747_);
lean_dec(v_x_2640_);
v___x_2749_ = l_Lean_Syntax_isNone(v___x_2748_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2750_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2748_);
v___x_2751_ = l_Lean_Syntax_matchesNull(v___x_2748_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
lean_dec(v___x_2748_);
lean_dec(v_declareSyntaxCatTk_2746_);
lean_dec(v___x_2740_);
lean_dec(v_docComment_x3f_2736_);
v___x_2752_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
lean_ctor_set(v___x_2753_, 1, v___y_2738_);
return v___x_2753_;
}
else
{
lean_object* v_lbTk_x3f_2754_; lean_object* v_behaviorTk_x3f_2755_; lean_object* v_colonEqTk_x3f_2756_; lean_object* v_behavior_x3f_2757_; lean_object* v___x_2758_; lean_object* v_rbTk_x3f_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v_lbTk_x3f_2754_ = l_Lean_Syntax_getArg(v___x_2748_, v___x_2734_);
v_behaviorTk_x3f_2755_ = l_Lean_Syntax_getArg(v___x_2748_, v___x_2745_);
v_colonEqTk_x3f_2756_ = l_Lean_Syntax_getArg(v___x_2748_, v___x_2739_);
v_behavior_x3f_2757_ = l_Lean_Syntax_getArg(v___x_2748_, v___x_2747_);
v___x_2758_ = lean_unsigned_to_nat(4u);
v_rbTk_x3f_2759_ = l_Lean_Syntax_getArg(v___x_2748_, v___x_2758_);
lean_dec(v___x_2748_);
v___x_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_lbTk_x3f_2754_);
v___x_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2761_, 0, v_behaviorTk_x3f_2755_);
v___x_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2762_, 0, v_colonEqTk_x3f_2756_);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v_behavior_x3f_2757_);
v___x_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2764_, 0, v_rbTk_x3f_2759_);
v___y_2712_ = v_docComment_x3f_2736_;
v___y_2713_ = v_declareSyntaxCatTk_2746_;
v___y_2714_ = v___x_2740_;
v___y_2715_ = v___x_2739_;
v_lbTk_x3f_2716_ = v___x_2760_;
v_behaviorTk_x3f_2717_ = v___x_2761_;
v_colonEqTk_x3f_2718_ = v___x_2762_;
v_behavior_x3f_2719_ = v___x_2763_;
v_rbTk_x3f_2720_ = v___x_2764_;
v___y_2721_ = v___y_2737_;
v___y_2722_ = v___y_2738_;
goto v___jp_2711_;
}
}
else
{
lean_object* v___x_2765_; 
lean_dec(v___x_2748_);
v___x_2765_ = lean_box(0);
v___y_2712_ = v_docComment_x3f_2736_;
v___y_2713_ = v_declareSyntaxCatTk_2746_;
v___y_2714_ = v___x_2740_;
v___y_2715_ = v___x_2739_;
v_lbTk_x3f_2716_ = v___x_2765_;
v_behaviorTk_x3f_2717_ = v___x_2765_;
v_colonEqTk_x3f_2718_ = v___x_2765_;
v_behavior_x3f_2719_ = v___x_2765_;
v_rbTk_x3f_2720_ = v___x_2765_;
v___y_2721_ = v___y_2737_;
v___y_2722_ = v___y_2738_;
goto v___jp_2711_;
}
}
}
}
v___jp_2645_:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v___y_2649_, v___y_2646_, v___y_2652_, v___y_2656_, v___y_2654_, v___y_2651_, v___y_2650_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2678_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_a_2659_ = lean_ctor_get(v___x_2657_, 1);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2661_ = v___x_2657_;
v_isShared_2662_ = v_isSharedCheck_2678_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2678_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2663_ = lean_unsigned_to_nat(3u);
v___x_2664_ = lean_mk_empty_array_with_capacity(v___x_2663_);
v___x_2665_ = lean_array_push(v___x_2664_, v___y_2648_);
v___x_2666_ = lean_array_push(v___x_2665_, v___y_2655_);
v___x_2667_ = lean_array_push(v___x_2666_, v_a_2658_);
v___x_2668_ = 0;
v___x_2669_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2669_, 0, v___x_2644_);
lean_ctor_set_uint8(v___x_2669_, 1, v___x_2668_);
lean_ctor_set_uint8(v___x_2669_, 2, v___x_2668_);
lean_ctor_set_uint8(v___x_2669_, 3, v___x_2668_);
v___x_2670_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2667_, v___x_2669_);
v___x_2671_ = lean_mk_empty_array_with_capacity(v___y_2653_);
v___x_2672_ = lean_array_push(v___x_2671_, v___y_2647_);
v___x_2673_ = lean_array_push(v___x_2672_, v___x_2670_);
v___x_2674_ = l_Lean_Fmt_Layouts_lines(v___x_2673_);
lean_dec_ref(v___x_2673_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2674_);
v___x_2676_ = v___x_2661_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_a_2659_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
else
{
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___y_2648_);
lean_dec_ref(v___y_2647_);
return v___x_2657_;
}
}
v___jp_2679_:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_Fmt_fmt_x3f(v___y_2690_, v___y_2686_, v___y_2684_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v_a_2693_; lean_object* v___x_2694_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
v_a_2693_ = lean_ctor_get(v___x_2691_, 1);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2691_, 2);
v___x_2694_ = l_Lean_Fmt_fmt(v___y_2681_, v___y_2686_, v_a_2693_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v_a_2696_; lean_object* v___x_2697_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
v_a_2696_ = lean_ctor_get(v___x_2694_, 1);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2694_, 2);
v___x_2697_ = l_Lean_Fmt_fmt(v___y_2683_, v___y_2686_, v_a_2696_);
if (lean_obj_tag(v___x_2697_) == 0)
{
if (lean_obj_tag(v___y_2682_) == 0)
{
lean_object* v_a_2698_; lean_object* v_a_2699_; lean_object* v___x_2700_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
v_a_2699_ = lean_ctor_get(v___x_2697_, 1);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2697_, 2);
v___x_2700_ = lean_box(0);
v___y_2646_ = v___y_2680_;
v___y_2647_ = v_a_2692_;
v___y_2648_ = v_a_2695_;
v___y_2649_ = v___y_2685_;
v___y_2650_ = v_a_2699_;
v___y_2651_ = v___y_2686_;
v___y_2652_ = v___y_2687_;
v___y_2653_ = v___y_2689_;
v___y_2654_ = v___y_2688_;
v___y_2655_ = v_a_2698_;
v___y_2656_ = v___x_2700_;
goto v___jp_2645_;
}
else
{
lean_object* v_a_2701_; lean_object* v_a_2702_; lean_object* v_val_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
v_a_2701_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2701_);
v_a_2702_ = lean_ctor_get(v___x_2697_, 1);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2697_, 2);
v_val_2703_ = lean_ctor_get(v___y_2682_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___y_2682_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___y_2682_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_val_2703_);
lean_dec(v___y_2682_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_val_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
v___y_2646_ = v___y_2680_;
v___y_2647_ = v_a_2692_;
v___y_2648_ = v_a_2695_;
v___y_2649_ = v___y_2685_;
v___y_2650_ = v_a_2702_;
v___y_2651_ = v___y_2686_;
v___y_2652_ = v___y_2687_;
v___y_2653_ = v___y_2689_;
v___y_2654_ = v___y_2688_;
v___y_2655_ = v_a_2701_;
v___y_2656_ = v___x_2708_;
goto v___jp_2645_;
}
}
}
}
else
{
lean_dec(v_a_2695_);
lean_dec(v_a_2692_);
lean_dec(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v___y_2685_);
lean_dec(v___y_2682_);
lean_dec(v___y_2680_);
return v___x_2697_;
}
}
else
{
lean_dec(v_a_2692_);
lean_dec(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v___y_2685_);
lean_dec(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec(v___y_2680_);
return v___x_2694_;
}
}
else
{
lean_dec(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v___y_2685_);
lean_dec(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec(v___y_2680_);
return v___x_2691_;
}
}
v___jp_2711_:
{
if (lean_obj_tag(v___y_2712_) == 0)
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_box(0);
v___y_2680_ = v_behaviorTk_x3f_2717_;
v___y_2681_ = v___y_2713_;
v___y_2682_ = v_behavior_x3f_2719_;
v___y_2683_ = v___y_2714_;
v___y_2684_ = v___y_2722_;
v___y_2685_ = v_lbTk_x3f_2716_;
v___y_2686_ = v___y_2721_;
v___y_2687_ = v_colonEqTk_x3f_2718_;
v___y_2688_ = v_rbTk_x3f_2720_;
v___y_2689_ = v___y_2715_;
v___y_2690_ = v___x_2723_;
goto v___jp_2679_;
}
else
{
lean_object* v_val_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
v_val_2724_ = lean_ctor_get(v___y_2712_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___y_2712_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___y_2712_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_val_2724_);
lean_dec(v___y_2712_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_val_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
v___y_2680_ = v_behaviorTk_x3f_2717_;
v___y_2681_ = v___y_2713_;
v___y_2682_ = v_behavior_x3f_2719_;
v___y_2683_ = v___y_2714_;
v___y_2684_ = v___y_2722_;
v___y_2685_ = v_lbTk_x3f_2716_;
v___y_2686_ = v___y_2721_;
v___y_2687_ = v_colonEqTk_x3f_2718_;
v___y_2688_ = v_rbTk_x3f_2720_;
v___y_2689_ = v___y_2715_;
v___y_2690_ = v___x_2729_;
goto v___jp_2679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeclareSyntaxCat___boxed(lean_object* v_x_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_Fmt_fmtDeclareSyntaxCat(v_x_2779_, v_a_2780_, v_a_2781_);
lean_dec_ref(v_a_2780_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1(){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2789_ = l_Lean_Fmt_fmtAttribute;
v___x_2790_ = ((lean_object*)(l_Lean_Fmt_fmtDeclareSyntaxCat___closed__1));
v___x_2791_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___closed__1));
v___x_2792_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDeclareSyntaxCat___boxed), 3, 0);
v___x_2793_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2789_, v___x_2790_, v___x_2791_, v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1___boxed(lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1();
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroArg(lean_object* v_x_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v_id_x3f_2834_; lean_object* v_colonTk_x3f_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = ((lean_object*)(l_Lean_Fmt_fmtMacroArg___closed__1));
lean_inc(v_x_2802_);
v___x_2850_ = l_Lean_Syntax_isOfKind(v_x_2802_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
lean_dec(v_x_2802_);
v___x_2851_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v_a_2804_);
return v___x_2852_;
}
else
{
lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
v___x_2853_ = lean_unsigned_to_nat(0u);
v___x_2854_ = l_Lean_Syntax_getArg(v_x_2802_, v___x_2853_);
v___x_2855_ = l_Lean_Syntax_isNone(v___x_2854_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2856_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2854_);
v___x_2857_ = l_Lean_Syntax_matchesNull(v___x_2854_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_dec(v___x_2854_);
lean_dec(v_x_2802_);
v___x_2858_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set(v___x_2859_, 1, v_a_2804_);
return v___x_2859_;
}
else
{
lean_object* v_id_x3f_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v_id_x3f_2860_ = l_Lean_Syntax_getArg(v___x_2854_, v___x_2853_);
v___x_2861_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v_id_x3f_2860_);
v___x_2862_ = l_Lean_Syntax_isOfKind(v_id_x3f_2860_, v___x_2861_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec(v_id_x3f_2860_);
lean_dec(v___x_2854_);
lean_dec(v_x_2802_);
v___x_2863_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set(v___x_2864_, 1, v_a_2804_);
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; lean_object* v_colonTk_x3f_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2865_ = lean_unsigned_to_nat(1u);
v_colonTk_x3f_2866_ = l_Lean_Syntax_getArg(v___x_2854_, v___x_2865_);
lean_dec(v___x_2854_);
v___x_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_id_x3f_2860_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v_colonTk_x3f_2866_);
v_id_x3f_2834_ = v___x_2867_;
v_colonTk_x3f_2835_ = v___x_2868_;
v___y_2836_ = v_a_2803_;
v___y_2837_ = v_a_2804_;
goto v___jp_2833_;
}
}
}
else
{
lean_object* v___x_2869_; 
lean_dec(v___x_2854_);
v___x_2869_ = lean_box(0);
v_id_x3f_2834_ = v___x_2869_;
v_colonTk_x3f_2835_ = v___x_2869_;
v___y_2836_ = v_a_2803_;
v___y_2837_ = v_a_2804_;
goto v___jp_2833_;
}
}
v___jp_2805_:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_Fmt_fmt_x3f(v___y_2810_, v___y_2809_, v___y_2807_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v_a_2813_; lean_object* v___x_2814_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
v_a_2813_ = lean_ctor_get(v___x_2811_, 1);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2811_, 2);
v___x_2814_ = l_Lean_Fmt_fmt_x3f(v___y_2808_, v___y_2809_, v_a_2813_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
v_a_2816_ = lean_ctor_get(v___x_2814_, 1);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2814_, 2);
v___x_2817_ = l_Lean_Fmt_fmt(v___y_2806_, v___y_2809_, v_a_2816_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2832_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_a_2819_ = lean_ctor_get(v___x_2817_, 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2821_ = v___x_2817_;
v_isShared_2822_ = v_isSharedCheck_2832_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2832_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2823_ = lean_unsigned_to_nat(3u);
v___x_2824_ = lean_mk_empty_array_with_capacity(v___x_2823_);
v___x_2825_ = lean_array_push(v___x_2824_, v_a_2812_);
v___x_2826_ = lean_array_push(v___x_2825_, v_a_2815_);
v___x_2827_ = lean_array_push(v___x_2826_, v_a_2818_);
v___x_2828_ = l_Lean_Fmt_Layouts_atomicInfixOperator(v___x_2827_);
lean_dec_ref(v___x_2827_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2828_);
v___x_2830_ = v___x_2821_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_a_2819_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
else
{
lean_dec(v_a_2815_);
lean_dec(v_a_2812_);
return v___x_2817_;
}
}
else
{
lean_dec(v_a_2812_);
lean_dec(v___y_2806_);
return v___x_2814_;
}
}
else
{
lean_dec(v___y_2808_);
lean_dec(v___y_2806_);
return v___x_2811_;
}
}
v___jp_2833_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = lean_unsigned_to_nat(1u);
v___x_2839_ = l_Lean_Syntax_getArg(v_x_2802_, v___x_2838_);
lean_dec(v_x_2802_);
if (lean_obj_tag(v_id_x3f_2834_) == 0)
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_box(0);
v___y_2806_ = v___x_2839_;
v___y_2807_ = v___y_2837_;
v___y_2808_ = v_colonTk_x3f_2835_;
v___y_2809_ = v___y_2836_;
v___y_2810_ = v___x_2840_;
goto v___jp_2805_;
}
else
{
lean_object* v_val_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
v_val_2841_ = lean_ctor_get(v_id_x3f_2834_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_id_x3f_2834_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v_id_x3f_2834_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_val_2841_);
lean_dec(v_id_x3f_2834_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_val_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
v___y_2806_ = v___x_2839_;
v___y_2807_ = v___y_2837_;
v___y_2808_ = v_colonTk_x3f_2835_;
v___y_2809_ = v___y_2836_;
v___y_2810_ = v___x_2846_;
goto v___jp_2805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroArg___boxed(lean_object* v_x_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_Fmt_fmtMacroArg(v_x_2870_, v_a_2871_, v_a_2872_);
lean_dec_ref(v_a_2871_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1(){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2880_ = l_Lean_Fmt_fmtAttribute;
v___x_2881_ = ((lean_object*)(l_Lean_Fmt_fmtMacroArg___closed__1));
v___x_2882_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___closed__1));
v___x_2883_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMacroArg___boxed), 3, 0);
v___x_2884_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2880_, v___x_2881_, v___x_2882_, v___x_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1___boxed(lean_object* v_a_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1();
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroRhs(lean_object* v_x_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v___x_2896_; uint8_t v___x_2897_; 
v___x_2896_ = ((lean_object*)(l_Lean_Fmt_fmtMacroRhs___closed__1));
lean_inc(v_x_2893_);
v___x_2897_ = l_Lean_Syntax_isOfKind(v_x_2893_, v___x_2896_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_dec(v_x_2893_);
v___x_2898_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
lean_ctor_set(v___x_2899_, 1, v_a_2895_);
return v___x_2899_;
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = lean_unsigned_to_nat(0u);
v___x_2901_ = l_Lean_Syntax_getArg(v_x_2893_, v___x_2900_);
lean_dec(v_x_2893_);
v___x_2902_ = l_Lean_Fmt_fmt(v___x_2901_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2912_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_a_2904_ = lean_ctor_get(v___x_2902_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2906_ = v___x_2902_;
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2908_ = l_Lean_Fmt_TaggedDoc_withPosition(v_a_2903_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2908_);
v___x_2910_ = v___x_2906_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_a_2904_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
else
{
return v___x_2902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacroRhs___boxed(lean_object* v_x_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_Fmt_fmtMacroRhs(v_x_2913_, v_a_2914_, v_a_2915_);
lean_dec_ref(v_a_2914_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1(){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2923_ = l_Lean_Fmt_fmtAttribute;
v___x_2924_ = ((lean_object*)(l_Lean_Fmt_fmtMacroRhs___closed__1));
v___x_2925_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___closed__1));
v___x_2926_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMacroRhs___boxed), 3, 0);
v___x_2927_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2923_, v___x_2924_, v___x_2925_, v___x_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1___boxed(lean_object* v_a_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1();
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtMacro_spec__0(size_t v_sz_2930_, size_t v_i_2931_, lean_object* v_bs_2932_){
_start:
{
uint8_t v___x_2933_; 
v___x_2933_ = lean_usize_dec_lt(v_i_2931_, v_sz_2930_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_bs_2932_);
return v___x_2934_;
}
else
{
lean_object* v_v_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v_v_2935_ = lean_array_uget(v_bs_2932_, v_i_2931_);
v___x_2936_ = ((lean_object*)(l_Lean_Fmt_fmtMacroArg___closed__1));
lean_inc(v_v_2935_);
v___x_2937_ = l_Lean_Syntax_isOfKind(v_v_2935_, v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; 
lean_dec(v_v_2935_);
lean_dec_ref(v_bs_2932_);
v___x_2938_ = lean_box(0);
return v___x_2938_;
}
else
{
lean_object* v___x_2939_; lean_object* v_bs_x27_2940_; size_t v___x_2941_; size_t v___x_2942_; lean_object* v___x_2943_; 
v___x_2939_ = lean_unsigned_to_nat(0u);
v_bs_x27_2940_ = lean_array_uset(v_bs_2932_, v_i_2931_, v___x_2939_);
v___x_2941_ = ((size_t)1ULL);
v___x_2942_ = lean_usize_add(v_i_2931_, v___x_2941_);
v___x_2943_ = lean_array_uset(v_bs_x27_2940_, v_i_2931_, v_v_2935_);
v_i_2931_ = v___x_2942_;
v_bs_2932_ = v___x_2943_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtMacro_spec__0___boxed(lean_object* v_sz_2945_, lean_object* v_i_2946_, lean_object* v_bs_2947_){
_start:
{
size_t v_sz_boxed_2948_; size_t v_i_boxed_2949_; lean_object* v_res_2950_; 
v_sz_boxed_2948_ = lean_unbox_usize(v_sz_2945_);
lean_dec(v_sz_2945_);
v_i_boxed_2949_ = lean_unbox_usize(v_i_2946_);
lean_dec(v_i_2946_);
v_res_2950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtMacro_spec__0(v_sz_boxed_2948_, v_i_boxed_2949_, v_bs_2947_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacro(lean_object* v_x_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v___x_3065_ = ((lean_object*)(l_Lean_Fmt_fmtMacro___closed__1));
lean_inc(v_x_2963_);
v___x_3066_ = l_Lean_Syntax_isOfKind(v_x_2963_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_dec(v_x_2963_);
v___x_3067_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v_a_2965_);
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v_namedPrio_x3f_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v_namedName_x3f_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v_prec_x3f_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v_attributes_x3f_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v_docComment_x3f_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3212_ = l_Lean_Syntax_getArg(v_x_2963_, v___x_3069_);
v___x_3213_ = l_Lean_Syntax_isNone(v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; uint8_t v___x_3215_; 
v___x_3214_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3212_);
v___x_3215_ = l_Lean_Syntax_matchesNull(v___x_3212_, v___x_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_dec(v___x_3212_);
lean_dec(v_x_2963_);
v___x_3216_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
lean_ctor_set(v___x_3217_, 1, v_a_2965_);
return v___x_3217_;
}
else
{
lean_object* v_docComment_x3f_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v_docComment_x3f_3218_ = l_Lean_Syntax_getArg(v___x_3212_, v___x_3069_);
lean_dec(v___x_3212_);
v___x_3219_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__10));
lean_inc(v_docComment_x3f_3218_);
v___x_3220_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_3218_, v___x_3219_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_dec(v_docComment_x3f_3218_);
lean_dec(v_x_2963_);
v___x_3221_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
lean_ctor_set(v___x_3222_, 1, v_a_2965_);
return v___x_3222_;
}
else
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v_docComment_x3f_3218_);
v_docComment_x3f_3196_ = v___x_3223_;
v___y_3197_ = v_a_2964_;
v___y_3198_ = v_a_2965_;
goto v___jp_3195_;
}
}
}
else
{
lean_object* v___x_3224_; 
lean_dec(v___x_3212_);
v___x_3224_ = lean_box(0);
v_docComment_x3f_3196_ = v___x_3224_;
v___y_3197_ = v_a_2964_;
v___y_3198_ = v_a_2965_;
goto v___jp_3195_;
}
v___jp_3070_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; size_t v_sz_3086_; size_t v___x_3087_; lean_object* v___x_3088_; 
v___x_3083_ = lean_unsigned_to_nat(7u);
v___x_3084_ = l_Lean_Syntax_getArg(v_x_2963_, v___x_3083_);
v___x_3085_ = l_Lean_Syntax_getArgs(v___x_3084_);
lean_dec(v___x_3084_);
v_sz_3086_ = lean_array_size(v___x_3085_);
v___x_3087_ = ((size_t)0ULL);
v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtMacro_spec__0(v_sz_3086_, v___x_3087_, v___x_3085_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
lean_dec(v_namedPrio_x3f_3080_);
lean_dec(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec(v___y_3073_);
lean_dec(v___y_3071_);
lean_dec(v_x_2963_);
v___x_3089_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
lean_ctor_set(v___x_3090_, 1, v___y_3082_);
return v___x_3090_;
}
else
{
lean_object* v_val_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v_val_3091_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_val_3091_);
lean_dec_ref_known(v___x_3088_, 1);
v___x_3092_ = lean_unsigned_to_nat(8u);
v___x_3093_ = l_Lean_Syntax_getArg(v_x_2963_, v___x_3092_);
lean_dec(v_x_2963_);
v___x_3094_ = ((lean_object*)(l_Lean_Fmt_fmtMacro___closed__3));
lean_inc(v___x_3093_);
v___x_3095_ = l_Lean_Syntax_isOfKind(v___x_3093_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
lean_dec(v___x_3093_);
lean_dec(v_val_3091_);
lean_dec(v_namedPrio_x3f_3080_);
lean_dec(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec(v___y_3073_);
lean_dec(v___y_3071_);
v___x_3096_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
lean_ctor_set(v___x_3097_, 1, v___y_3082_);
return v___x_3097_;
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3098_ = l_Lean_Syntax_getArg(v___x_3093_, v___y_3075_);
v___x_3099_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v___x_3098_);
v___x_3100_ = l_Lean_Syntax_isOfKind(v___x_3098_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
lean_dec(v___x_3098_);
lean_dec(v___x_3093_);
lean_dec(v_val_3091_);
lean_dec(v_namedPrio_x3f_3080_);
lean_dec(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec(v___y_3073_);
lean_dec(v___y_3071_);
v___x_3101_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
lean_ctor_set(v___x_3102_, 1, v___y_3082_);
return v___x_3102_;
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3103_ = l_Lean_Syntax_getArg(v___x_3093_, v___y_3074_);
v___x_3104_ = ((lean_object*)(l_Lean_Fmt_fmtMacroRhs___closed__1));
lean_inc(v___x_3103_);
v___x_3105_ = l_Lean_Syntax_isOfKind(v___x_3103_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_dec(v___x_3103_);
lean_dec(v___x_3098_);
lean_dec(v___x_3093_);
lean_dec(v_val_3091_);
lean_dec(v_namedPrio_x3f_3080_);
lean_dec(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec(v___y_3073_);
lean_dec(v___y_3071_);
v___x_3106_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
lean_ctor_set(v___x_3107_, 1, v___y_3082_);
return v___x_3107_;
}
else
{
lean_object* v_colonTk_3108_; lean_object* v_darrowTk_3109_; 
v_colonTk_3108_ = l_Lean_Syntax_getArg(v___x_3093_, v___x_3069_);
v_darrowTk_3109_ = l_Lean_Syntax_getArg(v___x_3093_, v___y_3072_);
lean_dec(v___x_3093_);
if (lean_obj_tag(v___y_3079_) == 0)
{
lean_object* v___x_3110_; 
v___x_3110_ = lean_box(0);
v___y_3035_ = v_val_3091_;
v___y_3036_ = v___y_3072_;
v___y_3037_ = v___x_3098_;
v___y_3038_ = v___y_3073_;
v___y_3039_ = v___y_3078_;
v___y_3040_ = v_darrowTk_3109_;
v___y_3041_ = v___y_3071_;
v___y_3042_ = v___y_3081_;
v___y_3043_ = v___y_3075_;
v___y_3044_ = v___x_3103_;
v___y_3045_ = v___y_3082_;
v___y_3046_ = v___y_3076_;
v___y_3047_ = v_namedPrio_x3f_3080_;
v___y_3048_ = v___y_3077_;
v___y_3049_ = v_colonTk_3108_;
v___y_3050_ = v___x_3110_;
goto v___jp_3034_;
}
else
{
lean_object* v_val_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
v_val_3111_ = lean_ctor_get(v___y_3079_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___y_3079_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___y_3079_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_val_3111_);
lean_dec(v___y_3079_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_val_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
v___y_3035_ = v_val_3091_;
v___y_3036_ = v___y_3072_;
v___y_3037_ = v___x_3098_;
v___y_3038_ = v___y_3073_;
v___y_3039_ = v___y_3078_;
v___y_3040_ = v_darrowTk_3109_;
v___y_3041_ = v___y_3071_;
v___y_3042_ = v___y_3081_;
v___y_3043_ = v___y_3075_;
v___y_3044_ = v___x_3103_;
v___y_3045_ = v___y_3082_;
v___y_3046_ = v___y_3076_;
v___y_3047_ = v_namedPrio_x3f_3080_;
v___y_3048_ = v___y_3077_;
v___y_3049_ = v_colonTk_3108_;
v___y_3050_ = v___x_3116_;
goto v___jp_3034_;
}
}
}
}
}
}
}
}
v___jp_3119_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3131_ = lean_unsigned_to_nat(6u);
v___x_3132_ = l_Lean_Syntax_getArg(v_x_2963_, v___x_3131_);
v___x_3133_ = l_Lean_Syntax_isNone(v___x_3132_);
if (v___x_3133_ == 0)
{
uint8_t v___x_3134_; 
lean_inc(v___x_3132_);
v___x_3134_ = l_Lean_Syntax_matchesNull(v___x_3132_, v___y_3124_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_dec(v___x_3132_);
lean_dec(v_namedName_x3f_3128_);
lean_dec(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec(v___y_3123_);
lean_dec(v___y_3120_);
lean_dec(v_x_2963_);
v___x_3135_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
lean_ctor_set(v___x_3136_, 1, v___y_3130_);
return v___x_3136_;
}
else
{
lean_object* v_namedPrio_x3f_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v_namedPrio_x3f_3137_ = l_Lean_Syntax_getArg(v___x_3132_, v___x_3069_);
lean_dec(v___x_3132_);
v___x_3138_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__3));
lean_inc(v_namedPrio_x3f_3137_);
v___x_3139_ = l_Lean_Syntax_isOfKind(v_namedPrio_x3f_3137_, v___x_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
lean_dec(v_namedPrio_x3f_3137_);
lean_dec(v_namedName_x3f_3128_);
lean_dec(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec(v___y_3123_);
lean_dec(v___y_3120_);
lean_dec(v_x_2963_);
v___x_3140_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v___y_3130_);
return v___x_3141_;
}
else
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3142_, 0, v_namedPrio_x3f_3137_);
v___y_3071_ = v___y_3120_;
v___y_3072_ = v___y_3121_;
v___y_3073_ = v___y_3123_;
v___y_3074_ = v___y_3122_;
v___y_3075_ = v___y_3124_;
v___y_3076_ = v___y_3125_;
v___y_3077_ = v___y_3127_;
v___y_3078_ = v___y_3126_;
v___y_3079_ = v_namedName_x3f_3128_;
v_namedPrio_x3f_3080_ = v___x_3142_;
v___y_3081_ = v___y_3129_;
v___y_3082_ = v___y_3130_;
goto v___jp_3070_;
}
}
}
else
{
lean_object* v___x_3143_; 
lean_dec(v___x_3132_);
v___x_3143_ = lean_box(0);
v___y_3071_ = v___y_3120_;
v___y_3072_ = v___y_3121_;
v___y_3073_ = v___y_3123_;
v___y_3074_ = v___y_3122_;
v___y_3075_ = v___y_3124_;
v___y_3076_ = v___y_3125_;
v___y_3077_ = v___y_3127_;
v___y_3078_ = v___y_3126_;
v___y_3079_ = v_namedName_x3f_3128_;
v_namedPrio_x3f_3080_ = v___x_3143_;
v___y_3081_ = v___y_3129_;
v___y_3082_ = v___y_3130_;
goto v___jp_3070_;
}
}
v___jp_3144_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3155_ = lean_unsigned_to_nat(5u);
v___x_3156_ = l_Lean_Syntax_getArg(v_x_2963_, v___x_3155_);
v___x_3157_ = l_Lean_Syntax_isNone(v___x_3156_);
if (v___x_3157_ == 0)
{
uint8_t v___x_3158_; 
lean_inc(v___x_3156_);
v___x_3158_ = l_Lean_Syntax_matchesNull(v___x_3156_, v___y_3149_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_dec(v___x_3156_);
lean_dec(v_prec_x3f_3152_);
lean_dec(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec(v___y_3147_);
lean_dec(v___y_3145_);
lean_dec(v_x_2963_);
v___x_3159_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v___y_3154_);
return v___x_3160_;
}
else
{
lean_object* v_namedName_x3f_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v_namedName_x3f_3161_ = l_Lean_Syntax_getArg(v___x_3156_, v___x_3069_);
lean_dec(v___x_3156_);
v___x_3162_ = ((lean_object*)(l_Lean_Fmt_fmtNamedName___closed__2));
lean_inc(v_namedName_x3f_3161_);
v___x_3163_ = l_Lean_Syntax_isOfKind(v_namedName_x3f_3161_, v___x_3162_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_dec(v_namedName_x3f_3161_);
lean_dec(v_prec_x3f_3152_);
lean_dec(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec(v___y_3147_);
lean_dec(v___y_3145_);
lean_dec(v_x_2963_);
v___x_3164_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
lean_ctor_set(v___x_3165_, 1, v___y_3154_);
return v___x_3165_;
}
else
{
lean_object* v___x_3166_; 
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_namedName_x3f_3161_);
v___y_3120_ = v___y_3145_;
v___y_3121_ = v___y_3146_;
v___y_3122_ = v___y_3148_;
v___y_3123_ = v___y_3147_;
v___y_3124_ = v___y_3149_;
v___y_3125_ = v___y_3150_;
v___y_3126_ = v___y_3151_;
v___y_3127_ = v_prec_x3f_3152_;
v_namedName_x3f_3128_ = v___x_3166_;
v___y_3129_ = v___y_3153_;
v___y_3130_ = v___y_3154_;
goto v___jp_3119_;
}
}
}
else
{
lean_object* v___x_3167_; 
lean_dec(v___x_3156_);
v___x_3167_ = lean_box(0);
v___y_3120_ = v___y_3145_;
v___y_3121_ = v___y_3146_;
v___y_3122_ = v___y_3148_;
v___y_3123_ = v___y_3147_;
v___y_3124_ = v___y_3149_;
v___y_3125_ = v___y_3150_;
v___y_3126_ = v___y_3151_;
v___y_3127_ = v_prec_x3f_3152_;
v_namedName_x3f_3128_ = v___x_3167_;
v___y_3129_ = v___y_3153_;
v___y_3130_ = v___y_3154_;
goto v___jp_3119_;
}
}
v___jp_3168_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3174_ = lean_unsigned_to_nat(2u);
v___x_3175_ = l_Lean_Syntax_getArg(v_x_2963_, v___x_3174_);
v___x_3176_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__6));
lean_inc(v___x_3175_);
v___x_3177_ = l_Lean_Syntax_isOfKind(v___x_3175_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_dec(v___x_3175_);
lean_dec(v_attributes_x3f_3171_);
lean_dec(v___y_3169_);
lean_dec(v_x_2963_);
v___x_3178_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v___y_3173_);
return v___x_3179_;
}
else
{
lean_object* v___x_3180_; lean_object* v_macroTk_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3180_ = lean_unsigned_to_nat(3u);
v_macroTk_3181_ = l_Lean_Syntax_getArg(v_x_2963_, v___x_3180_);
v___x_3182_ = lean_unsigned_to_nat(4u);
v___x_3183_ = l_Lean_Syntax_getArg(v_x_2963_, v___x_3182_);
v___x_3184_ = l_Lean_Syntax_isNone(v___x_3183_);
if (v___x_3184_ == 0)
{
uint8_t v___x_3185_; 
lean_inc(v___x_3183_);
v___x_3185_ = l_Lean_Syntax_matchesNull(v___x_3183_, v___y_3170_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec(v___x_3183_);
lean_dec(v_macroTk_3181_);
lean_dec(v___x_3175_);
lean_dec(v_attributes_x3f_3171_);
lean_dec(v___y_3169_);
lean_dec(v_x_2963_);
v___x_3186_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v___y_3173_);
return v___x_3187_;
}
else
{
lean_object* v_prec_x3f_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; 
v_prec_x3f_3188_ = l_Lean_Syntax_getArg(v___x_3183_, v___x_3069_);
lean_dec(v___x_3183_);
v___x_3189_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__3));
lean_inc(v_prec_x3f_3188_);
v___x_3190_ = l_Lean_Syntax_isOfKind(v_prec_x3f_3188_, v___x_3189_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_dec(v_prec_x3f_3188_);
lean_dec(v_macroTk_3181_);
lean_dec(v___x_3175_);
lean_dec(v_attributes_x3f_3171_);
lean_dec(v___y_3169_);
lean_dec(v_x_2963_);
v___x_3191_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v___y_3173_);
return v___x_3192_;
}
else
{
lean_object* v___x_3193_; 
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v_prec_x3f_3188_);
v___y_3145_ = v___x_3175_;
v___y_3146_ = v___x_3174_;
v___y_3147_ = v___y_3169_;
v___y_3148_ = v___x_3180_;
v___y_3149_ = v___y_3170_;
v___y_3150_ = v_macroTk_3181_;
v___y_3151_ = v_attributes_x3f_3171_;
v_prec_x3f_3152_ = v___x_3193_;
v___y_3153_ = v___y_3172_;
v___y_3154_ = v___y_3173_;
goto v___jp_3144_;
}
}
}
else
{
lean_object* v___x_3194_; 
lean_dec(v___x_3183_);
v___x_3194_ = lean_box(0);
v___y_3145_ = v___x_3175_;
v___y_3146_ = v___x_3174_;
v___y_3147_ = v___y_3169_;
v___y_3148_ = v___x_3180_;
v___y_3149_ = v___y_3170_;
v___y_3150_ = v_macroTk_3181_;
v___y_3151_ = v_attributes_x3f_3171_;
v_prec_x3f_3152_ = v___x_3194_;
v___y_3153_ = v___y_3172_;
v___y_3154_ = v___y_3173_;
goto v___jp_3144_;
}
}
}
v___jp_3195_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; uint8_t v___x_3201_; 
v___x_3199_ = lean_unsigned_to_nat(1u);
v___x_3200_ = l_Lean_Syntax_getArg(v_x_2963_, v___x_3199_);
v___x_3201_ = l_Lean_Syntax_isNone(v___x_3200_);
if (v___x_3201_ == 0)
{
uint8_t v___x_3202_; 
lean_inc(v___x_3200_);
v___x_3202_ = l_Lean_Syntax_matchesNull(v___x_3200_, v___x_3199_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_dec(v___x_3200_);
lean_dec(v_docComment_x3f_3196_);
lean_dec(v_x_2963_);
v___x_3203_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___y_3198_);
return v___x_3204_;
}
else
{
lean_object* v_attributes_x3f_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; 
v_attributes_x3f_3205_ = l_Lean_Syntax_getArg(v___x_3200_, v___x_3069_);
lean_dec(v___x_3200_);
v___x_3206_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__8));
lean_inc(v_attributes_x3f_3205_);
v___x_3207_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_3205_, v___x_3206_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_dec(v_attributes_x3f_3205_);
lean_dec(v_docComment_x3f_3196_);
lean_dec(v_x_2963_);
v___x_3208_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v___y_3198_);
return v___x_3209_;
}
else
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_attributes_x3f_3205_);
v___y_3169_ = v_docComment_x3f_3196_;
v___y_3170_ = v___x_3199_;
v_attributes_x3f_3171_ = v___x_3210_;
v___y_3172_ = v___y_3197_;
v___y_3173_ = v___y_3198_;
goto v___jp_3168_;
}
}
}
else
{
lean_object* v___x_3211_; 
lean_dec(v___x_3200_);
v___x_3211_ = lean_box(0);
v___y_3169_ = v_docComment_x3f_3196_;
v___y_3170_ = v___x_3199_;
v_attributes_x3f_3171_ = v___x_3211_;
v___y_3172_ = v___y_3197_;
v___y_3173_ = v___y_3198_;
goto v___jp_3168_;
}
}
}
v___jp_2966_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; lean_object* v___x_2988_; 
v___x_2982_ = lean_mk_empty_array_with_capacity(v___y_2967_);
v___x_2983_ = lean_array_push(v___x_2982_, v___y_2973_);
v___x_2984_ = lean_array_push(v___x_2983_, v___y_2969_);
v___x_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___y_2980_);
v___x_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___y_2968_);
v___x_2987_ = 0;
v___x_2988_ = l_Lean_Fmt_fmtMetaAssignmentDeclaration(v___y_2970_, v___y_2974_, v___y_2977_, v___y_2979_, v___y_2981_, v___x_2984_, v___y_2971_, v___x_2985_, v___x_2986_, v___y_2975_, v___y_2978_, v___x_2987_, v___y_2976_, v___y_2972_);
lean_dec_ref(v___x_2984_);
lean_dec_ref(v___y_2977_);
return v___x_2988_;
}
v___jp_2989_:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_Fmt_fmt_x3f(v___y_3005_, v___y_2999_, v___y_2991_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v_a_3008_; lean_object* v___x_3009_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
v_a_3008_ = lean_ctor_get(v___x_3006_, 1);
lean_inc(v_a_3008_);
lean_dec_ref_known(v___x_3006_, 2);
v___x_3009_ = l_Lean_Fmt_fmtArray___redArg(v___y_2990_, v___y_2999_, v_a_3008_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v_a_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
v_a_3011_ = lean_ctor_get(v___x_3009_, 1);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3009_, 2);
v___x_3012_ = l_Lean_Fmt_Layouts_fill(v_a_3010_);
lean_dec(v_a_3010_);
v___x_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___y_2998_);
v___x_3014_ = lean_mk_empty_array_with_capacity(v___y_3000_);
v___x_3015_ = lean_array_push(v___x_3014_, v___x_3013_);
if (lean_obj_tag(v___y_3003_) == 0)
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_box(0);
v___y_2967_ = v___y_2992_;
v___y_2968_ = v___y_2993_;
v___y_2969_ = v_a_3007_;
v___y_2970_ = v___y_2994_;
v___y_2971_ = v___x_3012_;
v___y_2972_ = v_a_3011_;
v___y_2973_ = v___y_2995_;
v___y_2974_ = v___y_2996_;
v___y_2975_ = v___y_2997_;
v___y_2976_ = v___y_2999_;
v___y_2977_ = v___x_3015_;
v___y_2978_ = v___y_3001_;
v___y_2979_ = v___y_3002_;
v___y_2980_ = v___y_3004_;
v___y_2981_ = v___x_3016_;
goto v___jp_2966_;
}
else
{
lean_object* v_val_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
v_val_3017_ = lean_ctor_get(v___y_3003_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___y_3003_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___y_3003_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_val_3017_);
lean_dec(v___y_3003_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_val_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
v___y_2967_ = v___y_2992_;
v___y_2968_ = v___y_2993_;
v___y_2969_ = v_a_3007_;
v___y_2970_ = v___y_2994_;
v___y_2971_ = v___x_3012_;
v___y_2972_ = v_a_3011_;
v___y_2973_ = v___y_2995_;
v___y_2974_ = v___y_2996_;
v___y_2975_ = v___y_2997_;
v___y_2976_ = v___y_2999_;
v___y_2977_ = v___x_3015_;
v___y_2978_ = v___y_3001_;
v___y_2979_ = v___y_3002_;
v___y_2980_ = v___y_3004_;
v___y_2981_ = v___x_3022_;
goto v___jp_2966_;
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec(v_a_3007_);
lean_dec(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec(v___y_2993_);
v_a_3025_ = lean_ctor_get(v___x_3009_, 0);
v_a_3026_ = lean_ctor_get(v___x_3009_, 1);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3009_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_inc(v_a_3025_);
lean_dec(v___x_3009_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3025_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_dec(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2990_);
return v___x_3006_;
}
}
v___jp_3034_:
{
lean_object* v___x_3051_; 
v___x_3051_ = l_Lean_Fmt_fmt_x3f(v___y_3050_, v___y_3042_, v___y_3045_);
if (lean_obj_tag(v___x_3051_) == 0)
{
if (lean_obj_tag(v___y_3047_) == 0)
{
lean_object* v_a_3052_; lean_object* v_a_3053_; lean_object* v___x_3054_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
v_a_3053_ = lean_ctor_get(v___x_3051_, 1);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3051_, 2);
v___x_3054_ = lean_box(0);
v___y_2990_ = v___y_3035_;
v___y_2991_ = v_a_3053_;
v___y_2992_ = v___y_3036_;
v___y_2993_ = v___y_3037_;
v___y_2994_ = v___y_3038_;
v___y_2995_ = v_a_3052_;
v___y_2996_ = v___y_3039_;
v___y_2997_ = v___y_3040_;
v___y_2998_ = v___y_3041_;
v___y_2999_ = v___y_3042_;
v___y_3000_ = v___y_3043_;
v___y_3001_ = v___y_3044_;
v___y_3002_ = v___y_3046_;
v___y_3003_ = v___y_3048_;
v___y_3004_ = v___y_3049_;
v___y_3005_ = v___x_3054_;
goto v___jp_2989_;
}
else
{
lean_object* v_a_3055_; lean_object* v_a_3056_; lean_object* v_val_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
v_a_3055_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3055_);
v_a_3056_ = lean_ctor_get(v___x_3051_, 1);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3051_, 2);
v_val_3057_ = lean_ctor_get(v___y_3047_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___y_3047_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___y_3047_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_val_3057_);
lean_dec(v___y_3047_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_val_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
v___y_2990_ = v___y_3035_;
v___y_2991_ = v_a_3056_;
v___y_2992_ = v___y_3036_;
v___y_2993_ = v___y_3037_;
v___y_2994_ = v___y_3038_;
v___y_2995_ = v_a_3055_;
v___y_2996_ = v___y_3039_;
v___y_2997_ = v___y_3040_;
v___y_2998_ = v___y_3041_;
v___y_2999_ = v___y_3042_;
v___y_3000_ = v___y_3043_;
v___y_3001_ = v___y_3044_;
v___y_3002_ = v___y_3046_;
v___y_3003_ = v___y_3048_;
v___y_3004_ = v___y_3049_;
v___y_3005_ = v___x_3062_;
goto v___jp_2989_;
}
}
}
}
else
{
lean_dec(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec(v___y_3044_);
lean_dec(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3035_);
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtMacro___boxed(lean_object* v_x_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Lean_Fmt_fmtMacro(v_x_3225_, v_a_3226_, v_a_3227_);
lean_dec_ref(v_a_3226_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1(){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3235_ = l_Lean_Fmt_fmtAttribute;
v___x_3236_ = ((lean_object*)(l_Lean_Fmt_fmtMacro___closed__1));
v___x_3237_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___closed__1));
v___x_3238_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtMacro___boxed), 3, 0);
v___x_3239_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3235_, v___x_3236_, v___x_3237_, v___x_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1___boxed(lean_object* v_a_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1();
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabRules(lean_object* v_x_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v_leTk_x3f_3351_; lean_object* v_expectedType_x3f_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v___x_3335_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__0));
v___x_3336_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__1));
v___x_3371_ = ((lean_object*)(l_Lean_Fmt_fmtElabRules___closed__1));
lean_inc(v_x_3248_);
v___x_3372_ = l_Lean_Syntax_isOfKind(v_x_3248_, v___x_3371_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_dec(v_x_3248_);
v___x_3373_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v_a_3250_);
return v___x_3374_;
}
else
{
lean_object* v___x_3375_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v_catColonTk_x3f_3389_; lean_object* v_cat_x3f_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v_lbTk_x3f_3416_; lean_object* v_kindTk_x3f_3417_; lean_object* v_colonEqTk_x3f_3418_; lean_object* v_kindId_x3f_3419_; lean_object* v_rbTk_x3f_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v_attributes_x3f_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v_docComment_x3f_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___x_3492_; uint8_t v___x_3493_; 
v___x_3375_ = lean_unsigned_to_nat(0u);
v___x_3492_ = l_Lean_Syntax_getArg(v_x_3248_, v___x_3375_);
v___x_3493_ = l_Lean_Syntax_isNone(v___x_3492_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3494_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3492_);
v___x_3495_ = l_Lean_Syntax_matchesNull(v___x_3492_, v___x_3494_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
lean_dec(v___x_3492_);
lean_dec(v_x_3248_);
v___x_3496_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
lean_ctor_set(v___x_3497_, 1, v_a_3250_);
return v___x_3497_;
}
else
{
lean_object* v_docComment_x3f_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v_docComment_x3f_3498_ = l_Lean_Syntax_getArg(v___x_3492_, v___x_3375_);
lean_dec(v___x_3492_);
v___x_3499_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__10));
lean_inc(v_docComment_x3f_3498_);
v___x_3500_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_3498_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_dec(v_docComment_x3f_3498_);
lean_dec(v_x_3248_);
v___x_3501_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v_a_3250_);
return v___x_3502_;
}
else
{
lean_object* v___x_3503_; 
v___x_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3503_, 0, v_docComment_x3f_3498_);
v_docComment_x3f_3476_ = v___x_3503_;
v___y_3477_ = v_a_3249_;
v___y_3478_ = v_a_3250_;
goto v___jp_3475_;
}
}
}
else
{
lean_object* v___x_3504_; 
lean_dec(v___x_3492_);
v___x_3504_ = lean_box(0);
v_docComment_x3f_3476_ = v___x_3504_;
v___y_3477_ = v_a_3249_;
v___y_3478_ = v_a_3250_;
goto v___jp_3475_;
}
v___jp_3376_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3393_ = lean_unsigned_to_nat(6u);
v___x_3394_ = l_Lean_Syntax_getArg(v_x_3248_, v___x_3393_);
v___x_3395_ = l_Lean_Syntax_isNone(v___x_3394_);
if (v___x_3395_ == 0)
{
uint8_t v___x_3396_; 
lean_inc(v___x_3394_);
v___x_3396_ = l_Lean_Syntax_matchesNull(v___x_3394_, v___y_3386_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_dec(v___x_3394_);
lean_dec(v_cat_x3f_3390_);
lean_dec(v_catColonTk_x3f_3389_);
lean_dec(v___y_3388_);
lean_dec(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec(v_x_3248_);
v___x_3397_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
lean_ctor_set(v___x_3398_, 1, v___y_3392_);
return v___x_3398_;
}
else
{
lean_object* v_expectedType_x3f_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_expectedType_x3f_3399_ = l_Lean_Syntax_getArg(v___x_3394_, v___y_3387_);
v___x_3400_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v_expectedType_x3f_3399_);
v___x_3401_ = l_Lean_Syntax_isOfKind(v_expectedType_x3f_3399_, v___x_3400_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec(v_expectedType_x3f_3399_);
lean_dec(v___x_3394_);
lean_dec(v_cat_x3f_3390_);
lean_dec(v_catColonTk_x3f_3389_);
lean_dec(v___y_3388_);
lean_dec(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec(v_x_3248_);
v___x_3402_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
lean_ctor_set(v___x_3403_, 1, v___y_3392_);
return v___x_3403_;
}
else
{
lean_object* v_leTk_x3f_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v_leTk_x3f_3404_ = l_Lean_Syntax_getArg(v___x_3394_, v___x_3375_);
lean_dec(v___x_3394_);
v___x_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3405_, 0, v_leTk_x3f_3404_);
v___x_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3406_, 0, v_expectedType_x3f_3399_);
v___y_3338_ = v___y_3385_;
v___y_3339_ = v___y_3387_;
v___y_3340_ = v___y_3388_;
v___y_3341_ = v___y_3378_;
v___y_3342_ = v___y_3377_;
v___y_3343_ = v___y_3380_;
v___y_3344_ = v___y_3379_;
v___y_3345_ = v___y_3381_;
v___y_3346_ = v___y_3382_;
v___y_3347_ = v_catColonTk_x3f_3389_;
v___y_3348_ = v___y_3384_;
v___y_3349_ = v___y_3383_;
v___y_3350_ = v_cat_x3f_3390_;
v_leTk_x3f_3351_ = v___x_3405_;
v_expectedType_x3f_3352_ = v___x_3406_;
v___y_3353_ = v___y_3391_;
v___y_3354_ = v___y_3392_;
goto v___jp_3337_;
}
}
}
else
{
lean_object* v___x_3407_; 
lean_dec(v___x_3394_);
v___x_3407_ = lean_box(0);
v___y_3338_ = v___y_3385_;
v___y_3339_ = v___y_3387_;
v___y_3340_ = v___y_3388_;
v___y_3341_ = v___y_3378_;
v___y_3342_ = v___y_3377_;
v___y_3343_ = v___y_3380_;
v___y_3344_ = v___y_3379_;
v___y_3345_ = v___y_3381_;
v___y_3346_ = v___y_3382_;
v___y_3347_ = v_catColonTk_x3f_3389_;
v___y_3348_ = v___y_3384_;
v___y_3349_ = v___y_3383_;
v___y_3350_ = v_cat_x3f_3390_;
v_leTk_x3f_3351_ = v___x_3407_;
v_expectedType_x3f_3352_ = v___x_3407_;
v___y_3353_ = v___y_3391_;
v___y_3354_ = v___y_3392_;
goto v___jp_3337_;
}
}
v___jp_3408_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3423_ = lean_unsigned_to_nat(5u);
v___x_3424_ = l_Lean_Syntax_getArg(v_x_3248_, v___x_3423_);
v___x_3425_ = l_Lean_Syntax_isNone(v___x_3424_);
if (v___x_3425_ == 0)
{
uint8_t v___x_3426_; 
lean_inc(v___x_3424_);
v___x_3426_ = l_Lean_Syntax_matchesNull(v___x_3424_, v___y_3414_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
lean_dec(v___x_3424_);
lean_dec(v_rbTk_x3f_3420_);
lean_dec(v_kindId_x3f_3419_);
lean_dec(v_colonEqTk_x3f_3418_);
lean_dec(v_kindTk_x3f_3417_);
lean_dec(v_lbTk_x3f_3416_);
lean_dec(v___y_3415_);
lean_dec(v___y_3412_);
lean_dec(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec(v_x_3248_);
v___x_3427_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v___y_3422_);
return v___x_3428_;
}
else
{
lean_object* v_cat_x3f_3429_; lean_object* v___x_3430_; uint8_t v___x_3431_; 
v_cat_x3f_3429_ = l_Lean_Syntax_getArg(v___x_3424_, v___y_3413_);
v___x_3430_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v_cat_x3f_3429_);
v___x_3431_ = l_Lean_Syntax_isOfKind(v_cat_x3f_3429_, v___x_3430_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_dec(v_cat_x3f_3429_);
lean_dec(v___x_3424_);
lean_dec(v_rbTk_x3f_3420_);
lean_dec(v_kindId_x3f_3419_);
lean_dec(v_colonEqTk_x3f_3418_);
lean_dec(v_kindTk_x3f_3417_);
lean_dec(v_lbTk_x3f_3416_);
lean_dec(v___y_3415_);
lean_dec(v___y_3412_);
lean_dec(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec(v_x_3248_);
v___x_3432_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
lean_ctor_set(v___x_3433_, 1, v___y_3422_);
return v___x_3433_;
}
else
{
lean_object* v_catColonTk_x3f_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v_catColonTk_x3f_3434_ = l_Lean_Syntax_getArg(v___x_3424_, v___x_3375_);
lean_dec(v___x_3424_);
v___x_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3435_, 0, v_catColonTk_x3f_3434_);
v___x_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3436_, 0, v_cat_x3f_3429_);
v___y_3377_ = v___y_3409_;
v___y_3378_ = v_colonEqTk_x3f_3418_;
v___y_3379_ = v___y_3410_;
v___y_3380_ = v_lbTk_x3f_3416_;
v___y_3381_ = v_kindTk_x3f_3417_;
v___y_3382_ = v_kindId_x3f_3419_;
v___y_3383_ = v_rbTk_x3f_3420_;
v___y_3384_ = v___y_3412_;
v___y_3385_ = v___y_3411_;
v___y_3386_ = v___y_3414_;
v___y_3387_ = v___y_3413_;
v___y_3388_ = v___y_3415_;
v_catColonTk_x3f_3389_ = v___x_3435_;
v_cat_x3f_3390_ = v___x_3436_;
v___y_3391_ = v___y_3421_;
v___y_3392_ = v___y_3422_;
goto v___jp_3376_;
}
}
}
else
{
lean_object* v___x_3437_; 
lean_dec(v___x_3424_);
v___x_3437_ = lean_box(0);
v___y_3377_ = v___y_3409_;
v___y_3378_ = v_colonEqTk_x3f_3418_;
v___y_3379_ = v___y_3410_;
v___y_3380_ = v_lbTk_x3f_3416_;
v___y_3381_ = v_kindTk_x3f_3417_;
v___y_3382_ = v_kindId_x3f_3419_;
v___y_3383_ = v_rbTk_x3f_3420_;
v___y_3384_ = v___y_3412_;
v___y_3385_ = v___y_3411_;
v___y_3386_ = v___y_3414_;
v___y_3387_ = v___y_3413_;
v___y_3388_ = v___y_3415_;
v_catColonTk_x3f_3389_ = v___x_3437_;
v_cat_x3f_3390_ = v___x_3437_;
v___y_3391_ = v___y_3421_;
v___y_3392_ = v___y_3422_;
goto v___jp_3376_;
}
}
v___jp_3438_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v___x_3444_ = lean_unsigned_to_nat(2u);
v___x_3445_ = l_Lean_Syntax_getArg(v_x_3248_, v___x_3444_);
v___x_3446_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__4));
v___x_3447_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__6));
lean_inc(v___x_3445_);
v___x_3448_ = l_Lean_Syntax_isOfKind(v___x_3445_, v___x_3447_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
lean_dec(v___x_3445_);
lean_dec(v_attributes_x3f_3441_);
lean_dec(v___y_3440_);
lean_dec(v_x_3248_);
v___x_3449_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
lean_ctor_set(v___x_3450_, 1, v___y_3443_);
return v___x_3450_;
}
else
{
lean_object* v___x_3451_; lean_object* v_elabRulesTk_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; 
v___x_3451_ = lean_unsigned_to_nat(3u);
v_elabRulesTk_3452_ = l_Lean_Syntax_getArg(v_x_3248_, v___x_3451_);
v___x_3453_ = lean_unsigned_to_nat(4u);
v___x_3454_ = l_Lean_Syntax_getArg(v_x_3248_, v___x_3453_);
v___x_3455_ = l_Lean_Syntax_isNone(v___x_3454_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_3454_);
v___x_3457_ = l_Lean_Syntax_matchesNull(v___x_3454_, v___x_3456_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
lean_dec(v___x_3454_);
lean_dec(v_elabRulesTk_3452_);
lean_dec(v___x_3445_);
lean_dec(v_attributes_x3f_3441_);
lean_dec(v___y_3440_);
lean_dec(v_x_3248_);
v___x_3458_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v___y_3443_);
return v___x_3459_;
}
else
{
lean_object* v_kindId_x3f_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; 
v_kindId_x3f_3460_ = l_Lean_Syntax_getArg(v___x_3454_, v___x_3451_);
v___x_3461_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v_kindId_x3f_3460_);
v___x_3462_ = l_Lean_Syntax_isOfKind(v_kindId_x3f_3460_, v___x_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_dec(v_kindId_x3f_3460_);
lean_dec(v___x_3454_);
lean_dec(v_elabRulesTk_3452_);
lean_dec(v___x_3445_);
lean_dec(v_attributes_x3f_3441_);
lean_dec(v___y_3440_);
lean_dec(v_x_3248_);
v___x_3463_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v___y_3443_);
return v___x_3464_;
}
else
{
lean_object* v_lbTk_x3f_3465_; lean_object* v_kindTk_x3f_3466_; lean_object* v_colonEqTk_x3f_3467_; lean_object* v_rbTk_x3f_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v_lbTk_x3f_3465_ = l_Lean_Syntax_getArg(v___x_3454_, v___x_3375_);
v_kindTk_x3f_3466_ = l_Lean_Syntax_getArg(v___x_3454_, v___y_3439_);
v_colonEqTk_x3f_3467_ = l_Lean_Syntax_getArg(v___x_3454_, v___x_3444_);
v_rbTk_x3f_3468_ = l_Lean_Syntax_getArg(v___x_3454_, v___x_3453_);
lean_dec(v___x_3454_);
v___x_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3469_, 0, v_lbTk_x3f_3465_);
v___x_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3470_, 0, v_kindTk_x3f_3466_);
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v_colonEqTk_x3f_3467_);
v___x_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3472_, 0, v_kindId_x3f_3460_);
v___x_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3473_, 0, v_rbTk_x3f_3468_);
v___y_3409_ = v___x_3445_;
v___y_3410_ = v_attributes_x3f_3441_;
v___y_3411_ = v___x_3446_;
v___y_3412_ = v_elabRulesTk_3452_;
v___y_3413_ = v___y_3439_;
v___y_3414_ = v___x_3444_;
v___y_3415_ = v___y_3440_;
v_lbTk_x3f_3416_ = v___x_3469_;
v_kindTk_x3f_3417_ = v___x_3470_;
v_colonEqTk_x3f_3418_ = v___x_3471_;
v_kindId_x3f_3419_ = v___x_3472_;
v_rbTk_x3f_3420_ = v___x_3473_;
v___y_3421_ = v___y_3442_;
v___y_3422_ = v___y_3443_;
goto v___jp_3408_;
}
}
}
else
{
lean_object* v___x_3474_; 
lean_dec(v___x_3454_);
v___x_3474_ = lean_box(0);
v___y_3409_ = v___x_3445_;
v___y_3410_ = v_attributes_x3f_3441_;
v___y_3411_ = v___x_3446_;
v___y_3412_ = v_elabRulesTk_3452_;
v___y_3413_ = v___y_3439_;
v___y_3414_ = v___x_3444_;
v___y_3415_ = v___y_3440_;
v_lbTk_x3f_3416_ = v___x_3474_;
v_kindTk_x3f_3417_ = v___x_3474_;
v_colonEqTk_x3f_3418_ = v___x_3474_;
v_kindId_x3f_3419_ = v___x_3474_;
v_rbTk_x3f_3420_ = v___x_3474_;
v___y_3421_ = v___y_3442_;
v___y_3422_ = v___y_3443_;
goto v___jp_3408_;
}
}
}
v___jp_3475_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3479_ = lean_unsigned_to_nat(1u);
v___x_3480_ = l_Lean_Syntax_getArg(v_x_3248_, v___x_3479_);
v___x_3481_ = l_Lean_Syntax_isNone(v___x_3480_);
if (v___x_3481_ == 0)
{
uint8_t v___x_3482_; 
lean_inc(v___x_3480_);
v___x_3482_ = l_Lean_Syntax_matchesNull(v___x_3480_, v___x_3479_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_dec(v___x_3480_);
lean_dec(v_docComment_x3f_3476_);
lean_dec(v_x_3248_);
v___x_3483_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
lean_ctor_set(v___x_3484_, 1, v___y_3478_);
return v___x_3484_;
}
else
{
lean_object* v_attributes_x3f_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v_attributes_x3f_3485_ = l_Lean_Syntax_getArg(v___x_3480_, v___x_3375_);
lean_dec(v___x_3480_);
v___x_3486_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__8));
lean_inc(v_attributes_x3f_3485_);
v___x_3487_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_3485_, v___x_3486_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
lean_dec(v_attributes_x3f_3485_);
lean_dec(v_docComment_x3f_3476_);
lean_dec(v_x_3248_);
v___x_3488_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
lean_ctor_set(v___x_3489_, 1, v___y_3478_);
return v___x_3489_;
}
else
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3490_, 0, v_attributes_x3f_3485_);
v___y_3439_ = v___x_3479_;
v___y_3440_ = v_docComment_x3f_3476_;
v_attributes_x3f_3441_ = v___x_3490_;
v___y_3442_ = v___y_3477_;
v___y_3443_ = v___y_3478_;
goto v___jp_3438_;
}
}
}
else
{
lean_object* v___x_3491_; 
lean_dec(v___x_3480_);
v___x_3491_ = lean_box(0);
v___y_3439_ = v___x_3479_;
v___y_3440_ = v_docComment_x3f_3476_;
v_attributes_x3f_3441_ = v___x_3491_;
v___y_3442_ = v___y_3477_;
v___y_3443_ = v___y_3478_;
goto v___jp_3438_;
}
}
}
v___jp_3251_:
{
lean_object* v___x_3267_; 
lean_inc_ref(v___y_3258_);
v___x_3267_ = l_Lean_Fmt_fmtElabDeclarationSignature(v___y_3262_, v___y_3265_, v___y_3264_, v___y_3258_, v___y_3261_, v___y_3263_, v___y_3254_, v___y_3266_, v___y_3260_, v___y_3259_);
lean_dec_ref(v___y_3264_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v_a_3269_; lean_object* v___x_3270_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
v_a_3269_ = lean_ctor_get(v___x_3267_, 1);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3267_, 2);
v___x_3270_ = l_Lean_Fmt_fmt(v___y_3252_, v___y_3260_, v_a_3269_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v_a_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
v_a_3272_ = lean_ctor_get(v___x_3270_, 1);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3270_, 2);
v___x_3273_ = l_Lean_Fmt_Layouts_matchDeclaration(v_a_3268_, v_a_3271_);
v___x_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___y_3256_);
v___x_3275_ = lean_mk_empty_array_with_capacity(v___y_3253_);
v___x_3276_ = lean_array_push(v___x_3275_, v___x_3274_);
v___x_3277_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_3255_, v___y_3257_, v___x_3276_, v___x_3273_, v___y_3260_, v_a_3272_);
lean_dec_ref(v___x_3276_);
return v___x_3277_;
}
else
{
lean_dec(v_a_3268_);
lean_dec(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec(v___y_3255_);
return v___x_3270_;
}
}
else
{
lean_dec(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3252_);
return v___x_3267_;
}
}
v___jp_3278_:
{
if (lean_obj_tag(v___y_3280_) == 0)
{
lean_inc(v___y_3292_);
v___y_3252_ = v___y_3279_;
v___y_3253_ = v___y_3281_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___y_3283_;
v___y_3256_ = v___y_3284_;
v___y_3257_ = v___y_3285_;
v___y_3258_ = v___y_3286_;
v___y_3259_ = v___y_3287_;
v___y_3260_ = v___y_3288_;
v___y_3261_ = v___y_3289_;
v___y_3262_ = v___y_3290_;
v___y_3263_ = v___y_3293_;
v___y_3264_ = v___y_3291_;
v___y_3265_ = v___y_3292_;
v___y_3266_ = v___y_3292_;
goto v___jp_3251_;
}
else
{
lean_object* v_val_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
v_val_3294_ = lean_ctor_get(v___y_3280_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___y_3280_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___y_3280_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_val_3294_);
lean_dec(v___y_3280_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_val_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
v___y_3252_ = v___y_3279_;
v___y_3253_ = v___y_3281_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___y_3283_;
v___y_3256_ = v___y_3284_;
v___y_3257_ = v___y_3285_;
v___y_3258_ = v___y_3286_;
v___y_3259_ = v___y_3287_;
v___y_3260_ = v___y_3288_;
v___y_3261_ = v___y_3289_;
v___y_3262_ = v___y_3290_;
v___y_3263_ = v___y_3293_;
v___y_3264_ = v___y_3291_;
v___y_3265_ = v___y_3292_;
v___y_3266_ = v___x_3299_;
goto v___jp_3251_;
}
}
}
}
v___jp_3302_:
{
lean_object* v___x_3320_; 
v___x_3320_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v___y_3311_, v___y_3313_, v___y_3309_, v___y_3319_, v___y_3317_, v___y_3314_, v___y_3304_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v_a_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
v_a_3322_ = lean_ctor_get(v___x_3320_, 1);
lean_inc(v_a_3322_);
lean_dec_ref_known(v___x_3320_, 2);
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_mk_empty_array_with_capacity(v___y_3306_);
v___x_3325_ = lean_array_push(v___x_3324_, v_a_3321_);
v___x_3326_ = l_Lean_Fmt_TaggedDoc_empty;
if (lean_obj_tag(v___y_3318_) == 0)
{
v___y_3279_ = v___y_3303_;
v___y_3280_ = v___y_3305_;
v___y_3281_ = v___y_3306_;
v___y_3282_ = v___y_3307_;
v___y_3283_ = v___y_3308_;
v___y_3284_ = v___y_3310_;
v___y_3285_ = v___y_3312_;
v___y_3286_ = v___x_3326_;
v___y_3287_ = v_a_3322_;
v___y_3288_ = v___y_3314_;
v___y_3289_ = v___y_3315_;
v___y_3290_ = v___y_3316_;
v___y_3291_ = v___x_3325_;
v___y_3292_ = v___x_3323_;
v___y_3293_ = v___x_3323_;
goto v___jp_3278_;
}
else
{
lean_object* v_val_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
v_val_3327_ = lean_ctor_get(v___y_3318_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___y_3318_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___y_3318_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_val_3327_);
lean_dec(v___y_3318_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_val_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
v___y_3279_ = v___y_3303_;
v___y_3280_ = v___y_3305_;
v___y_3281_ = v___y_3306_;
v___y_3282_ = v___y_3307_;
v___y_3283_ = v___y_3308_;
v___y_3284_ = v___y_3310_;
v___y_3285_ = v___y_3312_;
v___y_3286_ = v___x_3326_;
v___y_3287_ = v_a_3322_;
v___y_3288_ = v___y_3314_;
v___y_3289_ = v___y_3315_;
v___y_3290_ = v___y_3316_;
v___y_3291_ = v___x_3325_;
v___y_3292_ = v___x_3323_;
v___y_3293_ = v___x_3332_;
goto v___jp_3278_;
}
}
}
}
else
{
lean_dec(v___y_3318_);
lean_dec(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec(v___y_3312_);
lean_dec(v___y_3310_);
lean_dec(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3303_);
return v___x_3320_;
}
}
v___jp_3337_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3355_ = lean_unsigned_to_nat(7u);
v___x_3356_ = l_Lean_Syntax_getArg(v_x_3248_, v___x_3355_);
lean_dec(v_x_3248_);
v___x_3357_ = ((lean_object*)(l_Lean_Fmt_fmtMacroRules___closed__0));
lean_inc_ref(v___y_3338_);
v___x_3358_ = l_Lean_Name_mkStr4(v___x_3335_, v___x_3336_, v___y_3338_, v___x_3357_);
lean_inc(v___x_3356_);
v___x_3359_ = l_Lean_Syntax_isOfKind(v___x_3356_, v___x_3358_);
lean_dec(v___x_3358_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_dec(v___x_3356_);
lean_dec(v_expectedType_x3f_3352_);
lean_dec(v_leTk_x3f_3351_);
lean_dec(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec(v___y_3340_);
v___x_3360_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
lean_ctor_set(v___x_3361_, 1, v___y_3354_);
return v___x_3361_;
}
else
{
if (lean_obj_tag(v___y_3346_) == 0)
{
lean_object* v___x_3362_; 
v___x_3362_ = lean_box(0);
v___y_3303_ = v___x_3356_;
v___y_3304_ = v___y_3354_;
v___y_3305_ = v_expectedType_x3f_3352_;
v___y_3306_ = v___y_3339_;
v___y_3307_ = v_leTk_x3f_3351_;
v___y_3308_ = v___y_3340_;
v___y_3309_ = v___y_3341_;
v___y_3310_ = v___y_3342_;
v___y_3311_ = v___y_3343_;
v___y_3312_ = v___y_3344_;
v___y_3313_ = v___y_3345_;
v___y_3314_ = v___y_3353_;
v___y_3315_ = v___y_3347_;
v___y_3316_ = v___y_3348_;
v___y_3317_ = v___y_3349_;
v___y_3318_ = v___y_3350_;
v___y_3319_ = v___x_3362_;
goto v___jp_3302_;
}
else
{
lean_object* v_val_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
v_val_3363_ = lean_ctor_get(v___y_3346_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___y_3346_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___y_3346_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_val_3363_);
lean_dec(v___y_3346_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_val_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
v___y_3303_ = v___x_3356_;
v___y_3304_ = v___y_3354_;
v___y_3305_ = v_expectedType_x3f_3352_;
v___y_3306_ = v___y_3339_;
v___y_3307_ = v_leTk_x3f_3351_;
v___y_3308_ = v___y_3340_;
v___y_3309_ = v___y_3341_;
v___y_3310_ = v___y_3342_;
v___y_3311_ = v___y_3343_;
v___y_3312_ = v___y_3344_;
v___y_3313_ = v___y_3345_;
v___y_3314_ = v___y_3353_;
v___y_3315_ = v___y_3347_;
v___y_3316_ = v___y_3348_;
v___y_3317_ = v___y_3349_;
v___y_3318_ = v___y_3350_;
v___y_3319_ = v___x_3368_;
goto v___jp_3302_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabRules___boxed(lean_object* v_x_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_Fmt_fmtElabRules(v_x_3505_, v_a_3506_, v_a_3507_);
lean_dec_ref(v_a_3506_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1(){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3515_ = l_Lean_Fmt_fmtAttribute;
v___x_3516_ = ((lean_object*)(l_Lean_Fmt_fmtElabRules___closed__1));
v___x_3517_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___closed__1));
v___x_3518_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtElabRules___boxed), 3, 0);
v___x_3519_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3515_, v___x_3516_, v___x_3517_, v___x_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1___boxed(lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1();
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElab(lean_object* v_x_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v_leTk_x3f_3695_; lean_object* v_expectedType_x3f_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___x_3710_; uint8_t v___x_3711_; 
v___x_3710_ = ((lean_object*)(l_Lean_Fmt_fmtElab___closed__1));
lean_inc(v_x_3534_);
v___x_3711_ = l_Lean_Syntax_isOfKind(v_x_3534_, v___x_3710_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
lean_dec(v_x_3534_);
v___x_3712_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v_a_3536_);
return v___x_3713_;
}
else
{
lean_object* v___x_3714_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v_namedPrio_x3f_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v_namedName_x3f_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v_prec_x3f_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v_attributes_x3f_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v_docComment_x3f_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___x_3864_; uint8_t v___x_3865_; 
v___x_3714_ = lean_unsigned_to_nat(0u);
v___x_3864_ = l_Lean_Syntax_getArg(v_x_3534_, v___x_3714_);
v___x_3865_ = l_Lean_Syntax_isNone(v___x_3864_);
if (v___x_3865_ == 0)
{
lean_object* v___x_3866_; uint8_t v___x_3867_; 
v___x_3866_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3864_);
v___x_3867_ = l_Lean_Syntax_matchesNull(v___x_3864_, v___x_3866_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
lean_dec(v___x_3864_);
lean_dec(v_x_3534_);
v___x_3868_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
lean_ctor_set(v___x_3869_, 1, v_a_3536_);
return v___x_3869_;
}
else
{
lean_object* v_docComment_x3f_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v_docComment_x3f_3870_ = l_Lean_Syntax_getArg(v___x_3864_, v___x_3714_);
lean_dec(v___x_3864_);
v___x_3871_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__10));
lean_inc(v_docComment_x3f_3870_);
v___x_3872_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_3870_, v___x_3871_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
lean_dec(v_docComment_x3f_3870_);
lean_dec(v_x_3534_);
v___x_3873_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
lean_ctor_set(v___x_3874_, 1, v_a_3536_);
return v___x_3874_;
}
else
{
lean_object* v___x_3875_; 
v___x_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3875_, 0, v_docComment_x3f_3870_);
v_docComment_x3f_3848_ = v___x_3875_;
v___y_3849_ = v_a_3535_;
v___y_3850_ = v_a_3536_;
goto v___jp_3847_;
}
}
}
else
{
lean_object* v___x_3876_; 
lean_dec(v___x_3864_);
v___x_3876_ = lean_box(0);
v_docComment_x3f_3848_ = v___x_3876_;
v___y_3849_ = v_a_3535_;
v___y_3850_ = v_a_3536_;
goto v___jp_3847_;
}
v___jp_3715_:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; size_t v_sz_3732_; size_t v___x_3733_; lean_object* v___x_3734_; 
v___x_3729_ = lean_unsigned_to_nat(7u);
v___x_3730_ = l_Lean_Syntax_getArg(v_x_3534_, v___x_3729_);
v___x_3731_ = l_Lean_Syntax_getArgs(v___x_3730_);
lean_dec(v___x_3730_);
v_sz_3732_ = lean_array_size(v___x_3731_);
v___x_3733_ = ((size_t)0ULL);
v___x_3734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtMacro_spec__0(v_sz_3732_, v___x_3733_, v___x_3731_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
lean_dec(v_namedPrio_x3f_3726_);
lean_dec(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec(v___y_3721_);
lean_dec(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec(v___y_3716_);
lean_dec(v_x_3534_);
v___x_3735_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set(v___x_3736_, 1, v___y_3728_);
return v___x_3736_;
}
else
{
lean_object* v_val_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3768_; 
v_val_3737_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3739_ = v___x_3734_;
v_isShared_3740_ = v_isSharedCheck_3768_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_val_3737_);
lean_dec(v___x_3734_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3768_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v___x_3741_ = lean_unsigned_to_nat(8u);
v___x_3742_ = l_Lean_Syntax_getArg(v_x_3534_, v___x_3741_);
lean_dec(v_x_3534_);
v___x_3743_ = ((lean_object*)(l_Lean_Fmt_fmtElab___closed__3));
lean_inc(v___x_3742_);
v___x_3744_ = l_Lean_Syntax_isOfKind(v___x_3742_, v___x_3743_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec(v___x_3742_);
lean_del_object(v___x_3739_);
lean_dec(v_val_3737_);
lean_dec(v_namedPrio_x3f_3726_);
lean_dec(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec(v___y_3721_);
lean_dec(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec(v___y_3716_);
v___x_3745_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
lean_ctor_set(v___x_3746_, 1, v___y_3728_);
return v___x_3746_;
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3748_; uint8_t v___x_3749_; 
v___x_3747_ = l_Lean_Syntax_getArg(v___x_3742_, v___y_3720_);
v___x_3748_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v___x_3747_);
v___x_3749_ = l_Lean_Syntax_isOfKind(v___x_3747_, v___x_3748_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
lean_dec(v___x_3747_);
lean_dec(v___x_3742_);
lean_del_object(v___x_3739_);
lean_dec(v_val_3737_);
lean_dec(v_namedPrio_x3f_3726_);
lean_dec(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec(v___y_3721_);
lean_dec(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec(v___y_3716_);
v___x_3750_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_ctor_set(v___x_3751_, 1, v___y_3728_);
return v___x_3751_;
}
else
{
lean_object* v_colonTk_3752_; lean_object* v___x_3753_; uint8_t v___x_3754_; 
v_colonTk_3752_ = l_Lean_Syntax_getArg(v___x_3742_, v___x_3714_);
v___x_3753_ = l_Lean_Syntax_getArg(v___x_3742_, v___y_3722_);
v___x_3754_ = l_Lean_Syntax_isNone(v___x_3753_);
if (v___x_3754_ == 0)
{
uint8_t v___x_3755_; 
lean_inc(v___x_3753_);
v___x_3755_ = l_Lean_Syntax_matchesNull(v___x_3753_, v___y_3722_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
lean_dec(v___x_3753_);
lean_dec(v_colonTk_3752_);
lean_dec(v___x_3747_);
lean_dec(v___x_3742_);
lean_del_object(v___x_3739_);
lean_dec(v_val_3737_);
lean_dec(v_namedPrio_x3f_3726_);
lean_dec(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec(v___y_3721_);
lean_dec(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec(v___y_3716_);
v___x_3756_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set(v___x_3757_, 1, v___y_3728_);
return v___x_3757_;
}
else
{
lean_object* v_expectedType_x3f_3758_; uint8_t v___x_3759_; 
v_expectedType_x3f_3758_ = l_Lean_Syntax_getArg(v___x_3753_, v___y_3720_);
lean_inc(v_expectedType_x3f_3758_);
v___x_3759_ = l_Lean_Syntax_isOfKind(v_expectedType_x3f_3758_, v___x_3748_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
lean_dec(v_expectedType_x3f_3758_);
lean_dec(v___x_3753_);
lean_dec(v_colonTk_3752_);
lean_dec(v___x_3747_);
lean_dec(v___x_3742_);
lean_del_object(v___x_3739_);
lean_dec(v_val_3737_);
lean_dec(v_namedPrio_x3f_3726_);
lean_dec(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec(v___y_3721_);
lean_dec(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec(v___y_3716_);
v___x_3760_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
lean_ctor_set(v___x_3761_, 1, v___y_3728_);
return v___x_3761_;
}
else
{
lean_object* v_leTk_x3f_3762_; lean_object* v___x_3764_; 
v_leTk_x3f_3762_ = l_Lean_Syntax_getArg(v___x_3753_, v___x_3714_);
lean_dec(v___x_3753_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v_leTk_x3f_3762_);
v___x_3764_ = v___x_3739_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_leTk_x3f_3762_);
v___x_3764_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3765_; 
v___x_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3765_, 0, v_expectedType_x3f_3758_);
v___y_3680_ = v___y_3718_;
v___y_3681_ = v___y_3720_;
v___y_3682_ = v___x_3747_;
v___y_3683_ = v_colonTk_3752_;
v___y_3684_ = v___x_3742_;
v___y_3685_ = v_val_3737_;
v___y_3686_ = v___y_3724_;
v___y_3687_ = v_namedPrio_x3f_3726_;
v___y_3688_ = v___y_3716_;
v___y_3689_ = v___y_3717_;
v___y_3690_ = v___y_3719_;
v___y_3691_ = v___y_3721_;
v___y_3692_ = v___y_3722_;
v___y_3693_ = v___y_3723_;
v___y_3694_ = v___y_3725_;
v_leTk_x3f_3695_ = v___x_3764_;
v_expectedType_x3f_3696_ = v___x_3765_;
v___y_3697_ = v___y_3727_;
v___y_3698_ = v___y_3728_;
goto v___jp_3679_;
}
}
}
}
else
{
lean_object* v___x_3767_; 
lean_dec(v___x_3753_);
lean_del_object(v___x_3739_);
v___x_3767_ = lean_box(0);
v___y_3680_ = v___y_3718_;
v___y_3681_ = v___y_3720_;
v___y_3682_ = v___x_3747_;
v___y_3683_ = v_colonTk_3752_;
v___y_3684_ = v___x_3742_;
v___y_3685_ = v_val_3737_;
v___y_3686_ = v___y_3724_;
v___y_3687_ = v_namedPrio_x3f_3726_;
v___y_3688_ = v___y_3716_;
v___y_3689_ = v___y_3717_;
v___y_3690_ = v___y_3719_;
v___y_3691_ = v___y_3721_;
v___y_3692_ = v___y_3722_;
v___y_3693_ = v___y_3723_;
v___y_3694_ = v___y_3725_;
v_leTk_x3f_3695_ = v___x_3767_;
v_expectedType_x3f_3696_ = v___x_3767_;
v___y_3697_ = v___y_3727_;
v___y_3698_ = v___y_3728_;
goto v___jp_3679_;
}
}
}
}
}
}
v___jp_3769_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; uint8_t v___x_3784_; 
v___x_3782_ = lean_unsigned_to_nat(6u);
v___x_3783_ = l_Lean_Syntax_getArg(v_x_3534_, v___x_3782_);
v___x_3784_ = l_Lean_Syntax_isNone(v___x_3783_);
if (v___x_3784_ == 0)
{
uint8_t v___x_3785_; 
lean_inc(v___x_3783_);
v___x_3785_ = l_Lean_Syntax_matchesNull(v___x_3783_, v___y_3772_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
lean_dec(v___x_3783_);
lean_dec(v_namedName_x3f_3779_);
lean_dec(v___y_3778_);
lean_dec(v___y_3776_);
lean_dec(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec(v___y_3770_);
lean_dec(v_x_3534_);
v___x_3786_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
lean_ctor_set(v___x_3787_, 1, v___y_3781_);
return v___x_3787_;
}
else
{
lean_object* v_namedPrio_x3f_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v_namedPrio_x3f_3788_ = l_Lean_Syntax_getArg(v___x_3783_, v___x_3714_);
lean_dec(v___x_3783_);
v___x_3789_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__3));
lean_inc(v_namedPrio_x3f_3788_);
v___x_3790_ = l_Lean_Syntax_isOfKind(v_namedPrio_x3f_3788_, v___x_3789_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_dec(v_namedPrio_x3f_3788_);
lean_dec(v_namedName_x3f_3779_);
lean_dec(v___y_3778_);
lean_dec(v___y_3776_);
lean_dec(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec(v___y_3770_);
lean_dec(v_x_3534_);
v___x_3791_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
lean_ctor_set(v___x_3792_, 1, v___y_3781_);
return v___x_3792_;
}
else
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3793_, 0, v_namedPrio_x3f_3788_);
v___y_3716_ = v___y_3770_;
v___y_3717_ = v___y_3771_;
v___y_3718_ = v_namedName_x3f_3779_;
v___y_3719_ = v___y_3773_;
v___y_3720_ = v___y_3772_;
v___y_3721_ = v___y_3774_;
v___y_3722_ = v___y_3775_;
v___y_3723_ = v___y_3777_;
v___y_3724_ = v___y_3776_;
v___y_3725_ = v___y_3778_;
v_namedPrio_x3f_3726_ = v___x_3793_;
v___y_3727_ = v___y_3780_;
v___y_3728_ = v___y_3781_;
goto v___jp_3715_;
}
}
}
else
{
lean_object* v___x_3794_; 
lean_dec(v___x_3783_);
v___x_3794_ = lean_box(0);
v___y_3716_ = v___y_3770_;
v___y_3717_ = v___y_3771_;
v___y_3718_ = v_namedName_x3f_3779_;
v___y_3719_ = v___y_3773_;
v___y_3720_ = v___y_3772_;
v___y_3721_ = v___y_3774_;
v___y_3722_ = v___y_3775_;
v___y_3723_ = v___y_3777_;
v___y_3724_ = v___y_3776_;
v___y_3725_ = v___y_3778_;
v_namedPrio_x3f_3726_ = v___x_3794_;
v___y_3727_ = v___y_3780_;
v___y_3728_ = v___y_3781_;
goto v___jp_3715_;
}
}
v___jp_3795_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
v___x_3807_ = lean_unsigned_to_nat(5u);
v___x_3808_ = l_Lean_Syntax_getArg(v_x_3534_, v___x_3807_);
v___x_3809_ = l_Lean_Syntax_isNone(v___x_3808_);
if (v___x_3809_ == 0)
{
uint8_t v___x_3810_; 
lean_inc(v___x_3808_);
v___x_3810_ = l_Lean_Syntax_matchesNull(v___x_3808_, v___y_3799_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_dec(v___x_3808_);
lean_dec(v_prec_x3f_3804_);
lean_dec(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec(v___y_3798_);
lean_dec(v___y_3796_);
lean_dec(v_x_3534_);
v___x_3811_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
lean_ctor_set(v___x_3812_, 1, v___y_3806_);
return v___x_3812_;
}
else
{
lean_object* v_namedName_x3f_3813_; lean_object* v___x_3814_; uint8_t v___x_3815_; 
v_namedName_x3f_3813_ = l_Lean_Syntax_getArg(v___x_3808_, v___x_3714_);
lean_dec(v___x_3808_);
v___x_3814_ = ((lean_object*)(l_Lean_Fmt_fmtNamedName___closed__2));
lean_inc(v_namedName_x3f_3813_);
v___x_3815_ = l_Lean_Syntax_isOfKind(v_namedName_x3f_3813_, v___x_3814_);
if (v___x_3815_ == 0)
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
lean_dec(v_namedName_x3f_3813_);
lean_dec(v_prec_x3f_3804_);
lean_dec(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec(v___y_3798_);
lean_dec(v___y_3796_);
lean_dec(v_x_3534_);
v___x_3816_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
lean_ctor_set(v___x_3817_, 1, v___y_3806_);
return v___x_3817_;
}
else
{
lean_object* v___x_3818_; 
v___x_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3818_, 0, v_namedName_x3f_3813_);
v___y_3770_ = v___y_3796_;
v___y_3771_ = v___y_3797_;
v___y_3772_ = v___y_3799_;
v___y_3773_ = v___y_3798_;
v___y_3774_ = v_prec_x3f_3804_;
v___y_3775_ = v___y_3800_;
v___y_3776_ = v___y_3802_;
v___y_3777_ = v___y_3801_;
v___y_3778_ = v___y_3803_;
v_namedName_x3f_3779_ = v___x_3818_;
v___y_3780_ = v___y_3805_;
v___y_3781_ = v___y_3806_;
goto v___jp_3769_;
}
}
}
else
{
lean_object* v___x_3819_; 
lean_dec(v___x_3808_);
v___x_3819_ = lean_box(0);
v___y_3770_ = v___y_3796_;
v___y_3771_ = v___y_3797_;
v___y_3772_ = v___y_3799_;
v___y_3773_ = v___y_3798_;
v___y_3774_ = v_prec_x3f_3804_;
v___y_3775_ = v___y_3800_;
v___y_3776_ = v___y_3802_;
v___y_3777_ = v___y_3801_;
v___y_3778_ = v___y_3803_;
v_namedName_x3f_3779_ = v___x_3819_;
v___y_3780_ = v___y_3805_;
v___y_3781_ = v___y_3806_;
goto v___jp_3769_;
}
}
v___jp_3820_:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v___x_3826_ = lean_unsigned_to_nat(2u);
v___x_3827_ = l_Lean_Syntax_getArg(v_x_3534_, v___x_3826_);
v___x_3828_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__6));
lean_inc(v___x_3827_);
v___x_3829_ = l_Lean_Syntax_isOfKind(v___x_3827_, v___x_3828_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
lean_dec(v___x_3827_);
lean_dec(v_attributes_x3f_3823_);
lean_dec(v___y_3822_);
lean_dec(v_x_3534_);
v___x_3830_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
lean_ctor_set(v___x_3831_, 1, v___y_3825_);
return v___x_3831_;
}
else
{
lean_object* v___x_3832_; lean_object* v_elabTk_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v___x_3832_ = lean_unsigned_to_nat(3u);
v_elabTk_3833_ = l_Lean_Syntax_getArg(v_x_3534_, v___x_3832_);
v___x_3834_ = lean_unsigned_to_nat(4u);
v___x_3835_ = l_Lean_Syntax_getArg(v_x_3534_, v___x_3834_);
v___x_3836_ = l_Lean_Syntax_isNone(v___x_3835_);
if (v___x_3836_ == 0)
{
uint8_t v___x_3837_; 
lean_inc(v___x_3835_);
v___x_3837_ = l_Lean_Syntax_matchesNull(v___x_3835_, v___y_3821_);
if (v___x_3837_ == 0)
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
lean_dec(v___x_3835_);
lean_dec(v_elabTk_3833_);
lean_dec(v___x_3827_);
lean_dec(v_attributes_x3f_3823_);
lean_dec(v___y_3822_);
lean_dec(v_x_3534_);
v___x_3838_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3838_);
lean_ctor_set(v___x_3839_, 1, v___y_3825_);
return v___x_3839_;
}
else
{
lean_object* v_prec_x3f_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v_prec_x3f_3840_ = l_Lean_Syntax_getArg(v___x_3835_, v___x_3714_);
lean_dec(v___x_3835_);
v___x_3841_ = ((lean_object*)(l_Lean_Fmt_fmtPrecedence___closed__3));
lean_inc(v_prec_x3f_3840_);
v___x_3842_ = l_Lean_Syntax_isOfKind(v_prec_x3f_3840_, v___x_3841_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
lean_dec(v_prec_x3f_3840_);
lean_dec(v_elabTk_3833_);
lean_dec(v___x_3827_);
lean_dec(v_attributes_x3f_3823_);
lean_dec(v___y_3822_);
lean_dec(v_x_3534_);
v___x_3843_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3843_);
lean_ctor_set(v___x_3844_, 1, v___y_3825_);
return v___x_3844_;
}
else
{
lean_object* v___x_3845_; 
v___x_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3845_, 0, v_prec_x3f_3840_);
v___y_3796_ = v_elabTk_3833_;
v___y_3797_ = v___x_3832_;
v___y_3798_ = v___y_3822_;
v___y_3799_ = v___y_3821_;
v___y_3800_ = v___x_3826_;
v___y_3801_ = v___x_3834_;
v___y_3802_ = v___x_3827_;
v___y_3803_ = v_attributes_x3f_3823_;
v_prec_x3f_3804_ = v___x_3845_;
v___y_3805_ = v___y_3824_;
v___y_3806_ = v___y_3825_;
goto v___jp_3795_;
}
}
}
else
{
lean_object* v___x_3846_; 
lean_dec(v___x_3835_);
v___x_3846_ = lean_box(0);
v___y_3796_ = v_elabTk_3833_;
v___y_3797_ = v___x_3832_;
v___y_3798_ = v___y_3822_;
v___y_3799_ = v___y_3821_;
v___y_3800_ = v___x_3826_;
v___y_3801_ = v___x_3834_;
v___y_3802_ = v___x_3827_;
v___y_3803_ = v_attributes_x3f_3823_;
v_prec_x3f_3804_ = v___x_3846_;
v___y_3805_ = v___y_3824_;
v___y_3806_ = v___y_3825_;
goto v___jp_3795_;
}
}
}
v___jp_3847_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; 
v___x_3851_ = lean_unsigned_to_nat(1u);
v___x_3852_ = l_Lean_Syntax_getArg(v_x_3534_, v___x_3851_);
v___x_3853_ = l_Lean_Syntax_isNone(v___x_3852_);
if (v___x_3853_ == 0)
{
uint8_t v___x_3854_; 
lean_inc(v___x_3852_);
v___x_3854_ = l_Lean_Syntax_matchesNull(v___x_3852_, v___x_3851_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_dec(v___x_3852_);
lean_dec(v_docComment_x3f_3848_);
lean_dec(v_x_3534_);
v___x_3855_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
lean_ctor_set(v___x_3856_, 1, v___y_3850_);
return v___x_3856_;
}
else
{
lean_object* v_attributes_x3f_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v_attributes_x3f_3857_ = l_Lean_Syntax_getArg(v___x_3852_, v___x_3714_);
lean_dec(v___x_3852_);
v___x_3858_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__8));
lean_inc(v_attributes_x3f_3857_);
v___x_3859_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_3857_, v___x_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
lean_dec(v_attributes_x3f_3857_);
lean_dec(v_docComment_x3f_3848_);
lean_dec(v_x_3534_);
v___x_3860_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
lean_ctor_set(v___x_3861_, 1, v___y_3850_);
return v___x_3861_;
}
else
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3862_, 0, v_attributes_x3f_3857_);
v___y_3821_ = v___x_3851_;
v___y_3822_ = v_docComment_x3f_3848_;
v_attributes_x3f_3823_ = v___x_3862_;
v___y_3824_ = v___y_3849_;
v___y_3825_ = v___y_3850_;
goto v___jp_3820_;
}
}
}
else
{
lean_object* v___x_3863_; 
lean_dec(v___x_3852_);
v___x_3863_ = lean_box(0);
v___y_3821_ = v___x_3851_;
v___y_3822_ = v_docComment_x3f_3848_;
v_attributes_x3f_3823_ = v___x_3863_;
v___y_3824_ = v___y_3849_;
v___y_3825_ = v___y_3850_;
goto v___jp_3820_;
}
}
}
v___jp_3537_:
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_Fmt_fmtElabDeclarationSignature(v___y_3547_, v___y_3538_, v___y_3541_, v___y_3542_, v___y_3548_, v___y_3550_, v___y_3544_, v___y_3553_, v___y_3543_, v___y_3551_);
lean_dec_ref(v___y_3541_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v_a_3556_; uint8_t v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
v_a_3556_ = lean_ctor_get(v___x_3554_, 1);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3554_, 2);
v___x_3557_ = 0;
v___x_3558_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_3555_, v___y_3546_, v___y_3539_, v___x_3557_);
v___x_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___y_3545_);
v___x_3560_ = lean_mk_empty_array_with_capacity(v___y_3540_);
v___x_3561_ = lean_array_push(v___x_3560_, v___x_3559_);
v___x_3562_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_3549_, v___y_3552_, v___x_3561_, v___x_3558_, v___y_3543_, v_a_3556_);
lean_dec_ref(v___x_3561_);
return v___x_3562_;
}
else
{
lean_dec(v___y_3552_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3546_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3539_);
return v___x_3554_;
}
}
v___jp_3563_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3582_ = lean_mk_empty_array_with_capacity(v___y_3577_);
v___x_3583_ = lean_array_push(v___x_3582_, v___y_3580_);
v___x_3584_ = lean_array_push(v___x_3583_, v___y_3575_);
v___x_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3585_, 0, v___y_3569_);
v___x_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3586_, 0, v___y_3566_);
if (lean_obj_tag(v___y_3578_) == 0)
{
lean_object* v___x_3587_; 
v___x_3587_ = lean_box(0);
v___y_3538_ = v___y_3581_;
v___y_3539_ = v___y_3564_;
v___y_3540_ = v___y_3565_;
v___y_3541_ = v___x_3584_;
v___y_3542_ = v___y_3567_;
v___y_3543_ = v___y_3568_;
v___y_3544_ = v___y_3570_;
v___y_3545_ = v___y_3571_;
v___y_3546_ = v___y_3572_;
v___y_3547_ = v___y_3573_;
v___y_3548_ = v___x_3585_;
v___y_3549_ = v___y_3574_;
v___y_3550_ = v___x_3586_;
v___y_3551_ = v___y_3576_;
v___y_3552_ = v___y_3579_;
v___y_3553_ = v___x_3587_;
goto v___jp_3537_;
}
else
{
lean_object* v_val_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
v_val_3588_ = lean_ctor_get(v___y_3578_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___y_3578_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___y_3578_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_val_3588_);
lean_dec(v___y_3578_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_val_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
v___y_3538_ = v___y_3581_;
v___y_3539_ = v___y_3564_;
v___y_3540_ = v___y_3565_;
v___y_3541_ = v___x_3584_;
v___y_3542_ = v___y_3567_;
v___y_3543_ = v___y_3568_;
v___y_3544_ = v___y_3570_;
v___y_3545_ = v___y_3571_;
v___y_3546_ = v___y_3572_;
v___y_3547_ = v___y_3573_;
v___y_3548_ = v___x_3585_;
v___y_3549_ = v___y_3574_;
v___y_3550_ = v___x_3586_;
v___y_3551_ = v___y_3576_;
v___y_3552_ = v___y_3579_;
v___y_3553_ = v___x_3593_;
goto v___jp_3537_;
}
}
}
}
v___jp_3596_:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_Fmt_fmt_x3f(v___y_3614_, v___y_3599_, v___y_3604_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v_a_3617_; lean_object* v___x_3618_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
v_a_3617_ = lean_ctor_get(v___x_3615_, 1);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3615_, 2);
v___x_3618_ = l_Lean_Fmt_fmtArray___redArg(v___y_3602_, v___y_3599_, v_a_3617_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v_a_3620_; lean_object* v___x_3621_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
v_a_3620_ = lean_ctor_get(v___x_3618_, 1);
lean_inc(v_a_3620_);
lean_dec_ref_known(v___x_3618_, 2);
v___x_3621_ = l_Lean_Fmt_fmt(v___y_3605_, v___y_3599_, v_a_3620_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v_a_3623_; lean_object* v___x_3624_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
v_a_3623_ = lean_ctor_get(v___x_3621_, 1);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3621_, 2);
v___x_3624_ = l_Lean_Fmt_fmt(v___y_3606_, v___y_3599_, v_a_3623_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v_a_3626_; lean_object* v___x_3627_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
v_a_3626_ = lean_ctor_get(v___x_3624_, 1);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3624_, 2);
v___x_3627_ = l_Lean_Fmt_Layouts_fill(v_a_3619_);
lean_dec(v_a_3619_);
if (lean_obj_tag(v___y_3609_) == 0)
{
lean_object* v___x_3628_; 
v___x_3628_ = lean_box(0);
v___y_3564_ = v_a_3625_;
v___y_3565_ = v___y_3597_;
v___y_3566_ = v___y_3598_;
v___y_3567_ = v___x_3627_;
v___y_3568_ = v___y_3599_;
v___y_3569_ = v___y_3600_;
v___y_3570_ = v___y_3601_;
v___y_3571_ = v___y_3603_;
v___y_3572_ = v_a_3622_;
v___y_3573_ = v___y_3607_;
v___y_3574_ = v___y_3608_;
v___y_3575_ = v_a_3616_;
v___y_3576_ = v_a_3626_;
v___y_3577_ = v___y_3610_;
v___y_3578_ = v___y_3611_;
v___y_3579_ = v___y_3613_;
v___y_3580_ = v___y_3612_;
v___y_3581_ = v___x_3628_;
goto v___jp_3563_;
}
else
{
lean_object* v_val_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
v_val_3629_ = lean_ctor_get(v___y_3609_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___y_3609_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___y_3609_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_val_3629_);
lean_dec(v___y_3609_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_val_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
v___y_3564_ = v_a_3625_;
v___y_3565_ = v___y_3597_;
v___y_3566_ = v___y_3598_;
v___y_3567_ = v___x_3627_;
v___y_3568_ = v___y_3599_;
v___y_3569_ = v___y_3600_;
v___y_3570_ = v___y_3601_;
v___y_3571_ = v___y_3603_;
v___y_3572_ = v_a_3622_;
v___y_3573_ = v___y_3607_;
v___y_3574_ = v___y_3608_;
v___y_3575_ = v_a_3616_;
v___y_3576_ = v_a_3626_;
v___y_3577_ = v___y_3610_;
v___y_3578_ = v___y_3611_;
v___y_3579_ = v___y_3613_;
v___y_3580_ = v___y_3612_;
v___y_3581_ = v___x_3634_;
goto v___jp_3563_;
}
}
}
}
else
{
lean_dec(v_a_3622_);
lean_dec(v_a_3619_);
lean_dec(v_a_3616_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec(v___y_3603_);
lean_dec(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec(v___y_3598_);
return v___x_3624_;
}
}
else
{
lean_dec(v_a_3619_);
lean_dec(v_a_3616_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec(v___y_3603_);
lean_dec(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec(v___y_3598_);
return v___x_3621_;
}
}
else
{
lean_object* v_a_3637_; lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec(v_a_3616_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec(v___y_3603_);
lean_dec(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec(v___y_3598_);
v_a_3637_ = lean_ctor_get(v___x_3618_, 0);
v_a_3638_ = lean_ctor_get(v___x_3618_, 1);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3618_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_inc(v_a_3637_);
lean_dec(v___x_3618_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3637_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec(v___y_3598_);
return v___x_3615_;
}
}
v___jp_3646_:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_Fmt_fmt_x3f(v___y_3664_, v___y_3649_, v___y_3654_);
if (lean_obj_tag(v___x_3665_) == 0)
{
if (lean_obj_tag(v___y_3657_) == 0)
{
lean_object* v_a_3666_; lean_object* v_a_3667_; lean_object* v___x_3668_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
v_a_3667_ = lean_ctor_get(v___x_3665_, 1);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3665_, 2);
v___x_3668_ = lean_box(0);
v___y_3597_ = v___y_3647_;
v___y_3598_ = v___y_3648_;
v___y_3599_ = v___y_3649_;
v___y_3600_ = v___y_3650_;
v___y_3601_ = v___y_3651_;
v___y_3602_ = v___y_3652_;
v___y_3603_ = v___y_3653_;
v___y_3604_ = v_a_3667_;
v___y_3605_ = v___y_3655_;
v___y_3606_ = v___y_3656_;
v___y_3607_ = v___y_3658_;
v___y_3608_ = v___y_3659_;
v___y_3609_ = v___y_3660_;
v___y_3610_ = v___y_3661_;
v___y_3611_ = v___y_3662_;
v___y_3612_ = v_a_3666_;
v___y_3613_ = v___y_3663_;
v___y_3614_ = v___x_3668_;
goto v___jp_3596_;
}
else
{
lean_object* v_a_3669_; lean_object* v_a_3670_; lean_object* v_val_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
v_a_3669_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3669_);
v_a_3670_ = lean_ctor_get(v___x_3665_, 1);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3665_, 2);
v_val_3671_ = lean_ctor_get(v___y_3657_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___y_3657_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___y_3657_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_val_3671_);
lean_dec(v___y_3657_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_val_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
v___y_3597_ = v___y_3647_;
v___y_3598_ = v___y_3648_;
v___y_3599_ = v___y_3649_;
v___y_3600_ = v___y_3650_;
v___y_3601_ = v___y_3651_;
v___y_3602_ = v___y_3652_;
v___y_3603_ = v___y_3653_;
v___y_3604_ = v_a_3670_;
v___y_3605_ = v___y_3655_;
v___y_3606_ = v___y_3656_;
v___y_3607_ = v___y_3658_;
v___y_3608_ = v___y_3659_;
v___y_3609_ = v___y_3660_;
v___y_3610_ = v___y_3661_;
v___y_3611_ = v___y_3662_;
v___y_3612_ = v_a_3669_;
v___y_3613_ = v___y_3663_;
v___y_3614_ = v___x_3676_;
goto v___jp_3596_;
}
}
}
}
else
{
lean_dec(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec(v___y_3648_);
return v___x_3665_;
}
}
v___jp_3679_:
{
lean_object* v_darrowTk_3699_; lean_object* v___x_3700_; 
v_darrowTk_3699_ = l_Lean_Syntax_getArg(v___y_3684_, v___y_3689_);
v___x_3700_ = l_Lean_Syntax_getArg(v___y_3684_, v___y_3693_);
lean_dec(v___y_3684_);
if (lean_obj_tag(v___y_3680_) == 0)
{
lean_object* v___x_3701_; 
v___x_3701_ = lean_box(0);
v___y_3647_ = v___y_3681_;
v___y_3648_ = v___y_3682_;
v___y_3649_ = v___y_3697_;
v___y_3650_ = v___y_3683_;
v___y_3651_ = v_leTk_x3f_3695_;
v___y_3652_ = v___y_3685_;
v___y_3653_ = v___y_3686_;
v___y_3654_ = v___y_3698_;
v___y_3655_ = v_darrowTk_3699_;
v___y_3656_ = v___x_3700_;
v___y_3657_ = v___y_3687_;
v___y_3658_ = v___y_3688_;
v___y_3659_ = v___y_3690_;
v___y_3660_ = v___y_3691_;
v___y_3661_ = v___y_3692_;
v___y_3662_ = v_expectedType_x3f_3696_;
v___y_3663_ = v___y_3694_;
v___y_3664_ = v___x_3701_;
goto v___jp_3646_;
}
else
{
lean_object* v_val_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
v_val_3702_ = lean_ctor_get(v___y_3680_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___y_3680_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___y_3680_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_val_3702_);
lean_dec(v___y_3680_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_val_3702_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
v___y_3647_ = v___y_3681_;
v___y_3648_ = v___y_3682_;
v___y_3649_ = v___y_3697_;
v___y_3650_ = v___y_3683_;
v___y_3651_ = v_leTk_x3f_3695_;
v___y_3652_ = v___y_3685_;
v___y_3653_ = v___y_3686_;
v___y_3654_ = v___y_3698_;
v___y_3655_ = v_darrowTk_3699_;
v___y_3656_ = v___x_3700_;
v___y_3657_ = v___y_3687_;
v___y_3658_ = v___y_3688_;
v___y_3659_ = v___y_3690_;
v___y_3660_ = v___y_3691_;
v___y_3661_ = v___y_3692_;
v___y_3662_ = v_expectedType_x3f_3696_;
v___y_3663_ = v___y_3694_;
v___y_3664_ = v___x_3707_;
goto v___jp_3646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElab___boxed(lean_object* v_x_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lean_Fmt_fmtElab(v_x_3877_, v_a_3878_, v_a_3879_);
lean_dec_ref(v_a_3878_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1(){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3887_ = l_Lean_Fmt_fmtAttribute;
v___x_3888_ = ((lean_object*)(l_Lean_Fmt_fmtElab___closed__1));
v___x_3889_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___closed__1));
v___x_3890_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtElab___boxed), 3, 0);
v___x_3891_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3887_, v___x_3888_, v___x_3889_, v___x_3890_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1___boxed(lean_object* v_a_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1();
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredicate(lean_object* v_x_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v_namedPrio_x3f_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___x_4036_; uint8_t v___x_4037_; 
v___x_4036_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredicate___closed__1));
lean_inc(v_x_3900_);
v___x_4037_ = l_Lean_Syntax_isOfKind(v_x_3900_, v___x_4036_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_dec(v_x_3900_);
v___x_4038_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
lean_ctor_set(v___x_4039_, 1, v_a_3902_);
return v___x_4039_;
}
else
{
lean_object* v___x_4040_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v_namedName_x3f_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v_attrKind_x3f_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v_attributes_x3f_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v_docComment_x3f_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___x_4121_; uint8_t v___x_4122_; 
v___x_4040_ = lean_unsigned_to_nat(0u);
v___x_4121_ = l_Lean_Syntax_getArg(v_x_3900_, v___x_4040_);
v___x_4122_ = l_Lean_Syntax_isNone(v___x_4121_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; uint8_t v___x_4124_; 
v___x_4123_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4121_);
v___x_4124_ = l_Lean_Syntax_matchesNull(v___x_4121_, v___x_4123_);
if (v___x_4124_ == 0)
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
lean_dec(v___x_4121_);
lean_dec(v_x_3900_);
v___x_4125_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
lean_ctor_set(v___x_4126_, 1, v_a_3902_);
return v___x_4126_;
}
else
{
lean_object* v_docComment_x3f_4127_; lean_object* v___x_4128_; uint8_t v___x_4129_; 
v_docComment_x3f_4127_ = l_Lean_Syntax_getArg(v___x_4121_, v___x_4040_);
lean_dec(v___x_4121_);
v___x_4128_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__10));
lean_inc(v_docComment_x3f_4127_);
v___x_4129_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_4127_, v___x_4128_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
lean_dec(v_docComment_x3f_4127_);
lean_dec(v_x_3900_);
v___x_4130_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
lean_ctor_set(v___x_4131_, 1, v_a_3902_);
return v___x_4131_;
}
else
{
lean_object* v___x_4132_; 
v___x_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4132_, 0, v_docComment_x3f_4127_);
v_docComment_x3f_4105_ = v___x_4132_;
v___y_4106_ = v_a_3901_;
v___y_4107_ = v_a_3902_;
goto v___jp_4104_;
}
}
}
else
{
lean_object* v___x_4133_; 
lean_dec(v___x_4121_);
v___x_4133_ = lean_box(0);
v_docComment_x3f_4105_ = v___x_4133_;
v___y_4106_ = v_a_3901_;
v___y_4107_ = v_a_3902_;
goto v___jp_4104_;
}
v___jp_4041_:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4050_ = lean_unsigned_to_nat(5u);
v___x_4051_ = l_Lean_Syntax_getArg(v_x_3900_, v___x_4050_);
v___x_4052_ = l_Lean_Syntax_isNone(v___x_4051_);
if (v___x_4052_ == 0)
{
uint8_t v___x_4053_; 
lean_inc(v___x_4051_);
v___x_4053_ = l_Lean_Syntax_matchesNull(v___x_4051_, v___y_4044_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
lean_dec(v___x_4051_);
lean_dec(v_namedName_x3f_4047_);
lean_dec(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec(v_x_3900_);
v___x_4054_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
lean_ctor_set(v___x_4055_, 1, v___y_4049_);
return v___x_4055_;
}
else
{
lean_object* v_namedPrio_x3f_4056_; lean_object* v___x_4057_; uint8_t v___x_4058_; 
v_namedPrio_x3f_4056_ = l_Lean_Syntax_getArg(v___x_4051_, v___x_4040_);
lean_dec(v___x_4051_);
v___x_4057_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__3));
lean_inc(v_namedPrio_x3f_4056_);
v___x_4058_ = l_Lean_Syntax_isOfKind(v_namedPrio_x3f_4056_, v___x_4057_);
if (v___x_4058_ == 0)
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
lean_dec(v_namedPrio_x3f_4056_);
lean_dec(v_namedName_x3f_4047_);
lean_dec(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec(v_x_3900_);
v___x_4059_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4059_);
lean_ctor_set(v___x_4060_, 1, v___y_4049_);
return v___x_4060_;
}
else
{
lean_object* v___x_4061_; 
v___x_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4061_, 0, v_namedPrio_x3f_4056_);
v___y_3999_ = v___y_4043_;
v___y_4000_ = v___y_4042_;
v___y_4001_ = v___y_4044_;
v___y_4002_ = v___y_4045_;
v___y_4003_ = v_namedName_x3f_4047_;
v___y_4004_ = v___y_4046_;
v_namedPrio_x3f_4005_ = v___x_4061_;
v___y_4006_ = v___y_4048_;
v___y_4007_ = v___y_4049_;
goto v___jp_3998_;
}
}
}
else
{
lean_object* v___x_4062_; 
lean_dec(v___x_4051_);
v___x_4062_ = lean_box(0);
v___y_3999_ = v___y_4043_;
v___y_4000_ = v___y_4042_;
v___y_4001_ = v___y_4044_;
v___y_4002_ = v___y_4045_;
v___y_4003_ = v_namedName_x3f_4047_;
v___y_4004_ = v___y_4046_;
v_namedPrio_x3f_4005_ = v___x_4062_;
v___y_4006_ = v___y_4048_;
v___y_4007_ = v___y_4049_;
goto v___jp_3998_;
}
}
v___jp_4063_:
{
lean_object* v___x_4070_; lean_object* v_binderPredicateTk_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; uint8_t v___x_4074_; 
v___x_4070_ = lean_unsigned_to_nat(3u);
v_binderPredicateTk_4071_ = l_Lean_Syntax_getArg(v_x_3900_, v___x_4070_);
v___x_4072_ = lean_unsigned_to_nat(4u);
v___x_4073_ = l_Lean_Syntax_getArg(v_x_3900_, v___x_4072_);
v___x_4074_ = l_Lean_Syntax_isNone(v___x_4073_);
if (v___x_4074_ == 0)
{
uint8_t v___x_4075_; 
lean_inc(v___x_4073_);
v___x_4075_ = l_Lean_Syntax_matchesNull(v___x_4073_, v___y_4065_);
if (v___x_4075_ == 0)
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_dec(v___x_4073_);
lean_dec(v_binderPredicateTk_4071_);
lean_dec(v_attrKind_x3f_4067_);
lean_dec(v___y_4066_);
lean_dec(v___y_4064_);
lean_dec(v_x_3900_);
v___x_4076_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
lean_ctor_set(v___x_4077_, 1, v___y_4069_);
return v___x_4077_;
}
else
{
lean_object* v_namedName_x3f_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; 
v_namedName_x3f_4078_ = l_Lean_Syntax_getArg(v___x_4073_, v___x_4040_);
lean_dec(v___x_4073_);
v___x_4079_ = ((lean_object*)(l_Lean_Fmt_fmtNamedName___closed__2));
lean_inc(v_namedName_x3f_4078_);
v___x_4080_ = l_Lean_Syntax_isOfKind(v_namedName_x3f_4078_, v___x_4079_);
if (v___x_4080_ == 0)
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
lean_dec(v_namedName_x3f_4078_);
lean_dec(v_binderPredicateTk_4071_);
lean_dec(v_attrKind_x3f_4067_);
lean_dec(v___y_4066_);
lean_dec(v___y_4064_);
lean_dec(v_x_3900_);
v___x_4081_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
lean_ctor_set(v___x_4082_, 1, v___y_4069_);
return v___x_4082_;
}
else
{
lean_object* v___x_4083_; 
v___x_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4083_, 0, v_namedName_x3f_4078_);
v___y_4042_ = v___y_4064_;
v___y_4043_ = v_attrKind_x3f_4067_;
v___y_4044_ = v___y_4065_;
v___y_4045_ = v_binderPredicateTk_4071_;
v___y_4046_ = v___y_4066_;
v_namedName_x3f_4047_ = v___x_4083_;
v___y_4048_ = v___y_4068_;
v___y_4049_ = v___y_4069_;
goto v___jp_4041_;
}
}
}
else
{
lean_object* v___x_4084_; 
lean_dec(v___x_4073_);
v___x_4084_ = lean_box(0);
v___y_4042_ = v___y_4064_;
v___y_4043_ = v_attrKind_x3f_4067_;
v___y_4044_ = v___y_4065_;
v___y_4045_ = v_binderPredicateTk_4071_;
v___y_4046_ = v___y_4066_;
v_namedName_x3f_4047_ = v___x_4084_;
v___y_4048_ = v___y_4068_;
v___y_4049_ = v___y_4069_;
goto v___jp_4041_;
}
}
v___jp_4085_:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; uint8_t v___x_4093_; 
v___x_4091_ = lean_unsigned_to_nat(2u);
v___x_4092_ = l_Lean_Syntax_getArg(v_x_3900_, v___x_4091_);
v___x_4093_ = l_Lean_Syntax_isNone(v___x_4092_);
if (v___x_4093_ == 0)
{
uint8_t v___x_4094_; 
lean_inc(v___x_4092_);
v___x_4094_ = l_Lean_Syntax_matchesNull(v___x_4092_, v___y_4086_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
lean_dec(v___x_4092_);
lean_dec(v_attributes_x3f_4088_);
lean_dec(v___y_4087_);
lean_dec(v_x_3900_);
v___x_4095_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
lean_ctor_set(v___x_4096_, 1, v___y_4090_);
return v___x_4096_;
}
else
{
lean_object* v_attrKind_x3f_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v_attrKind_x3f_4097_ = l_Lean_Syntax_getArg(v___x_4092_, v___x_4040_);
lean_dec(v___x_4092_);
v___x_4098_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__6));
lean_inc(v_attrKind_x3f_4097_);
v___x_4099_ = l_Lean_Syntax_isOfKind(v_attrKind_x3f_4097_, v___x_4098_);
if (v___x_4099_ == 0)
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
lean_dec(v_attrKind_x3f_4097_);
lean_dec(v_attributes_x3f_4088_);
lean_dec(v___y_4087_);
lean_dec(v_x_3900_);
v___x_4100_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4100_);
lean_ctor_set(v___x_4101_, 1, v___y_4090_);
return v___x_4101_;
}
else
{
lean_object* v___x_4102_; 
v___x_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4102_, 0, v_attrKind_x3f_4097_);
v___y_4064_ = v_attributes_x3f_4088_;
v___y_4065_ = v___y_4086_;
v___y_4066_ = v___y_4087_;
v_attrKind_x3f_4067_ = v___x_4102_;
v___y_4068_ = v___y_4089_;
v___y_4069_ = v___y_4090_;
goto v___jp_4063_;
}
}
}
else
{
lean_object* v___x_4103_; 
lean_dec(v___x_4092_);
v___x_4103_ = lean_box(0);
v___y_4064_ = v_attributes_x3f_4088_;
v___y_4065_ = v___y_4086_;
v___y_4066_ = v___y_4087_;
v_attrKind_x3f_4067_ = v___x_4103_;
v___y_4068_ = v___y_4089_;
v___y_4069_ = v___y_4090_;
goto v___jp_4063_;
}
}
v___jp_4104_:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
v___x_4108_ = lean_unsigned_to_nat(1u);
v___x_4109_ = l_Lean_Syntax_getArg(v_x_3900_, v___x_4108_);
v___x_4110_ = l_Lean_Syntax_isNone(v___x_4109_);
if (v___x_4110_ == 0)
{
uint8_t v___x_4111_; 
lean_inc(v___x_4109_);
v___x_4111_ = l_Lean_Syntax_matchesNull(v___x_4109_, v___x_4108_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
lean_dec(v___x_4109_);
lean_dec(v_docComment_x3f_4105_);
lean_dec(v_x_3900_);
v___x_4112_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
lean_ctor_set(v___x_4113_, 1, v___y_4107_);
return v___x_4113_;
}
else
{
lean_object* v_attributes_x3f_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; 
v_attributes_x3f_4114_ = l_Lean_Syntax_getArg(v___x_4109_, v___x_4040_);
lean_dec(v___x_4109_);
v___x_4115_ = ((lean_object*)(l_Lean_Fmt_fmtMixfix___closed__8));
lean_inc(v_attributes_x3f_4114_);
v___x_4116_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_4114_, v___x_4115_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
lean_dec(v_attributes_x3f_4114_);
lean_dec(v_docComment_x3f_4105_);
lean_dec(v_x_3900_);
v___x_4117_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
lean_ctor_set(v___x_4118_, 1, v___y_4107_);
return v___x_4118_;
}
else
{
lean_object* v___x_4119_; 
v___x_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4119_, 0, v_attributes_x3f_4114_);
v___y_4086_ = v___x_4108_;
v___y_4087_ = v_docComment_x3f_4105_;
v_attributes_x3f_4088_ = v___x_4119_;
v___y_4089_ = v___y_4106_;
v___y_4090_ = v___y_4107_;
goto v___jp_4085_;
}
}
}
else
{
lean_object* v___x_4120_; 
lean_dec(v___x_4109_);
v___x_4120_ = lean_box(0);
v___y_4086_ = v___x_4108_;
v___y_4087_ = v_docComment_x3f_4105_;
v_attributes_x3f_4088_ = v___x_4120_;
v___y_4089_ = v___y_4106_;
v___y_4090_ = v___y_4107_;
goto v___jp_4085_;
}
}
}
v___jp_3903_:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; uint8_t v___x_3923_; lean_object* v___x_3924_; 
v___x_3916_ = lean_mk_empty_array_with_capacity(v___y_3910_);
v___x_3917_ = lean_array_push(v___x_3916_, v___y_3915_);
v___x_3918_ = lean_box(0);
v___x_3919_ = lean_unsigned_to_nat(2u);
v___x_3920_ = lean_mk_empty_array_with_capacity(v___x_3919_);
v___x_3921_ = lean_array_push(v___x_3920_, v___y_3909_);
v___x_3922_ = lean_array_push(v___x_3921_, v___y_3907_);
v___x_3923_ = 0;
v___x_3924_ = l_Lean_Fmt_fmtMetaAssignmentDeclaration(v___y_3913_, v___y_3906_, v___x_3917_, v___y_3911_, v___x_3918_, v___x_3922_, v___y_3905_, v___x_3918_, v___x_3918_, v___y_3912_, v___y_3904_, v___x_3923_, v___y_3908_, v___y_3914_);
lean_dec_ref(v___x_3922_);
lean_dec_ref(v___x_3917_);
return v___x_3924_;
}
v___jp_3925_:
{
lean_object* v___x_3939_; 
v___x_3939_ = l_Lean_Fmt_fmt_x3f(v___y_3938_, v___y_3932_, v___y_3934_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v_a_3941_; lean_object* v___x_3942_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
v_a_3941_ = lean_ctor_get(v___x_3939_, 1);
lean_inc(v_a_3941_);
lean_dec_ref_known(v___x_3939_, 2);
v___x_3942_ = l_Lean_Fmt_fmt(v___y_3935_, v___y_3932_, v_a_3941_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v_a_3944_; lean_object* v___x_3945_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
v_a_3944_ = lean_ctor_get(v___x_3942_, 1);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3942_, 2);
v___x_3945_ = l_Lean_Fmt_fmtArray___redArg(v___y_3927_, v___y_3932_, v_a_3944_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v_a_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
v_a_3947_ = lean_ctor_get(v___x_3945_, 1);
lean_inc(v_a_3947_);
lean_dec_ref_known(v___x_3945_, 2);
v___x_3948_ = lean_mk_empty_array_with_capacity(v___y_3931_);
v___x_3949_ = lean_array_push(v___x_3948_, v_a_3943_);
v___x_3950_ = l_Array_append___redArg(v___x_3949_, v_a_3946_);
lean_dec(v_a_3946_);
v___x_3951_ = l_Lean_Fmt_Layouts_fill(v___x_3950_);
lean_dec_ref(v___x_3950_);
if (lean_obj_tag(v___y_3928_) == 0)
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_box(0);
v___y_3904_ = v___y_3926_;
v___y_3905_ = v___x_3951_;
v___y_3906_ = v___y_3929_;
v___y_3907_ = v_a_3940_;
v___y_3908_ = v___y_3932_;
v___y_3909_ = v___y_3930_;
v___y_3910_ = v___y_3931_;
v___y_3911_ = v___y_3933_;
v___y_3912_ = v___y_3936_;
v___y_3913_ = v___y_3937_;
v___y_3914_ = v_a_3947_;
v___y_3915_ = v___x_3952_;
goto v___jp_3903_;
}
else
{
lean_object* v_val_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
v_val_3953_ = lean_ctor_get(v___y_3928_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___y_3928_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___y_3928_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_val_3953_);
lean_dec(v___y_3928_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_val_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
v___y_3904_ = v___y_3926_;
v___y_3905_ = v___x_3951_;
v___y_3906_ = v___y_3929_;
v___y_3907_ = v_a_3940_;
v___y_3908_ = v___y_3932_;
v___y_3909_ = v___y_3930_;
v___y_3910_ = v___y_3931_;
v___y_3911_ = v___y_3933_;
v___y_3912_ = v___y_3936_;
v___y_3913_ = v___y_3937_;
v___y_3914_ = v_a_3947_;
v___y_3915_ = v___x_3958_;
goto v___jp_3903_;
}
}
}
}
else
{
lean_object* v_a_3961_; lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec(v_a_3943_);
lean_dec(v_a_3940_);
lean_dec(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec(v___y_3926_);
v_a_3961_ = lean_ctor_get(v___x_3945_, 0);
v_a_3962_ = lean_ctor_get(v___x_3945_, 1);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3945_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_inc(v_a_3961_);
lean_dec(v___x_3945_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3961_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
else
{
lean_dec(v_a_3940_);
lean_dec(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
return v___x_3942_;
}
}
else
{
lean_dec(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
return v___x_3939_;
}
}
v___jp_3970_:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Lean_Fmt_fmt_x3f(v___y_3983_, v___y_3976_, v___y_3982_);
if (lean_obj_tag(v___x_3984_) == 0)
{
if (lean_obj_tag(v___y_3981_) == 0)
{
lean_object* v_a_3985_; lean_object* v_a_3986_; lean_object* v___x_3987_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
v_a_3986_ = lean_ctor_get(v___x_3984_, 1);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3984_, 2);
v___x_3987_ = lean_box(0);
v___y_3926_ = v___y_3972_;
v___y_3927_ = v___y_3971_;
v___y_3928_ = v___y_3974_;
v___y_3929_ = v___y_3973_;
v___y_3930_ = v_a_3985_;
v___y_3931_ = v___y_3975_;
v___y_3932_ = v___y_3976_;
v___y_3933_ = v___y_3977_;
v___y_3934_ = v_a_3986_;
v___y_3935_ = v___y_3978_;
v___y_3936_ = v___y_3979_;
v___y_3937_ = v___y_3980_;
v___y_3938_ = v___x_3987_;
goto v___jp_3925_;
}
else
{
lean_object* v_a_3988_; lean_object* v_a_3989_; lean_object* v_val_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
v_a_3988_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3988_);
v_a_3989_ = lean_ctor_get(v___x_3984_, 1);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___x_3984_, 2);
v_val_3990_ = lean_ctor_get(v___y_3981_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___y_3981_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___y_3981_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_val_3990_);
lean_dec(v___y_3981_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_val_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
v___y_3926_ = v___y_3972_;
v___y_3927_ = v___y_3971_;
v___y_3928_ = v___y_3974_;
v___y_3929_ = v___y_3973_;
v___y_3930_ = v_a_3988_;
v___y_3931_ = v___y_3975_;
v___y_3932_ = v___y_3976_;
v___y_3933_ = v___y_3977_;
v___y_3934_ = v_a_3989_;
v___y_3935_ = v___y_3978_;
v___y_3936_ = v___y_3979_;
v___y_3937_ = v___y_3980_;
v___y_3938_ = v___x_3995_;
goto v___jp_3925_;
}
}
}
}
else
{
lean_dec(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
return v___x_3984_;
}
}
v___jp_3998_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; uint8_t v___x_4011_; 
v___x_4008_ = lean_unsigned_to_nat(6u);
v___x_4009_ = l_Lean_Syntax_getArg(v_x_3900_, v___x_4008_);
v___x_4010_ = ((lean_object*)(l_Lean_Fmt_fmtSyntaxCat___closed__3));
lean_inc(v___x_4009_);
v___x_4011_ = l_Lean_Syntax_isOfKind(v___x_4009_, v___x_4010_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
lean_dec(v___x_4009_);
lean_dec(v_namedPrio_x3f_4005_);
lean_dec(v___y_4004_);
lean_dec(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec(v_x_3900_);
v___x_4012_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
lean_ctor_set(v___x_4013_, 1, v___y_4007_);
return v___x_4013_;
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; size_t v_sz_4017_; size_t v___x_4018_; lean_object* v___x_4019_; 
v___x_4014_ = lean_unsigned_to_nat(7u);
v___x_4015_ = l_Lean_Syntax_getArg(v_x_3900_, v___x_4014_);
v___x_4016_ = l_Lean_Syntax_getArgs(v___x_4015_);
lean_dec(v___x_4015_);
v_sz_4017_ = lean_array_size(v___x_4016_);
v___x_4018_ = ((size_t)0ULL);
v___x_4019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtMacro_spec__0(v_sz_4017_, v___x_4018_, v___x_4016_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
lean_dec(v___x_4009_);
lean_dec(v_namedPrio_x3f_4005_);
lean_dec(v___y_4004_);
lean_dec(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec(v_x_3900_);
v___x_4020_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4020_);
lean_ctor_set(v___x_4021_, 1, v___y_4007_);
return v___x_4021_;
}
else
{
lean_object* v_val_4022_; lean_object* v___x_4023_; lean_object* v_darrowTk_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_val_4022_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_val_4022_);
lean_dec_ref_known(v___x_4019_, 1);
v___x_4023_ = lean_unsigned_to_nat(8u);
v_darrowTk_4024_ = l_Lean_Syntax_getArg(v_x_3900_, v___x_4023_);
v___x_4025_ = lean_unsigned_to_nat(9u);
v___x_4026_ = l_Lean_Syntax_getArg(v_x_3900_, v___x_4025_);
lean_dec(v_x_3900_);
if (lean_obj_tag(v___y_4003_) == 0)
{
lean_object* v___x_4027_; 
v___x_4027_ = lean_box(0);
v___y_3971_ = v_val_4022_;
v___y_3972_ = v___x_4026_;
v___y_3973_ = v___y_4000_;
v___y_3974_ = v___y_3999_;
v___y_3975_ = v___y_4001_;
v___y_3976_ = v___y_4006_;
v___y_3977_ = v___y_4002_;
v___y_3978_ = v___x_4009_;
v___y_3979_ = v_darrowTk_4024_;
v___y_3980_ = v___y_4004_;
v___y_3981_ = v_namedPrio_x3f_4005_;
v___y_3982_ = v___y_4007_;
v___y_3983_ = v___x_4027_;
goto v___jp_3970_;
}
else
{
lean_object* v_val_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
v_val_4028_ = lean_ctor_get(v___y_4003_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___y_4003_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___y_4003_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_val_4028_);
lean_dec(v___y_4003_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_val_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
v___y_3971_ = v_val_4022_;
v___y_3972_ = v___x_4026_;
v___y_3973_ = v___y_4000_;
v___y_3974_ = v___y_3999_;
v___y_3975_ = v___y_4001_;
v___y_3976_ = v___y_4006_;
v___y_3977_ = v___y_4002_;
v___y_3978_ = v___x_4009_;
v___y_3979_ = v_darrowTk_4024_;
v___y_3980_ = v___y_4004_;
v___y_3981_ = v_namedPrio_x3f_4005_;
v___y_3982_ = v___y_4007_;
v___y_3983_ = v___x_4033_;
goto v___jp_3970_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderPredicate___boxed(lean_object* v_x_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_Fmt_fmtBinderPredicate(v_x_4134_, v_a_4135_, v_a_4136_);
lean_dec_ref(v_a_4135_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1(){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4144_ = l_Lean_Fmt_fmtAttribute;
v___x_4145_ = ((lean_object*)(l_Lean_Fmt_fmtBinderPredicate___closed__1));
v___x_4146_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___closed__1));
v___x_4147_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderPredicate___boxed), 3, 0);
v___x_4148_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4144_, v___x_4145_, v___x_4146_, v___x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1___boxed(lean_object* v_a_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1();
return v_res_4150_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Syntax(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrecedence___regBuiltin_Lean_Fmt_fmtPrecedence__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxParen___regBuiltin_Lean_Fmt_fmtSyntaxParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCat___regBuiltin_Lean_Fmt_fmtSyntaxCat__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnary___regBuiltin_Lean_Fmt_fmtSyntaxUnary__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxBinary___regBuiltin_Lean_Fmt_fmtSyntaxBinary__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy___regBuiltin_Lean_Fmt_fmtSyntaxSepBy__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxSepBy1___regBuiltin_Lean_Fmt_fmtSyntaxSepBy1__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAtom___regBuiltin_Lean_Fmt_fmtSyntaxAtom__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxNonReserved___regBuiltin_Lean_Fmt_fmtSyntaxNonReserved__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxUnicodeAtom___regBuiltin_Lean_Fmt_fmtSyntaxUnicodeAtom__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNamedName___regBuiltin_Lean_Fmt_fmtNamedName__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtIdentPrec___regBuiltin_Lean_Fmt_fmtIdentPrec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPrefix___regBuiltin_Lean_Fmt_fmtPrefix__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfix___regBuiltin_Lean_Fmt_fmtInfix__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixl___regBuiltin_Lean_Fmt_fmtInfixl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtInfixr___regBuiltin_Lean_Fmt_fmtInfixr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtPostfix___regBuiltin_Lean_Fmt_fmtPostfix__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMixfix___regBuiltin_Lean_Fmt_fmtMixfix__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtNotation___regBuiltin_Lean_Fmt_fmtNotation__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRules___regBuiltin_Lean_Fmt_fmtMacroRules__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxCmd___regBuiltin_Lean_Fmt_fmtSyntaxCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtSyntaxAbbrev___regBuiltin_Lean_Fmt_fmtSyntaxAbbrev__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorBoth___regBuiltin_Lean_Fmt_fmtCatBehaviorBoth__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtCatBehaviorSymbol___regBuiltin_Lean_Fmt_fmtCatBehaviorSymbol__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtDeclareSyntaxCat___regBuiltin_Lean_Fmt_fmtDeclareSyntaxCat__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroArg___regBuiltin_Lean_Fmt_fmtMacroArg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacroRhs___regBuiltin_Lean_Fmt_fmtMacroRhs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtMacro___regBuiltin_Lean_Fmt_fmtMacro__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElabRules___regBuiltin_Lean_Fmt_fmtElabRules__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtElab___regBuiltin_Lean_Fmt_fmtElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Syntax_0__Lean_Fmt_fmtBinderPredicate___regBuiltin_Lean_Fmt_fmtBinderPredicate__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Syntax(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Parser_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
