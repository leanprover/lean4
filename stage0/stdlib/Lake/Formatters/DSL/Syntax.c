// Lean compiler output
// Module: Lake.Formatters.DSL.Syntax
// Imports: public import Lean.Fmt.FmtM.Basic public import Lake.Formatters.DSL.DeclUtil public import Lake.DSL.Syntax import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAppLike(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lake_Formatters_fmtWithOptConfig(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Fmt_fmtAssignmentDeclaration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_retainedWhitespace(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtWhereDeclaration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtMatchDeclaration(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_strLit(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
static const lean_string_object l_Lake_Formatters_fmtGetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_Formatters_fmtGetConfig___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value;
static const lean_string_object l_Lake_Formatters_fmtGetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l_Lake_Formatters_fmtGetConfig___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtGetConfig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "getConfig"};
static const lean_object* l_Lake_Formatters_fmtGetConfig___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtGetConfig___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtGetConfig___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtGetConfig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__3_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 0, 210, 145, 234, 91, 2, 92)}};
static const lean_object* l_Lake_Formatters_fmtGetConfig___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__3_value;
static const lean_string_object l_Lake_Formatters_fmtGetConfig___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_Formatters_fmtGetConfig___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__4_value;
static const lean_ctor_object l_Lake_Formatters_fmtGetConfig___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_Formatters_fmtGetConfig___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGetConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGetConfig___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Formatters"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value;
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtGetConfig"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__1_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__2_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 51, 146, 198, 186, 125, 168, 168)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__2 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Formatters_fmtPackageCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "packageCommand"};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 54, 253, 85, 92, 174, 10, 50)}};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtPackageCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__3_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(175, 253, 70, 178, 90, 186, 195, 40)}};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__3_value;
static const lean_array_object l_Lake_Formatters_fmtPackageCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__4_value;
static const lean_string_object l_Lake_Formatters_fmtPackageCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "identOrStr"};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__5_value;
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__6_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__6_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__5_value),LEAN_SCALAR_PTR_LITERAL(197, 188, 128, 7, 103, 245, 245, 49)}};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__6 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__6_value;
static const lean_string_object l_Lake_Formatters_fmtPackageCommand___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__7 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value;
static const lean_string_object l_Lake_Formatters_fmtPackageCommand___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__8 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value;
static const lean_string_object l_Lake_Formatters_fmtPackageCommand___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__9 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__9_value;
static const lean_string_object l_Lake_Formatters_fmtPackageCommand___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__10 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__10_value;
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__11_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__11_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__11_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__10_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__11 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__11_value;
static const lean_string_object l_Lake_Formatters_fmtPackageCommand___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__12 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__12_value;
static const lean_string_object l_Lake_Formatters_fmtPackageCommand___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__13 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__13_value;
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__14_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__14_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageCommand___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__14_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__13_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lake_Formatters_fmtPackageCommand___closed__14 = (const lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__14_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageCommand___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtPackageCommand"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 245, 111, 133, 248, 53, 26, 81)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtLeanLibCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "leanLibCommand"};
static const lean_object* l_Lake_Formatters_fmtLeanLibCommand___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtLeanLibCommand___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtLeanLibCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtLeanLibCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtLeanLibCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtLeanLibCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtLeanLibCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtLeanLibCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 85, 99, 177, 237, 29, 129, 161)}};
static const lean_object* l_Lake_Formatters_fmtLeanLibCommand___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtLeanLibCommand___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLeanLibCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLeanLibCommand___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtLeanLibCommand"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 78, 207, 114, 179, 168, 55, 167)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtLeanExeCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "leanExeCommand"};
static const lean_object* l_Lake_Formatters_fmtLeanExeCommand___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtLeanExeCommand___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtLeanExeCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtLeanExeCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtLeanExeCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtLeanExeCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtLeanExeCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtLeanExeCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 151, 142, 11, 47, 160, 28)}};
static const lean_object* l_Lake_Formatters_fmtLeanExeCommand___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtLeanExeCommand___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLeanExeCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLeanExeCommand___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtLeanExeCommand"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 29, 214, 81, 122, 70, 201, 14)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtInputFileCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "inputFileCommand"};
static const lean_object* l_Lake_Formatters_fmtInputFileCommand___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtInputFileCommand___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtInputFileCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtInputFileCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtInputFileCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtInputFileCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtInputFileCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtInputFileCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 35, 118, 98, 33, 135, 119, 140)}};
static const lean_object* l_Lake_Formatters_fmtInputFileCommand___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtInputFileCommand___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtInputFileCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtInputFileCommand___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtInputFileCommand"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 12, 164, 113, 90, 233, 127, 159)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtInputDirCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inputDirCommand"};
static const lean_object* l_Lake_Formatters_fmtInputDirCommand___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtInputDirCommand___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtInputDirCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtInputDirCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtInputDirCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtInputDirCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtInputDirCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtInputDirCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 99, 104, 48, 39, 151, 172, 112)}};
static const lean_object* l_Lake_Formatters_fmtInputDirCommand___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtInputDirCommand___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtInputDirCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtInputDirCommand___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtInputDirCommand"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 68, 185, 25, 247, 39, 157, 35)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___boxed(lean_object*);
static lean_once_cell_t l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__0;
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__1_value;
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__2 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__2_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__1_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3_value_aux_2),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3_value;
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__4 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__4_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__5 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__5_value;
static lean_once_cell_t l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__6;
static lean_once_cell_t l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__7;
static lean_once_cell_t l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix;
static const lean_string_object l_Lake_Formatters_fmtPostUpdateDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "postUpdateDecl"};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 217, 106, 51, 176, 161, 152, 100)}};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__1_value;
static const lean_array_object l_Lake_Formatters_fmtPostUpdateDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__2_value;
static lean_once_cell_t l_Lake_Formatters_fmtPostUpdateDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__3;
static const lean_string_object l_Lake_Formatters_fmtPostUpdateDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__4_value;
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__5_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__5_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__5_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__5_value;
static const lean_string_object l_Lake_Formatters_fmtPostUpdateDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declValDo"};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__6 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__6_value;
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__7_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__7_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(253, 210, 120, 194, 116, 135, 247, 152)}};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__7 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__7_value;
static const lean_string_object l_Lake_Formatters_fmtPostUpdateDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__8 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__8_value;
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__9_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__9_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__9_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__8_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__9 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__9_value;
static const lean_string_object l_Lake_Formatters_fmtPostUpdateDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__10 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__10_value;
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__11_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__11_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__11_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__10_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__11 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__11_value;
static const lean_string_object l_Lake_Formatters_fmtPostUpdateDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "simpleBinder"};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__12 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__12_value;
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__13_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtPostUpdateDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__13_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__12_value),LEAN_SCALAR_PTR_LITERAL(58, 16, 244, 231, 102, 138, 237, 36)}};
static const lean_object* l_Lake_Formatters_fmtPostUpdateDecl___closed__13 = (const lean_object*)&l_Lake_Formatters_fmtPostUpdateDecl___closed__13_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPostUpdateDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPostUpdateDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtPostUpdateDecl"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 127, 255, 66, 141, 156, 205, 197)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtFromPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fromPath"};
static const lean_object* l_Lake_Formatters_fmtFromPath___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtFromPath___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtFromPath___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtFromPath___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFromPath___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtFromPath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFromPath___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtFromPath___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 231, 238, 12, 211, 124, 7, 152)}};
static const lean_object* l_Lake_Formatters_fmtFromPath___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtFromPath___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromPath___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtFromPath"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 163, 219, 103, 191, 103, 70, 136)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtFromGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fromGit"};
static const lean_object* l_Lake_Formatters_fmtFromGit___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtFromGit___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtFromGit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtFromGit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFromGit___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtFromGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFromGit___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtFromGit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 198, 35, 138, 239, 183, 90, 121)}};
static const lean_object* l_Lake_Formatters_fmtFromGit___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtFromGit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromGit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtFromGit"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 219, 42, 104, 179, 106, 138, 22)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtFromSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromSource"};
static const lean_object* l_Lake_Formatters_fmtFromSource___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtFromSource___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtFromSource___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtFromSource___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFromSource___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtFromSource___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFromSource___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtFromSource___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 238, 246, 101, 8, 76, 68, 147)}};
static const lean_object* l_Lake_Formatters_fmtFromSource___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtFromSource___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromSource(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromSource___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtFromSource"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 94, 165, 34, 167, 45, 185, 79)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtFromClause___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromClause"};
static const lean_object* l_Lake_Formatters_fmtFromClause___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtFromClause___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtFromClause___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtFromClause___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFromClause___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtFromClause___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFromClause___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtFromClause___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 123, 128, 15, 141, 170, 246, 11)}};
static const lean_object* l_Lake_Formatters_fmtFromClause___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtFromClause___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromClause(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromClause___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtFromClause"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 251, 158, 96, 43, 3, 198, 82)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtWithClause___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "withClause"};
static const lean_object* l_Lake_Formatters_fmtWithClause___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtWithClause___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtWithClause___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithClause___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithClause___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithClause___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithClause___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtWithClause___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 242, 50, 31, 135, 230, 200, 221)}};
static const lean_object* l_Lake_Formatters_fmtWithClause___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtWithClause___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithClause(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithClause___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtWithClause"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 46, 131, 66, 33, 248, 190, 12)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtDepName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depName"};
static const lean_object* l_Lake_Formatters_fmtDepName___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtDepName___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtDepName___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtDepName___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtDepName___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtDepName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtDepName___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtDepName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 76, 0, 7, 47, 106, 167, 185)}};
static const lean_object* l_Lake_Formatters_fmtDepName___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtDepName___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtDepName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lake_Formatters_fmtDepName___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtDepName___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtDepName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtDepName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lake_Formatters_fmtDepName___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtDepName___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDepName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDepName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtDepName"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 160, 86, 120, 238, 183, 250, 185)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtVerSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "verSpec"};
static const lean_object* l_Lake_Formatters_fmtVerSpec___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtVerSpec___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtVerSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtVerSpec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtVerSpec___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtVerSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtVerSpec___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtVerSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 204, 227, 250, 63, 151, 124, 47)}};
static const lean_object* l_Lake_Formatters_fmtVerSpec___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtVerSpec___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtVerSpec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtVerSpec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtVerSpec"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 113, 145, 125, 196, 250, 59, 198)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtRequireDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "requireDecl"};
static const lean_object* l_Lake_Formatters_fmtRequireDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtRequireDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtRequireDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtRequireDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 86, 225, 163, 119, 172, 216, 31)}};
static const lean_object* l_Lake_Formatters_fmtRequireDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtRequireDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depSpec"};
static const lean_object* l_Lake_Formatters_fmtRequireDecl___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtRequireDecl___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtRequireDecl___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtRequireDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__3_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(55, 11, 239, 15, 0, 67, 249, 1)}};
static const lean_object* l_Lake_Formatters_fmtRequireDecl___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__3_value;
static const lean_string_object l_Lake_Formatters_fmtRequireDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "verClause"};
static const lean_object* l_Lake_Formatters_fmtRequireDecl___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__4_value;
static const lean_ctor_object l_Lake_Formatters_fmtRequireDecl___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtRequireDecl___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__5_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtRequireDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__5_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(123, 114, 66, 152, 98, 148, 165, 231)}};
static const lean_object* l_Lake_Formatters_fmtRequireDecl___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtRequireDecl___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtRequireDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtRequireDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtRequireDecl"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 214, 164, 168, 99, 158, 105, 173)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___boxed(lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "bracketedSimpleBinder"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 236, 129, 27, 124, 223, 134, 77)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__2 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__2_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__3_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__3 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__3_value;
static const lean_array_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__4 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__4_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__5_value),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__4_value)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__5 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Formatters_fmtWithBuildDeclSig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "buildDeclSig"};
static const lean_object* l_Lake_Formatters_fmtWithBuildDeclSig___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtWithBuildDeclSig___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtWithBuildDeclSig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithBuildDeclSig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithBuildDeclSig___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithBuildDeclSig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithBuildDeclSig___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtWithBuildDeclSig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 196, 135, 185, 88, 103, 114, 194)}};
static const lean_object* l_Lake_Formatters_fmtWithBuildDeclSig___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtWithBuildDeclSig___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtWithBuildDeclSig___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lake_Formatters_fmtWithBuildDeclSig___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtWithBuildDeclSig___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtWithBuildDeclSig___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithBuildDeclSig___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithBuildDeclSig___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithBuildDeclSig___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithBuildDeclSig___closed__3_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_Formatters_fmtWithBuildDeclSig___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtWithBuildDeclSig___closed__3_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtWithBuildDeclSig___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lake_Formatters_fmtWithBuildDeclSig___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtWithBuildDeclSig___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithBuildDeclSig(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithBuildDeclSig___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Formatters_fmtModuleFacetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "moduleFacetDecl"};
static const lean_object* l_Lake_Formatters_fmtModuleFacetDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtModuleFacetDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtModuleFacetDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtModuleFacetDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtModuleFacetDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtModuleFacetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtModuleFacetDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtModuleFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 43, 74, 179, 42, 185, 17, 154)}};
static const lean_object* l_Lake_Formatters_fmtModuleFacetDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtModuleFacetDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleFacetDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleFacetDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtModuleFacetDecl"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 209, 242, 32, 88, 119, 104, 3)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtPackageFacetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "packageFacetDecl"};
static const lean_object* l_Lake_Formatters_fmtPackageFacetDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtPackageFacetDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtPackageFacetDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageFacetDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageFacetDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageFacetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageFacetDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 92, 181, 116, 139, 59, 115, 98)}};
static const lean_object* l_Lake_Formatters_fmtPackageFacetDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtPackageFacetDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageFacetDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageFacetDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtPackageFacetDecl"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 96, 248, 90, 203, 184, 167, 222)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtLibraryFacetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "libraryFacetDecl"};
static const lean_object* l_Lake_Formatters_fmtLibraryFacetDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtLibraryFacetDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtLibraryFacetDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtLibraryFacetDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtLibraryFacetDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtLibraryFacetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtLibraryFacetDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtLibraryFacetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 169, 186, 57, 250, 57, 9, 172)}};
static const lean_object* l_Lake_Formatters_fmtLibraryFacetDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtLibraryFacetDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLibraryFacetDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLibraryFacetDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtLibraryFacetDecl"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 184, 151, 111, 41, 81, 184, 52)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtTargetCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "targetCommand"};
static const lean_object* l_Lake_Formatters_fmtTargetCommand___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtTargetCommand___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtTargetCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtTargetCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtTargetCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtTargetCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtTargetCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtTargetCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 4, 31, 14, 49, 110, 122, 182)}};
static const lean_object* l_Lake_Formatters_fmtTargetCommand___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtTargetCommand___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtTargetCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtTargetCommand___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtTargetCommand"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 192, 172, 133, 3, 169, 229, 206)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtExternLibCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "externLibCommand"};
static const lean_object* l_Lake_Formatters_fmtExternLibCommand___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtExternLibCommand___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtExternLibCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtExternLibCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtExternLibCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtExternLibCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtExternLibCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtExternLibCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 102, 133, 13, 61, 107, 230, 129)}};
static const lean_object* l_Lake_Formatters_fmtExternLibCommand___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtExternLibCommand___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtExternLibCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "externLibDeclSpec"};
static const lean_object* l_Lake_Formatters_fmtExternLibCommand___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtExternLibCommand___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtExternLibCommand___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtExternLibCommand___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtExternLibCommand___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtExternLibCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtExternLibCommand___closed__3_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtExternLibCommand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(153, 47, 189, 11, 205, 24, 206, 176)}};
static const lean_object* l_Lake_Formatters_fmtExternLibCommand___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtExternLibCommand___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtExternLibCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtExternLibCommand___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtExternLibCommand"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 52, 31, 70, 129, 134, 109, 185)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtCacheServiceCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "cacheServiceCommand"};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 45, 201, 219, 139, 244, 81, 2)}};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtCacheServiceCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declValEqns"};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__3_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__3_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 66, 113, 88, 174, 230, 155, 36)}};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__3_value;
static const lean_string_object l_Lake_Formatters_fmtCacheServiceCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__4_value;
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__5_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__5_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__5_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__4_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__5_value;
static const lean_string_object l_Lake_Formatters_fmtCacheServiceCommand___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__6 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__6_value;
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__7_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__7_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__7_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__7 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__7_value;
static const lean_string_object l_Lake_Formatters_fmtCacheServiceCommand___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "matchAltsWhereDecls"};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__8 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__8_value;
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__9_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__9_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__9_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(179, 171, 202, 53, 227, 199, 51, 48)}};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__9 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__9_value;
static const lean_string_object l_Lake_Formatters_fmtCacheServiceCommand___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__10 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__10_value;
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__11_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__11_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_Formatters_fmtCacheServiceCommand___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__11_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__10_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lake_Formatters_fmtCacheServiceCommand___closed__11 = (const lean_object*)&l_Lake_Formatters_fmtCacheServiceCommand___closed__11_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtCacheServiceCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtCacheServiceCommand___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtCacheServiceCommand"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 187, 78, 221, 231, 217, 40, 35)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtScriptDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scriptDecl"};
static const lean_object* l_Lake_Formatters_fmtScriptDecl___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtScriptDecl___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtScriptDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtScriptDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtScriptDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtScriptDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtScriptDecl___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtScriptDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 18, 40, 229, 14, 216, 222, 158)}};
static const lean_object* l_Lake_Formatters_fmtScriptDecl___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtScriptDecl___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtScriptDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "scriptDeclSpec"};
static const lean_object* l_Lake_Formatters_fmtScriptDecl___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtScriptDecl___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtScriptDecl___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtScriptDecl___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtScriptDecl___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtScriptDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtScriptDecl___closed__3_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtScriptDecl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(106, 145, 50, 108, 63, 62, 118, 110)}};
static const lean_object* l_Lake_Formatters_fmtScriptDecl___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtScriptDecl___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtScriptDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtScriptDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtScriptDecl"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 23, 199, 190, 174, 39, 134, 186)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtEvalVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalVer"};
static const lean_object* l_Lake_Formatters_fmtEvalVer___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtEvalVer___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtEvalVer___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtEvalVer___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtEvalVer___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtEvalVer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtEvalVer___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtEvalVer___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 252, 213, 234, 103, 11, 172, 191)}};
static const lean_object* l_Lake_Formatters_fmtEvalVer___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtEvalVer___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtEvalVer(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtEvalVer___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtEvalVer"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 133, 14, 228, 97, 115, 220, 58)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtVerLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "verLit"};
static const lean_object* l_Lake_Formatters_fmtVerLit___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtVerLit___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtVerLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtVerLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtVerLit___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtVerLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtVerLit___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtVerLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 205, 236, 50, 125, 9, 172, 134)}};
static const lean_object* l_Lake_Formatters_fmtVerLit___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtVerLit___closed__1_value;
static const lean_string_object l_Lake_Formatters_fmtVerLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l_Lake_Formatters_fmtVerLit___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtVerLit___closed__2_value;
static const lean_ctor_object l_Lake_Formatters_fmtVerLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtVerLit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l_Lake_Formatters_fmtVerLit___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtVerLit___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtVerLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtVerLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtVerLit"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 71, 116, 47, 145, 161, 115, 102)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtFacetSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "facetSuffix"};
static const lean_object* l_Lake_Formatters_fmtFacetSuffix___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtFacetSuffix___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtFacetSuffix___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtFacetSuffix___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFacetSuffix___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtFacetSuffix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFacetSuffix___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtFacetSuffix___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 19, 148, 195, 91, 53, 9, 109)}};
static const lean_object* l_Lake_Formatters_fmtFacetSuffix___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtFacetSuffix___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFacetSuffix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFacetSuffix___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtFacetSuffix"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 251, 185, 9, 44, 12, 71, 42)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtPackageTargetLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "packageTargetLit"};
static const lean_object* l_Lake_Formatters_fmtPackageTargetLit___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtPackageTargetLit___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtPackageTargetLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageTargetLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageTargetLit___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageTargetLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageTargetLit___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageTargetLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 101, 186, 35, 177, 203, 61, 85)}};
static const lean_object* l_Lake_Formatters_fmtPackageTargetLit___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtPackageTargetLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageTargetLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageTargetLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtPackageTargetLit"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 82, 40, 155, 105, 96, 49, 53)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtModuleTargetKeyLit_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtModuleTargetKeyLit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Formatters_fmtModuleTargetKeyLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "moduleTargetKeyLit"};
static const lean_object* l_Lake_Formatters_fmtModuleTargetKeyLit___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtModuleTargetKeyLit___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtModuleTargetKeyLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtModuleTargetKeyLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtModuleTargetKeyLit___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtModuleTargetKeyLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtModuleTargetKeyLit___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtModuleTargetKeyLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 150, 87, 20, 34, 170, 193, 64)}};
static const lean_object* l_Lake_Formatters_fmtModuleTargetKeyLit___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtModuleTargetKeyLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleTargetKeyLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleTargetKeyLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtModuleTargetKeyLit"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 53, 220, 57, 45, 254, 134, 82)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtPackageTargetKeyLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "packageTargetKeyLit"};
static const lean_object* l_Lake_Formatters_fmtPackageTargetKeyLit___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtPackageTargetKeyLit___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtPackageTargetKeyLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageTargetKeyLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageTargetKeyLit___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtPackageTargetKeyLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtPackageTargetKeyLit___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtPackageTargetKeyLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 78, 171, 75, 222, 86, 241, 235)}};
static const lean_object* l_Lake_Formatters_fmtPackageTargetKeyLit___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtPackageTargetKeyLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageTargetKeyLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageTargetKeyLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtPackageTargetKeyLit"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 150, 135, 196, 167, 184, 111, 40)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___boxed(lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "metaIf"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 98, 156, 191, 205, 206, 20, 202)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__1_value;
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cmdDo"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__2 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__2_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__3_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(97, 39, 184, 30, 65, 63, 201, 66)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__3 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfChain(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfChain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtMetaIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtMetaIf___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtMetaIf"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 75, 147, 80, 6, 41, 61, 18)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtRunIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "runIO"};
static const lean_object* l_Lake_Formatters_fmtRunIO___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtRunIO___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtRunIO___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtRunIO___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtRunIO___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_Formatters_fmtRunIO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtRunIO___closed__1_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtRunIO___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 189, 119, 141, 116, 67, 96, 12)}};
static const lean_object* l_Lake_Formatters_fmtRunIO___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtRunIO___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtRunIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtRunIO___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtRunIO"};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGetConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 224, 168, 72, 173, 113, 29, 138)}};
static const lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGetConfig(lean_object* v_x_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = ((lean_object*)(l_Lake_Formatters_fmtGetConfig___closed__3));
lean_inc(v_x_11_);
v___x_15_ = l_Lean_Syntax_isOfKind(v_x_11_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_x_11_);
v___x_16_ = l_Lean_Fmt_Error_partialFormatter;
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_a_13_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = l_Lean_Syntax_getArg(v_x_11_, v___x_18_);
v___x_20_ = ((lean_object*)(l_Lake_Formatters_fmtGetConfig___closed__5));
lean_inc(v___x_19_);
v___x_21_ = l_Lean_Syntax_isOfKind(v___x_19_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v___x_19_);
lean_dec(v_x_11_);
v___x_22_ = l_Lean_Fmt_Error_partialFormatter;
v___x_23_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v_a_13_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; lean_object* v_getConfigTk_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_24_ = lean_unsigned_to_nat(0u);
v_getConfigTk_25_ = l_Lean_Syntax_getArg(v_x_11_, v___x_24_);
lean_dec(v_x_11_);
v___x_26_ = lean_unsigned_to_nat(2u);
v___x_27_ = lean_mk_empty_array_with_capacity(v___x_26_);
v___x_28_ = lean_array_push(v___x_27_, v_getConfigTk_25_);
v___x_29_ = lean_array_push(v___x_28_, v___x_19_);
v___x_30_ = l_Lean_Fmt_fmtAppLike(v___x_29_, v_a_12_, v_a_13_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGetConfig___boxed(lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lake_Formatters_fmtGetConfig(v_x_31_, v_a_32_, v_a_33_);
lean_dec_ref(v_a_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1(){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_42_ = l_Lean_Fmt_fmtAttribute;
v___x_43_ = ((lean_object*)(l_Lake_Formatters_fmtGetConfig___closed__3));
v___x_44_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___closed__2));
v___x_45_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtGetConfig___boxed), 3, 0);
v___x_46_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_42_, v___x_43_, v___x_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1___boxed(lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1();
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand(lean_object* v_kwTk_52_, lean_object* v_name_x3f_53_, lean_object* v_config_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Fmt_fmt(v_kwTk_52_, v_a_55_, v_a_56_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v_a_59_; lean_object* v___y_61_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
v_a_59_ = lean_ctor_get(v___x_57_, 1);
lean_inc(v_a_59_);
lean_dec_ref_known(v___x_57_, 2);
if (lean_obj_tag(v_name_x3f_53_) == 0)
{
lean_object* v___x_72_; 
v___x_72_ = lean_box(0);
v___y_61_ = v___x_72_;
goto v___jp_60_;
}
else
{
lean_object* v_val_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_val_73_ = lean_ctor_get(v_name_x3f_53_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v_name_x3f_53_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v_name_x3f_53_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_val_73_);
lean_dec(v_name_x3f_53_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_val_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
v___y_61_ = v___x_78_;
goto v___jp_60_;
}
}
}
v___jp_60_:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Fmt_fmt_x3f(v___y_61_, v_a_55_, v_a_59_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v_a_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_a_63_);
v_a_64_ = lean_ctor_get(v___x_62_, 1);
lean_inc(v_a_64_);
lean_dec_ref_known(v___x_62_, 2);
v___x_65_ = lean_unsigned_to_nat(2u);
v___x_66_ = lean_mk_empty_array_with_capacity(v___x_65_);
v___x_67_ = lean_array_push(v___x_66_, v_a_58_);
v___x_68_ = lean_array_push(v___x_67_, v_a_63_);
v___x_69_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand___closed__0));
v___x_70_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_68_, v___x_69_);
v___x_71_ = l_Lake_Formatters_fmtWithOptConfig(v___x_70_, v_config_54_, v_a_55_, v_a_64_);
return v___x_71_;
}
else
{
lean_dec(v_a_58_);
lean_dec(v_config_54_);
return v___x_62_;
}
}
}
else
{
lean_dec(v_config_54_);
lean_dec(v_name_x3f_53_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand___boxed(lean_object* v_kwTk_81_, lean_object* v_name_x3f_82_, lean_object* v_config_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand(v_kwTk_81_, v_name_x3f_82_, v_config_83_, v_a_84_, v_a_85_);
lean_dec_ref(v_a_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageCommand(lean_object* v_x_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__1));
lean_inc(v_x_120_);
v___x_124_ = l_Lean_Syntax_isOfKind(v_x_120_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec(v_x_120_);
v___x_125_ = l_Lean_Fmt_Error_partialFormatter;
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v_a_122_);
return v___x_126_;
}
else
{
lean_object* v___x_127_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v_name_x3f_132_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_147_; lean_object* v___y_148_; lean_object* v_attributes_x3f_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v_docComment_x3f_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_184_ = l_Lean_Syntax_getArg(v_x_120_, v___x_127_);
v___x_185_ = l_Lean_Syntax_isNone(v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_184_);
v___x_187_ = l_Lean_Syntax_matchesNull(v___x_184_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v___x_184_);
lean_dec(v_x_120_);
v___x_188_ = l_Lean_Fmt_Error_partialFormatter;
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_122_);
return v___x_189_;
}
else
{
lean_object* v_docComment_x3f_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_docComment_x3f_190_ = l_Lean_Syntax_getArg(v___x_184_, v___x_127_);
lean_dec(v___x_184_);
v___x_191_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_190_);
v___x_192_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_docComment_x3f_190_);
lean_dec(v_x_120_);
v___x_193_ = l_Lean_Fmt_Error_partialFormatter;
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v_a_122_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v_docComment_x3f_190_);
v_docComment_x3f_168_ = v___x_195_;
v___y_169_ = v_a_121_;
v___y_170_ = v_a_122_;
goto v___jp_167_;
}
}
}
else
{
lean_object* v___x_196_; 
lean_dec(v___x_184_);
v___x_196_ = lean_box(0);
v_docComment_x3f_168_ = v___x_196_;
v___y_169_ = v_a_121_;
v___y_170_ = v_a_122_;
goto v___jp_167_;
}
v___jp_128_:
{
lean_object* v___x_135_; lean_object* v_config_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_135_ = lean_unsigned_to_nat(4u);
v_config_136_ = l_Lean_Syntax_getArg(v_x_120_, v___x_135_);
lean_dec(v_x_120_);
v___x_137_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__3));
lean_inc(v_config_136_);
v___x_138_ = l_Lean_Syntax_isOfKind(v_config_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec(v_config_136_);
lean_dec(v_name_x3f_132_);
lean_dec(v___y_131_);
lean_dec(v___y_130_);
lean_dec(v___y_129_);
v___x_139_ = l_Lean_Fmt_Error_partialFormatter;
v___x_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___y_134_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand(v___y_130_, v_name_x3f_132_, v_config_136_, v___y_133_, v___y_134_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v_a_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
v_a_143_ = lean_ctor_get(v___x_141_, 1);
lean_inc(v_a_143_);
lean_dec_ref_known(v___x_141_, 2);
v___x_144_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_145_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_131_, v___y_129_, v___x_144_, v_a_142_, v___y_133_, v_a_143_);
return v___x_145_;
}
else
{
lean_dec(v___y_131_);
lean_dec(v___y_129_);
return v___x_141_;
}
}
}
v___jp_146_:
{
lean_object* v___x_152_; lean_object* v_packageTk_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_152_ = lean_unsigned_to_nat(2u);
v_packageTk_153_ = l_Lean_Syntax_getArg(v_x_120_, v___x_152_);
v___x_154_ = lean_unsigned_to_nat(3u);
v___x_155_ = l_Lean_Syntax_getArg(v_x_120_, v___x_154_);
v___x_156_ = l_Lean_Syntax_isNone(v___x_155_);
if (v___x_156_ == 0)
{
uint8_t v___x_157_; 
lean_inc(v___x_155_);
v___x_157_ = l_Lean_Syntax_matchesNull(v___x_155_, v___y_147_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec(v___x_155_);
lean_dec(v_packageTk_153_);
lean_dec(v_attributes_x3f_149_);
lean_dec(v___y_148_);
lean_dec(v_x_120_);
v___x_158_ = l_Lean_Fmt_Error_partialFormatter;
v___x_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___y_151_);
return v___x_159_;
}
else
{
lean_object* v_name_x3f_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_name_x3f_160_ = l_Lean_Syntax_getArg(v___x_155_, v___x_127_);
lean_dec(v___x_155_);
v___x_161_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__6));
lean_inc(v_name_x3f_160_);
v___x_162_ = l_Lean_Syntax_isOfKind(v_name_x3f_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_name_x3f_160_);
lean_dec(v_packageTk_153_);
lean_dec(v_attributes_x3f_149_);
lean_dec(v___y_148_);
lean_dec(v_x_120_);
v___x_163_ = l_Lean_Fmt_Error_partialFormatter;
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___y_151_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v_name_x3f_160_);
v___y_129_ = v_attributes_x3f_149_;
v___y_130_ = v_packageTk_153_;
v___y_131_ = v___y_148_;
v_name_x3f_132_ = v___x_165_;
v___y_133_ = v___y_150_;
v___y_134_ = v___y_151_;
goto v___jp_128_;
}
}
}
else
{
lean_object* v___x_166_; 
lean_dec(v___x_155_);
v___x_166_ = lean_box(0);
v___y_129_ = v_attributes_x3f_149_;
v___y_130_ = v_packageTk_153_;
v___y_131_ = v___y_148_;
v_name_x3f_132_ = v___x_166_;
v___y_133_ = v___y_150_;
v___y_134_ = v___y_151_;
goto v___jp_128_;
}
}
v___jp_167_:
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = l_Lean_Syntax_getArg(v_x_120_, v___x_171_);
v___x_173_ = l_Lean_Syntax_isNone(v___x_172_);
if (v___x_173_ == 0)
{
uint8_t v___x_174_; 
lean_inc(v___x_172_);
v___x_174_ = l_Lean_Syntax_matchesNull(v___x_172_, v___x_171_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v___x_172_);
lean_dec(v_docComment_x3f_168_);
lean_dec(v_x_120_);
v___x_175_ = l_Lean_Fmt_Error_partialFormatter;
v___x_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___y_170_);
return v___x_176_;
}
else
{
lean_object* v_attributes_x3f_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_attributes_x3f_177_ = l_Lean_Syntax_getArg(v___x_172_, v___x_127_);
lean_dec(v___x_172_);
v___x_178_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_177_);
v___x_179_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_attributes_x3f_177_);
lean_dec(v_docComment_x3f_168_);
lean_dec(v_x_120_);
v___x_180_ = l_Lean_Fmt_Error_partialFormatter;
v___x_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___y_170_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v_attributes_x3f_177_);
v___y_147_ = v___x_171_;
v___y_148_ = v_docComment_x3f_168_;
v_attributes_x3f_149_ = v___x_182_;
v___y_150_ = v___y_169_;
v___y_151_ = v___y_170_;
goto v___jp_146_;
}
}
}
else
{
lean_object* v___x_183_; 
lean_dec(v___x_172_);
v___x_183_ = lean_box(0);
v___y_147_ = v___x_171_;
v___y_148_ = v_docComment_x3f_168_;
v_attributes_x3f_149_ = v___x_183_;
v___y_150_ = v___y_169_;
v___y_151_ = v___y_170_;
goto v___jp_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageCommand___boxed(lean_object* v_x_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_Formatters_fmtPackageCommand(v_x_197_, v_a_198_, v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1(){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_207_ = l_Lean_Fmt_fmtAttribute;
v___x_208_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__1));
v___x_209_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___closed__1));
v___x_210_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtPackageCommand___boxed), 3, 0);
v___x_211_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_207_, v___x_208_, v___x_209_, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1___boxed(lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1();
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLeanLibCommand(lean_object* v_x_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = ((lean_object*)(l_Lake_Formatters_fmtLeanLibCommand___closed__1));
lean_inc(v_x_219_);
v___x_223_ = l_Lean_Syntax_isOfKind(v_x_219_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec(v_x_219_);
v___x_224_ = l_Lean_Fmt_Error_partialFormatter;
v___x_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v_a_221_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v_name_x3f_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v_attributes_x3f_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v_docComment_x3f_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_283_ = l_Lean_Syntax_getArg(v_x_219_, v___x_226_);
v___x_284_ = l_Lean_Syntax_isNone(v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_283_);
v___x_286_ = l_Lean_Syntax_matchesNull(v___x_283_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v___x_283_);
lean_dec(v_x_219_);
v___x_287_ = l_Lean_Fmt_Error_partialFormatter;
v___x_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_a_221_);
return v___x_288_;
}
else
{
lean_object* v_docComment_x3f_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_docComment_x3f_289_ = l_Lean_Syntax_getArg(v___x_283_, v___x_226_);
lean_dec(v___x_283_);
v___x_290_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_289_);
v___x_291_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec(v_docComment_x3f_289_);
lean_dec(v_x_219_);
v___x_292_ = l_Lean_Fmt_Error_partialFormatter;
v___x_293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_a_221_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v_docComment_x3f_289_);
v_docComment_x3f_267_ = v___x_294_;
v___y_268_ = v_a_220_;
v___y_269_ = v_a_221_;
goto v___jp_266_;
}
}
}
else
{
lean_object* v___x_295_; 
lean_dec(v___x_283_);
v___x_295_ = lean_box(0);
v_docComment_x3f_267_ = v___x_295_;
v___y_268_ = v_a_220_;
v___y_269_ = v_a_221_;
goto v___jp_266_;
}
v___jp_227_:
{
lean_object* v___x_234_; lean_object* v_config_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_234_ = lean_unsigned_to_nat(4u);
v_config_235_ = l_Lean_Syntax_getArg(v_x_219_, v___x_234_);
lean_dec(v_x_219_);
v___x_236_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__3));
lean_inc(v_config_235_);
v___x_237_ = l_Lean_Syntax_isOfKind(v_config_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v_config_235_);
lean_dec(v_name_x3f_231_);
lean_dec(v___y_230_);
lean_dec(v___y_229_);
lean_dec(v___y_228_);
v___x_238_ = l_Lean_Fmt_Error_partialFormatter;
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___y_233_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand(v___y_229_, v_name_x3f_231_, v_config_235_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v_a_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
v_a_242_ = lean_ctor_get(v___x_240_, 1);
lean_inc(v_a_242_);
lean_dec_ref_known(v___x_240_, 2);
v___x_243_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_244_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_230_, v___y_228_, v___x_243_, v_a_241_, v___y_232_, v_a_242_);
return v___x_244_;
}
else
{
lean_dec(v___y_230_);
lean_dec(v___y_228_);
return v___x_240_;
}
}
}
v___jp_245_:
{
lean_object* v___x_251_; lean_object* v_leanLibTk_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_251_ = lean_unsigned_to_nat(2u);
v_leanLibTk_252_ = l_Lean_Syntax_getArg(v_x_219_, v___x_251_);
v___x_253_ = lean_unsigned_to_nat(3u);
v___x_254_ = l_Lean_Syntax_getArg(v_x_219_, v___x_253_);
v___x_255_ = l_Lean_Syntax_isNone(v___x_254_);
if (v___x_255_ == 0)
{
uint8_t v___x_256_; 
lean_inc(v___x_254_);
v___x_256_ = l_Lean_Syntax_matchesNull(v___x_254_, v___y_246_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v___x_254_);
lean_dec(v_leanLibTk_252_);
lean_dec(v_attributes_x3f_248_);
lean_dec(v___y_247_);
lean_dec(v_x_219_);
v___x_257_ = l_Lean_Fmt_Error_partialFormatter;
v___x_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___y_250_);
return v___x_258_;
}
else
{
lean_object* v_name_x3f_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v_name_x3f_259_ = l_Lean_Syntax_getArg(v___x_254_, v___x_226_);
lean_dec(v___x_254_);
v___x_260_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__6));
lean_inc(v_name_x3f_259_);
v___x_261_ = l_Lean_Syntax_isOfKind(v_name_x3f_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_name_x3f_259_);
lean_dec(v_leanLibTk_252_);
lean_dec(v_attributes_x3f_248_);
lean_dec(v___y_247_);
lean_dec(v_x_219_);
v___x_262_ = l_Lean_Fmt_Error_partialFormatter;
v___x_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___y_250_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; 
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v_name_x3f_259_);
v___y_228_ = v_attributes_x3f_248_;
v___y_229_ = v_leanLibTk_252_;
v___y_230_ = v___y_247_;
v_name_x3f_231_ = v___x_264_;
v___y_232_ = v___y_249_;
v___y_233_ = v___y_250_;
goto v___jp_227_;
}
}
}
else
{
lean_object* v___x_265_; 
lean_dec(v___x_254_);
v___x_265_ = lean_box(0);
v___y_228_ = v_attributes_x3f_248_;
v___y_229_ = v_leanLibTk_252_;
v___y_230_ = v___y_247_;
v_name_x3f_231_ = v___x_265_;
v___y_232_ = v___y_249_;
v___y_233_ = v___y_250_;
goto v___jp_227_;
}
}
v___jp_266_:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = l_Lean_Syntax_getArg(v_x_219_, v___x_270_);
v___x_272_ = l_Lean_Syntax_isNone(v___x_271_);
if (v___x_272_ == 0)
{
uint8_t v___x_273_; 
lean_inc(v___x_271_);
v___x_273_ = l_Lean_Syntax_matchesNull(v___x_271_, v___x_270_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec(v___x_271_);
lean_dec(v_docComment_x3f_267_);
lean_dec(v_x_219_);
v___x_274_ = l_Lean_Fmt_Error_partialFormatter;
v___x_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___y_269_);
return v___x_275_;
}
else
{
lean_object* v_attributes_x3f_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_attributes_x3f_276_ = l_Lean_Syntax_getArg(v___x_271_, v___x_226_);
lean_dec(v___x_271_);
v___x_277_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_276_);
v___x_278_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec(v_attributes_x3f_276_);
lean_dec(v_docComment_x3f_267_);
lean_dec(v_x_219_);
v___x_279_ = l_Lean_Fmt_Error_partialFormatter;
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___y_269_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v_attributes_x3f_276_);
v___y_246_ = v___x_270_;
v___y_247_ = v_docComment_x3f_267_;
v_attributes_x3f_248_ = v___x_281_;
v___y_249_ = v___y_268_;
v___y_250_ = v___y_269_;
goto v___jp_245_;
}
}
}
else
{
lean_object* v___x_282_; 
lean_dec(v___x_271_);
v___x_282_ = lean_box(0);
v___y_246_ = v___x_270_;
v___y_247_ = v_docComment_x3f_267_;
v_attributes_x3f_248_ = v___x_282_;
v___y_249_ = v___y_268_;
v___y_250_ = v___y_269_;
goto v___jp_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLeanLibCommand___boxed(lean_object* v_x_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lake_Formatters_fmtLeanLibCommand(v_x_296_, v_a_297_, v_a_298_);
lean_dec_ref(v_a_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1(){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_306_ = l_Lean_Fmt_fmtAttribute;
v___x_307_ = ((lean_object*)(l_Lake_Formatters_fmtLeanLibCommand___closed__1));
v___x_308_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___closed__1));
v___x_309_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtLeanLibCommand___boxed), 3, 0);
v___x_310_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_306_, v___x_307_, v___x_308_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1___boxed(lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1();
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLeanExeCommand(lean_object* v_x_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lake_Formatters_fmtLeanExeCommand___closed__1));
lean_inc(v_x_318_);
v___x_322_ = l_Lean_Syntax_isOfKind(v_x_318_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v_x_318_);
v___x_323_ = l_Lean_Fmt_Error_partialFormatter;
v___x_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_a_320_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v_name_x3f_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v_attributes_x3f_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v_docComment_x3f_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_382_ = l_Lean_Syntax_getArg(v_x_318_, v___x_325_);
v___x_383_ = l_Lean_Syntax_isNone(v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_382_);
v___x_385_ = l_Lean_Syntax_matchesNull(v___x_382_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v___x_382_);
lean_dec(v_x_318_);
v___x_386_ = l_Lean_Fmt_Error_partialFormatter;
v___x_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v_a_320_);
return v___x_387_;
}
else
{
lean_object* v_docComment_x3f_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_docComment_x3f_388_ = l_Lean_Syntax_getArg(v___x_382_, v___x_325_);
lean_dec(v___x_382_);
v___x_389_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_388_);
v___x_390_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v_docComment_x3f_388_);
lean_dec(v_x_318_);
v___x_391_ = l_Lean_Fmt_Error_partialFormatter;
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_a_320_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; 
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v_docComment_x3f_388_);
v_docComment_x3f_366_ = v___x_393_;
v___y_367_ = v_a_319_;
v___y_368_ = v_a_320_;
goto v___jp_365_;
}
}
}
else
{
lean_object* v___x_394_; 
lean_dec(v___x_382_);
v___x_394_ = lean_box(0);
v_docComment_x3f_366_ = v___x_394_;
v___y_367_ = v_a_319_;
v___y_368_ = v_a_320_;
goto v___jp_365_;
}
v___jp_326_:
{
lean_object* v___x_333_; lean_object* v_config_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_333_ = lean_unsigned_to_nat(4u);
v_config_334_ = l_Lean_Syntax_getArg(v_x_318_, v___x_333_);
lean_dec(v_x_318_);
v___x_335_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__3));
lean_inc(v_config_334_);
v___x_336_ = l_Lean_Syntax_isOfKind(v_config_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_config_334_);
lean_dec(v_name_x3f_330_);
lean_dec(v___y_329_);
lean_dec(v___y_328_);
lean_dec(v___y_327_);
v___x_337_ = l_Lean_Fmt_Error_partialFormatter;
v___x_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___y_332_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand(v___y_329_, v_name_x3f_330_, v_config_334_, v___y_331_, v___y_332_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v_a_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
v_a_341_ = lean_ctor_get(v___x_339_, 1);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_339_, 2);
v___x_342_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_343_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_328_, v___y_327_, v___x_342_, v_a_340_, v___y_331_, v_a_341_);
return v___x_343_;
}
else
{
lean_dec(v___y_328_);
lean_dec(v___y_327_);
return v___x_339_;
}
}
}
v___jp_344_:
{
lean_object* v___x_350_; lean_object* v_leanExeTk_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_350_ = lean_unsigned_to_nat(2u);
v_leanExeTk_351_ = l_Lean_Syntax_getArg(v_x_318_, v___x_350_);
v___x_352_ = lean_unsigned_to_nat(3u);
v___x_353_ = l_Lean_Syntax_getArg(v_x_318_, v___x_352_);
v___x_354_ = l_Lean_Syntax_isNone(v___x_353_);
if (v___x_354_ == 0)
{
uint8_t v___x_355_; 
lean_inc(v___x_353_);
v___x_355_ = l_Lean_Syntax_matchesNull(v___x_353_, v___y_345_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec(v___x_353_);
lean_dec(v_leanExeTk_351_);
lean_dec(v_attributes_x3f_347_);
lean_dec(v___y_346_);
lean_dec(v_x_318_);
v___x_356_ = l_Lean_Fmt_Error_partialFormatter;
v___x_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___y_349_);
return v___x_357_;
}
else
{
lean_object* v_name_x3f_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_name_x3f_358_ = l_Lean_Syntax_getArg(v___x_353_, v___x_325_);
lean_dec(v___x_353_);
v___x_359_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__6));
lean_inc(v_name_x3f_358_);
v___x_360_ = l_Lean_Syntax_isOfKind(v_name_x3f_358_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec(v_name_x3f_358_);
lean_dec(v_leanExeTk_351_);
lean_dec(v_attributes_x3f_347_);
lean_dec(v___y_346_);
lean_dec(v_x_318_);
v___x_361_ = l_Lean_Fmt_Error_partialFormatter;
v___x_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v___y_349_);
return v___x_362_;
}
else
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v_name_x3f_358_);
v___y_327_ = v_attributes_x3f_347_;
v___y_328_ = v___y_346_;
v___y_329_ = v_leanExeTk_351_;
v_name_x3f_330_ = v___x_363_;
v___y_331_ = v___y_348_;
v___y_332_ = v___y_349_;
goto v___jp_326_;
}
}
}
else
{
lean_object* v___x_364_; 
lean_dec(v___x_353_);
v___x_364_ = lean_box(0);
v___y_327_ = v_attributes_x3f_347_;
v___y_328_ = v___y_346_;
v___y_329_ = v_leanExeTk_351_;
v_name_x3f_330_ = v___x_364_;
v___y_331_ = v___y_348_;
v___y_332_ = v___y_349_;
goto v___jp_326_;
}
}
v___jp_365_:
{
lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = l_Lean_Syntax_getArg(v_x_318_, v___x_369_);
v___x_371_ = l_Lean_Syntax_isNone(v___x_370_);
if (v___x_371_ == 0)
{
uint8_t v___x_372_; 
lean_inc(v___x_370_);
v___x_372_ = l_Lean_Syntax_matchesNull(v___x_370_, v___x_369_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v___x_370_);
lean_dec(v_docComment_x3f_366_);
lean_dec(v_x_318_);
v___x_373_ = l_Lean_Fmt_Error_partialFormatter;
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___y_368_);
return v___x_374_;
}
else
{
lean_object* v_attributes_x3f_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_attributes_x3f_375_ = l_Lean_Syntax_getArg(v___x_370_, v___x_325_);
lean_dec(v___x_370_);
v___x_376_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_375_);
v___x_377_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_375_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_attributes_x3f_375_);
lean_dec(v_docComment_x3f_366_);
lean_dec(v_x_318_);
v___x_378_ = l_Lean_Fmt_Error_partialFormatter;
v___x_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___y_368_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; 
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v_attributes_x3f_375_);
v___y_345_ = v___x_369_;
v___y_346_ = v_docComment_x3f_366_;
v_attributes_x3f_347_ = v___x_380_;
v___y_348_ = v___y_367_;
v___y_349_ = v___y_368_;
goto v___jp_344_;
}
}
}
else
{
lean_object* v___x_381_; 
lean_dec(v___x_370_);
v___x_381_ = lean_box(0);
v___y_345_ = v___x_369_;
v___y_346_ = v_docComment_x3f_366_;
v_attributes_x3f_347_ = v___x_381_;
v___y_348_ = v___y_367_;
v___y_349_ = v___y_368_;
goto v___jp_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLeanExeCommand___boxed(lean_object* v_x_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lake_Formatters_fmtLeanExeCommand(v_x_395_, v_a_396_, v_a_397_);
lean_dec_ref(v_a_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1(){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_405_ = l_Lean_Fmt_fmtAttribute;
v___x_406_ = ((lean_object*)(l_Lake_Formatters_fmtLeanExeCommand___closed__1));
v___x_407_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___closed__1));
v___x_408_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtLeanExeCommand___boxed), 3, 0);
v___x_409_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_405_, v___x_406_, v___x_407_, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1___boxed(lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1();
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtInputFileCommand(lean_object* v_x_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lake_Formatters_fmtInputFileCommand___closed__1));
lean_inc(v_x_417_);
v___x_421_ = l_Lean_Syntax_isOfKind(v_x_417_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v_x_417_);
v___x_422_ = l_Lean_Fmt_Error_partialFormatter;
v___x_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v_a_419_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v_name_x3f_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v_attributes_x3f_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v_docComment_x3f_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_481_ = l_Lean_Syntax_getArg(v_x_417_, v___x_424_);
v___x_482_ = l_Lean_Syntax_isNone(v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_481_);
v___x_484_ = l_Lean_Syntax_matchesNull(v___x_481_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v___x_481_);
lean_dec(v_x_417_);
v___x_485_ = l_Lean_Fmt_Error_partialFormatter;
v___x_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_a_419_);
return v___x_486_;
}
else
{
lean_object* v_docComment_x3f_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_docComment_x3f_487_ = l_Lean_Syntax_getArg(v___x_481_, v___x_424_);
lean_dec(v___x_481_);
v___x_488_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_487_);
v___x_489_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v_docComment_x3f_487_);
lean_dec(v_x_417_);
v___x_490_ = l_Lean_Fmt_Error_partialFormatter;
v___x_491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v_a_419_);
return v___x_491_;
}
else
{
lean_object* v___x_492_; 
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v_docComment_x3f_487_);
v_docComment_x3f_465_ = v___x_492_;
v___y_466_ = v_a_418_;
v___y_467_ = v_a_419_;
goto v___jp_464_;
}
}
}
else
{
lean_object* v___x_493_; 
lean_dec(v___x_481_);
v___x_493_ = lean_box(0);
v_docComment_x3f_465_ = v___x_493_;
v___y_466_ = v_a_418_;
v___y_467_ = v_a_419_;
goto v___jp_464_;
}
v___jp_425_:
{
lean_object* v___x_432_; lean_object* v_config_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_432_ = lean_unsigned_to_nat(4u);
v_config_433_ = l_Lean_Syntax_getArg(v_x_417_, v___x_432_);
lean_dec(v_x_417_);
v___x_434_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__3));
lean_inc(v_config_433_);
v___x_435_ = l_Lean_Syntax_isOfKind(v_config_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec(v_config_433_);
lean_dec(v_name_x3f_429_);
lean_dec(v___y_428_);
lean_dec(v___y_427_);
lean_dec(v___y_426_);
v___x_436_ = l_Lean_Fmt_Error_partialFormatter;
v___x_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___y_431_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; 
v___x_438_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand(v___y_428_, v_name_x3f_429_, v_config_433_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
v_a_440_ = lean_ctor_get(v___x_438_, 1);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_438_, 2);
v___x_441_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_442_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_426_, v___y_427_, v___x_441_, v_a_439_, v___y_430_, v_a_440_);
return v___x_442_;
}
else
{
lean_dec(v___y_427_);
lean_dec(v___y_426_);
return v___x_438_;
}
}
}
v___jp_443_:
{
lean_object* v___x_449_; lean_object* v_inputFileTk_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_449_ = lean_unsigned_to_nat(2u);
v_inputFileTk_450_ = l_Lean_Syntax_getArg(v_x_417_, v___x_449_);
v___x_451_ = lean_unsigned_to_nat(3u);
v___x_452_ = l_Lean_Syntax_getArg(v_x_417_, v___x_451_);
v___x_453_ = l_Lean_Syntax_isNone(v___x_452_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
lean_inc(v___x_452_);
v___x_454_ = l_Lean_Syntax_matchesNull(v___x_452_, v___y_445_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v___x_452_);
lean_dec(v_inputFileTk_450_);
lean_dec(v_attributes_x3f_446_);
lean_dec(v___y_444_);
lean_dec(v_x_417_);
v___x_455_ = l_Lean_Fmt_Error_partialFormatter;
v___x_456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___y_448_);
return v___x_456_;
}
else
{
lean_object* v_name_x3f_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_name_x3f_457_ = l_Lean_Syntax_getArg(v___x_452_, v___x_424_);
lean_dec(v___x_452_);
v___x_458_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__6));
lean_inc(v_name_x3f_457_);
v___x_459_ = l_Lean_Syntax_isOfKind(v_name_x3f_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec(v_name_x3f_457_);
lean_dec(v_inputFileTk_450_);
lean_dec(v_attributes_x3f_446_);
lean_dec(v___y_444_);
lean_dec(v_x_417_);
v___x_460_ = l_Lean_Fmt_Error_partialFormatter;
v___x_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___y_448_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; 
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v_name_x3f_457_);
v___y_426_ = v___y_444_;
v___y_427_ = v_attributes_x3f_446_;
v___y_428_ = v_inputFileTk_450_;
v_name_x3f_429_ = v___x_462_;
v___y_430_ = v___y_447_;
v___y_431_ = v___y_448_;
goto v___jp_425_;
}
}
}
else
{
lean_object* v___x_463_; 
lean_dec(v___x_452_);
v___x_463_ = lean_box(0);
v___y_426_ = v___y_444_;
v___y_427_ = v_attributes_x3f_446_;
v___y_428_ = v_inputFileTk_450_;
v_name_x3f_429_ = v___x_463_;
v___y_430_ = v___y_447_;
v___y_431_ = v___y_448_;
goto v___jp_425_;
}
}
v___jp_464_:
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = l_Lean_Syntax_getArg(v_x_417_, v___x_468_);
v___x_470_ = l_Lean_Syntax_isNone(v___x_469_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
lean_inc(v___x_469_);
v___x_471_ = l_Lean_Syntax_matchesNull(v___x_469_, v___x_468_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec(v___x_469_);
lean_dec(v_docComment_x3f_465_);
lean_dec(v_x_417_);
v___x_472_ = l_Lean_Fmt_Error_partialFormatter;
v___x_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___y_467_);
return v___x_473_;
}
else
{
lean_object* v_attributes_x3f_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_attributes_x3f_474_ = l_Lean_Syntax_getArg(v___x_469_, v___x_424_);
lean_dec(v___x_469_);
v___x_475_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_474_);
v___x_476_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_attributes_x3f_474_);
lean_dec(v_docComment_x3f_465_);
lean_dec(v_x_417_);
v___x_477_ = l_Lean_Fmt_Error_partialFormatter;
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___y_467_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v_attributes_x3f_474_);
v___y_444_ = v_docComment_x3f_465_;
v___y_445_ = v___x_468_;
v_attributes_x3f_446_ = v___x_479_;
v___y_447_ = v___y_466_;
v___y_448_ = v___y_467_;
goto v___jp_443_;
}
}
}
else
{
lean_object* v___x_480_; 
lean_dec(v___x_469_);
v___x_480_ = lean_box(0);
v___y_444_ = v_docComment_x3f_465_;
v___y_445_ = v___x_468_;
v_attributes_x3f_446_ = v___x_480_;
v___y_447_ = v___y_466_;
v___y_448_ = v___y_467_;
goto v___jp_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtInputFileCommand___boxed(lean_object* v_x_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lake_Formatters_fmtInputFileCommand(v_x_494_, v_a_495_, v_a_496_);
lean_dec_ref(v_a_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1(){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_504_ = l_Lean_Fmt_fmtAttribute;
v___x_505_ = ((lean_object*)(l_Lake_Formatters_fmtInputFileCommand___closed__1));
v___x_506_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___closed__1));
v___x_507_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtInputFileCommand___boxed), 3, 0);
v___x_508_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_504_, v___x_505_, v___x_506_, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1___boxed(lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1();
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtInputDirCommand(lean_object* v_x_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lake_Formatters_fmtInputDirCommand___closed__1));
lean_inc(v_x_516_);
v___x_520_ = l_Lean_Syntax_isOfKind(v_x_516_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_x_516_);
v___x_521_ = l_Lean_Fmt_Error_partialFormatter;
v___x_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_a_518_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v_name_x3f_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v_attributes_x3f_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v_docComment_x3f_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_580_ = l_Lean_Syntax_getArg(v_x_516_, v___x_523_);
v___x_581_ = l_Lean_Syntax_isNone(v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_580_);
v___x_583_ = l_Lean_Syntax_matchesNull(v___x_580_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v___x_580_);
lean_dec(v_x_516_);
v___x_584_ = l_Lean_Fmt_Error_partialFormatter;
v___x_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v_a_518_);
return v___x_585_;
}
else
{
lean_object* v_docComment_x3f_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v_docComment_x3f_586_ = l_Lean_Syntax_getArg(v___x_580_, v___x_523_);
lean_dec(v___x_580_);
v___x_587_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_586_);
v___x_588_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v_docComment_x3f_586_);
lean_dec(v_x_516_);
v___x_589_ = l_Lean_Fmt_Error_partialFormatter;
v___x_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v_a_518_);
return v___x_590_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v_docComment_x3f_586_);
v_docComment_x3f_564_ = v___x_591_;
v___y_565_ = v_a_517_;
v___y_566_ = v_a_518_;
goto v___jp_563_;
}
}
}
else
{
lean_object* v___x_592_; 
lean_dec(v___x_580_);
v___x_592_ = lean_box(0);
v_docComment_x3f_564_ = v___x_592_;
v___y_565_ = v_a_517_;
v___y_566_ = v_a_518_;
goto v___jp_563_;
}
v___jp_524_:
{
lean_object* v___x_531_; lean_object* v_config_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_531_ = lean_unsigned_to_nat(4u);
v_config_532_ = l_Lean_Syntax_getArg(v_x_516_, v___x_531_);
lean_dec(v_x_516_);
v___x_533_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__3));
lean_inc(v_config_532_);
v___x_534_ = l_Lean_Syntax_isOfKind(v_config_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_config_532_);
lean_dec(v_name_x3f_528_);
lean_dec(v___y_527_);
lean_dec(v___y_526_);
lean_dec(v___y_525_);
v___x_535_ = l_Lean_Fmt_Error_partialFormatter;
v___x_536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___y_530_);
return v___x_536_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand(v___y_526_, v_name_x3f_528_, v_config_532_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v_a_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
v_a_539_ = lean_ctor_get(v___x_537_, 1);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_537_, 2);
v___x_540_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_541_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_525_, v___y_527_, v___x_540_, v_a_538_, v___y_529_, v_a_539_);
return v___x_541_;
}
else
{
lean_dec(v___y_527_);
lean_dec(v___y_525_);
return v___x_537_;
}
}
}
v___jp_542_:
{
lean_object* v___x_548_; lean_object* v_inputDirTk_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_548_ = lean_unsigned_to_nat(2u);
v_inputDirTk_549_ = l_Lean_Syntax_getArg(v_x_516_, v___x_548_);
v___x_550_ = lean_unsigned_to_nat(3u);
v___x_551_ = l_Lean_Syntax_getArg(v_x_516_, v___x_550_);
v___x_552_ = l_Lean_Syntax_isNone(v___x_551_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; 
lean_inc(v___x_551_);
v___x_553_ = l_Lean_Syntax_matchesNull(v___x_551_, v___y_544_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec(v___x_551_);
lean_dec(v_inputDirTk_549_);
lean_dec(v_attributes_x3f_545_);
lean_dec(v___y_543_);
lean_dec(v_x_516_);
v___x_554_ = l_Lean_Fmt_Error_partialFormatter;
v___x_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v___y_547_);
return v___x_555_;
}
else
{
lean_object* v_name_x3f_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_name_x3f_556_ = l_Lean_Syntax_getArg(v___x_551_, v___x_523_);
lean_dec(v___x_551_);
v___x_557_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__6));
lean_inc(v_name_x3f_556_);
v___x_558_ = l_Lean_Syntax_isOfKind(v_name_x3f_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v_name_x3f_556_);
lean_dec(v_inputDirTk_549_);
lean_dec(v_attributes_x3f_545_);
lean_dec(v___y_543_);
lean_dec(v_x_516_);
v___x_559_ = l_Lean_Fmt_Error_partialFormatter;
v___x_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___y_547_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v_name_x3f_556_);
v___y_525_ = v___y_543_;
v___y_526_ = v_inputDirTk_549_;
v___y_527_ = v_attributes_x3f_545_;
v_name_x3f_528_ = v___x_561_;
v___y_529_ = v___y_546_;
v___y_530_ = v___y_547_;
goto v___jp_524_;
}
}
}
else
{
lean_object* v___x_562_; 
lean_dec(v___x_551_);
v___x_562_ = lean_box(0);
v___y_525_ = v___y_543_;
v___y_526_ = v_inputDirTk_549_;
v___y_527_ = v_attributes_x3f_545_;
v_name_x3f_528_ = v___x_562_;
v___y_529_ = v___y_546_;
v___y_530_ = v___y_547_;
goto v___jp_524_;
}
}
v___jp_563_:
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = l_Lean_Syntax_getArg(v_x_516_, v___x_567_);
v___x_569_ = l_Lean_Syntax_isNone(v___x_568_);
if (v___x_569_ == 0)
{
uint8_t v___x_570_; 
lean_inc(v___x_568_);
v___x_570_ = l_Lean_Syntax_matchesNull(v___x_568_, v___x_567_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v___x_568_);
lean_dec(v_docComment_x3f_564_);
lean_dec(v_x_516_);
v___x_571_ = l_Lean_Fmt_Error_partialFormatter;
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___y_566_);
return v___x_572_;
}
else
{
lean_object* v_attributes_x3f_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_attributes_x3f_573_ = l_Lean_Syntax_getArg(v___x_568_, v___x_523_);
lean_dec(v___x_568_);
v___x_574_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_573_);
v___x_575_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_attributes_x3f_573_);
lean_dec(v_docComment_x3f_564_);
lean_dec(v_x_516_);
v___x_576_ = l_Lean_Fmt_Error_partialFormatter;
v___x_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___y_566_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; 
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_attributes_x3f_573_);
v___y_543_ = v_docComment_x3f_564_;
v___y_544_ = v___x_567_;
v_attributes_x3f_545_ = v___x_578_;
v___y_546_ = v___y_565_;
v___y_547_ = v___y_566_;
goto v___jp_542_;
}
}
}
else
{
lean_object* v___x_579_; 
lean_dec(v___x_568_);
v___x_579_ = lean_box(0);
v___y_543_ = v_docComment_x3f_564_;
v___y_544_ = v___x_567_;
v_attributes_x3f_545_ = v___x_579_;
v___y_546_ = v___y_565_;
v___y_547_ = v___y_566_;
goto v___jp_542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtInputDirCommand___boxed(lean_object* v_x_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lake_Formatters_fmtInputDirCommand(v_x_593_, v_a_594_, v_a_595_);
lean_dec_ref(v_a_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1(){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_603_ = l_Lean_Fmt_fmtAttribute;
v___x_604_ = ((lean_object*)(l_Lake_Formatters_fmtInputDirCommand___closed__1));
v___x_605_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___closed__1));
v___x_606_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtInputDirCommand___boxed), 3, 0);
v___x_607_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_603_, v___x_604_, v___x_605_, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1___boxed(lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1();
return v_res_609_;
}
}
static lean_object* _init_l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__0(void){
_start:
{
uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = 0;
v___x_611_ = lean_box(0);
v___x_612_ = l_Lean_SourceInfo_fromRef(v___x_611_, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__6(void){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Array_mkArray0___redArg();
return v___x_623_;
}
}
static lean_object* _init_l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__7(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_624_ = lean_obj_once(&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__6, &l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__6_once, _init_l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__6);
v___x_625_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__5));
v___x_626_ = lean_obj_once(&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__0, &l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__0_once, _init_l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__0);
v___x_627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_625_);
lean_ctor_set(v___x_627_, 2, v___x_624_);
return v___x_627_;
}
}
static lean_object* _init_l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__8(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = lean_obj_once(&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__7, &l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__7_once, _init_l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__7);
v___x_629_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3));
v___x_630_ = lean_obj_once(&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__0, &l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__0_once, _init_l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__0);
v___x_631_ = l_Lean_Syntax_node2(v___x_630_, v___x_629_, v___x_628_, v___x_628_);
return v___x_631_;
}
}
static lean_object* _init_l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix(void){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__8, &l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__8_once, _init_l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__8);
return v___x_632_;
}
}
static lean_object* _init_l_Lake_Formatters_fmtPostUpdateDecl___closed__3(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix;
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPostUpdateDecl(lean_object* v_x_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__1));
lean_inc(v_x_670_);
v___x_674_ = l_Lean_Syntax_isOfKind(v_x_670_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v_x_670_);
v___x_675_ = l_Lean_Fmt_Error_partialFormatter;
v___x_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v_a_672_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v_whereDecls_x3f_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v_whereDecls_x3f_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v_binder_x3f_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v_attributes_x3f_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v_docComment_x3f_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_843_ = l_Lean_Syntax_getArg(v_x_670_, v___x_677_);
v___x_844_ = l_Lean_Syntax_isNone(v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_843_);
v___x_846_ = l_Lean_Syntax_matchesNull(v___x_843_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec(v___x_843_);
lean_dec(v_x_670_);
v___x_847_ = l_Lean_Fmt_Error_partialFormatter;
v___x_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v_a_672_);
return v___x_848_;
}
else
{
lean_object* v_docComment_x3f_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v_docComment_x3f_849_ = l_Lean_Syntax_getArg(v___x_843_, v___x_677_);
lean_dec(v___x_843_);
v___x_850_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_849_);
v___x_851_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_849_, v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v_docComment_x3f_849_);
lean_dec(v_x_670_);
v___x_852_ = l_Lean_Fmt_Error_partialFormatter;
v___x_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v_a_672_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_854_, 0, v_docComment_x3f_849_);
v_docComment_x3f_827_ = v___x_854_;
v___y_828_ = v_a_671_;
v___y_829_ = v_a_672_;
goto v___jp_826_;
}
}
}
else
{
lean_object* v___x_855_; 
lean_dec(v___x_843_);
v___x_855_ = lean_box(0);
v_docComment_x3f_827_ = v___x_855_;
v___y_828_ = v_a_671_;
v___y_829_ = v_a_672_;
goto v___jp_826_;
}
v___jp_678_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__2));
v___x_689_ = lean_obj_once(&l_Lake_Formatters_fmtPostUpdateDecl___closed__3, &l_Lake_Formatters_fmtPostUpdateDecl___closed__3_once, _init_l_Lake_Formatters_fmtPostUpdateDecl___closed__3);
lean_inc_n(v___y_684_, 3);
v___x_690_ = l_Lean_Fmt_fmtAssignmentDeclaration(v___y_685_, v___y_684_, v___y_687_, v___x_688_, v___y_684_, v___y_684_, v___y_684_, v___y_680_, v___x_689_, v___y_679_, v___y_686_, v___y_681_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v_a_692_; lean_object* v___x_693_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
v_a_692_ = lean_ctor_get(v___x_690_, 1);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_690_, 2);
v___x_693_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_683_, v___y_682_, v___x_688_, v_a_691_, v___y_686_, v_a_692_);
return v___x_693_;
}
else
{
lean_dec(v___y_683_);
lean_dec(v___y_682_);
return v___x_690_;
}
}
v___jp_694_:
{
lean_object* v___x_703_; 
v___x_703_ = lean_box(0);
if (lean_obj_tag(v___y_696_) == 0)
{
v___y_679_ = v_whereDecls_x3f_700_;
v___y_680_ = v___y_695_;
v___y_681_ = v___y_702_;
v___y_682_ = v___y_698_;
v___y_683_ = v___y_697_;
v___y_684_ = v___x_703_;
v___y_685_ = v___y_699_;
v___y_686_ = v___y_701_;
v___y_687_ = v___x_703_;
goto v___jp_678_;
}
else
{
lean_object* v_val_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
v_val_704_ = lean_ctor_get(v___y_696_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___y_696_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___y_696_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_val_704_);
lean_dec(v___y_696_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_val_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v___y_679_ = v_whereDecls_x3f_700_;
v___y_680_ = v___y_695_;
v___y_681_ = v___y_702_;
v___y_682_ = v___y_698_;
v___y_683_ = v___y_697_;
v___y_684_ = v___x_703_;
v___y_685_ = v___y_699_;
v___y_686_ = v___y_701_;
v___y_687_ = v___x_709_;
goto v___jp_678_;
}
}
}
}
v___jp_712_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__2));
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v___y_713_);
v___x_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_726_, 0, v___y_721_);
lean_inc_n(v___y_718_, 2);
v___x_727_ = l_Lean_Fmt_fmtAssignmentDeclaration(v___y_720_, v___y_718_, v___y_723_, v___x_724_, v___y_718_, v___y_718_, v___x_725_, v___y_717_, v___x_726_, v___y_722_, v___y_714_, v___y_719_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v_a_729_; lean_object* v___x_730_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
v_a_729_ = lean_ctor_get(v___x_727_, 1);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_727_, 2);
v___x_730_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_716_, v___y_715_, v___x_724_, v_a_728_, v___y_714_, v_a_729_);
return v___x_730_;
}
else
{
lean_dec(v___y_716_);
lean_dec(v___y_715_);
return v___x_727_;
}
}
v___jp_731_:
{
lean_object* v___x_742_; 
v___x_742_ = lean_box(0);
if (lean_obj_tag(v___y_733_) == 0)
{
v___y_713_ = v___y_732_;
v___y_714_ = v___y_740_;
v___y_715_ = v___y_736_;
v___y_716_ = v___y_735_;
v___y_717_ = v___y_734_;
v___y_718_ = v___x_742_;
v___y_719_ = v___y_741_;
v___y_720_ = v___y_737_;
v___y_721_ = v___y_738_;
v___y_722_ = v_whereDecls_x3f_739_;
v___y_723_ = v___x_742_;
goto v___jp_712_;
}
else
{
lean_object* v_val_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
v_val_743_ = lean_ctor_get(v___y_733_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___y_733_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___y_733_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_val_743_);
lean_dec(v___y_733_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_val_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
v___y_713_ = v___y_732_;
v___y_714_ = v___y_740_;
v___y_715_ = v___y_736_;
v___y_716_ = v___y_735_;
v___y_717_ = v___y_734_;
v___y_718_ = v___x_742_;
v___y_719_ = v___y_741_;
v___y_720_ = v___y_737_;
v___y_721_ = v___y_738_;
v___y_722_ = v_whereDecls_x3f_739_;
v___y_723_ = v___x_748_;
goto v___jp_712_;
}
}
}
}
v___jp_751_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_761_ = lean_unsigned_to_nat(4u);
v___x_762_ = l_Lean_Syntax_getArg(v_x_670_, v___x_761_);
lean_dec(v_x_670_);
v___x_763_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__5));
lean_inc(v___x_762_);
v___x_764_ = l_Lean_Syntax_isOfKind(v___x_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__7));
lean_inc(v___x_762_);
v___x_766_ = l_Lean_Syntax_isOfKind(v___x_762_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v___x_762_);
lean_dec(v_binder_x3f_758_);
lean_dec(v___y_757_);
lean_dec(v___y_755_);
lean_dec(v___y_754_);
v___x_767_ = l_Lean_Fmt_Error_partialFormatter;
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v___y_760_);
return v___x_768_;
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_769_ = l_Lean_Syntax_getArg(v___x_762_, v___x_677_);
v___x_770_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__9));
lean_inc(v___x_769_);
v___x_771_ = l_Lean_Syntax_isOfKind(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec(v___x_769_);
lean_dec(v___x_762_);
lean_dec(v_binder_x3f_758_);
lean_dec(v___y_757_);
lean_dec(v___y_755_);
lean_dec(v___y_754_);
v___x_772_ = l_Lean_Fmt_Error_partialFormatter;
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___y_760_);
return v___x_773_;
}
else
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = l_Lean_Syntax_getArg(v___x_762_, v___y_756_);
lean_dec(v___x_762_);
v___x_775_ = l_Lean_Syntax_isNone(v___x_774_);
if (v___x_775_ == 0)
{
uint8_t v___x_776_; 
lean_inc(v___x_774_);
v___x_776_ = l_Lean_Syntax_matchesNull(v___x_774_, v___y_756_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec(v___x_774_);
lean_dec(v___x_769_);
lean_dec(v_binder_x3f_758_);
lean_dec(v___y_757_);
lean_dec(v___y_755_);
lean_dec(v___y_754_);
v___x_777_ = l_Lean_Fmt_Error_partialFormatter;
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___y_760_);
return v___x_778_;
}
else
{
lean_object* v_whereDecls_x3f_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_whereDecls_x3f_779_ = l_Lean_Syntax_getArg(v___x_774_, v___x_677_);
lean_dec(v___x_774_);
v___x_780_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__11));
lean_inc(v_whereDecls_x3f_779_);
v___x_781_ = l_Lean_Syntax_isOfKind(v_whereDecls_x3f_779_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec(v_whereDecls_x3f_779_);
lean_dec(v___x_769_);
lean_dec(v_binder_x3f_758_);
lean_dec(v___y_757_);
lean_dec(v___y_755_);
lean_dec(v___y_754_);
v___x_782_ = l_Lean_Fmt_Error_partialFormatter;
v___x_783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v___y_760_);
return v___x_783_;
}
else
{
lean_object* v___x_784_; 
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v_whereDecls_x3f_779_);
v___y_695_ = v___x_769_;
v___y_696_ = v_binder_x3f_758_;
v___y_697_ = v___y_755_;
v___y_698_ = v___y_754_;
v___y_699_ = v___y_757_;
v_whereDecls_x3f_700_ = v___x_784_;
v___y_701_ = v___y_759_;
v___y_702_ = v___y_760_;
goto v___jp_694_;
}
}
}
else
{
lean_object* v___x_785_; 
lean_dec(v___x_774_);
v___x_785_ = lean_box(0);
v___y_695_ = v___x_769_;
v___y_696_ = v_binder_x3f_758_;
v___y_697_ = v___y_755_;
v___y_698_ = v___y_754_;
v___y_699_ = v___y_757_;
v_whereDecls_x3f_700_ = v___x_785_;
v___y_701_ = v___y_759_;
v___y_702_ = v___y_760_;
goto v___jp_694_;
}
}
}
}
else
{
lean_object* v_terminationSuffix_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_terminationSuffix_786_ = l_Lean_Syntax_getArg(v___x_762_, v___y_753_);
v___x_787_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3));
lean_inc(v_terminationSuffix_786_);
v___x_788_ = l_Lean_Syntax_isOfKind(v_terminationSuffix_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v_terminationSuffix_786_);
lean_dec(v___x_762_);
lean_dec(v_binder_x3f_758_);
lean_dec(v___y_757_);
lean_dec(v___y_755_);
lean_dec(v___y_754_);
v___x_789_ = l_Lean_Fmt_Error_partialFormatter;
v___x_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___y_760_);
return v___x_790_;
}
else
{
lean_object* v_colonEqTk_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_colonEqTk_791_ = l_Lean_Syntax_getArg(v___x_762_, v___x_677_);
v___x_792_ = l_Lean_Syntax_getArg(v___x_762_, v___y_756_);
v___x_793_ = l_Lean_Syntax_getArg(v___x_762_, v___y_752_);
lean_dec(v___x_762_);
v___x_794_ = l_Lean_Syntax_isNone(v___x_793_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; 
lean_inc(v___x_793_);
v___x_795_ = l_Lean_Syntax_matchesNull(v___x_793_, v___y_756_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v___x_793_);
lean_dec(v___x_792_);
lean_dec(v_colonEqTk_791_);
lean_dec(v_terminationSuffix_786_);
lean_dec(v_binder_x3f_758_);
lean_dec(v___y_757_);
lean_dec(v___y_755_);
lean_dec(v___y_754_);
v___x_796_ = l_Lean_Fmt_Error_partialFormatter;
v___x_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___y_760_);
return v___x_797_;
}
else
{
lean_object* v_whereDecls_x3f_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_whereDecls_x3f_798_ = l_Lean_Syntax_getArg(v___x_793_, v___x_677_);
lean_dec(v___x_793_);
v___x_799_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__11));
lean_inc(v_whereDecls_x3f_798_);
v___x_800_ = l_Lean_Syntax_isOfKind(v_whereDecls_x3f_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec(v_whereDecls_x3f_798_);
lean_dec(v___x_792_);
lean_dec(v_colonEqTk_791_);
lean_dec(v_terminationSuffix_786_);
lean_dec(v_binder_x3f_758_);
lean_dec(v___y_757_);
lean_dec(v___y_755_);
lean_dec(v___y_754_);
v___x_801_ = l_Lean_Fmt_Error_partialFormatter;
v___x_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v___y_760_);
return v___x_802_;
}
else
{
lean_object* v___x_803_; 
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v_whereDecls_x3f_798_);
v___y_732_ = v_colonEqTk_791_;
v___y_733_ = v_binder_x3f_758_;
v___y_734_ = v___x_792_;
v___y_735_ = v___y_755_;
v___y_736_ = v___y_754_;
v___y_737_ = v___y_757_;
v___y_738_ = v_terminationSuffix_786_;
v_whereDecls_x3f_739_ = v___x_803_;
v___y_740_ = v___y_759_;
v___y_741_ = v___y_760_;
goto v___jp_731_;
}
}
}
else
{
lean_object* v___x_804_; 
lean_dec(v___x_793_);
v___x_804_ = lean_box(0);
v___y_732_ = v_colonEqTk_791_;
v___y_733_ = v_binder_x3f_758_;
v___y_734_ = v___x_792_;
v___y_735_ = v___y_755_;
v___y_736_ = v___y_754_;
v___y_737_ = v___y_757_;
v___y_738_ = v_terminationSuffix_786_;
v_whereDecls_x3f_739_ = v___x_804_;
v___y_740_ = v___y_759_;
v___y_741_ = v___y_760_;
goto v___jp_731_;
}
}
}
}
v___jp_805_:
{
lean_object* v___x_811_; lean_object* v_postUpdateTk_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_811_ = lean_unsigned_to_nat(2u);
v_postUpdateTk_812_ = l_Lean_Syntax_getArg(v_x_670_, v___x_811_);
v___x_813_ = lean_unsigned_to_nat(3u);
v___x_814_ = l_Lean_Syntax_getArg(v_x_670_, v___x_813_);
v___x_815_ = l_Lean_Syntax_isNone(v___x_814_);
if (v___x_815_ == 0)
{
uint8_t v___x_816_; 
lean_inc(v___x_814_);
v___x_816_ = l_Lean_Syntax_matchesNull(v___x_814_, v___y_807_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec(v___x_814_);
lean_dec(v_postUpdateTk_812_);
lean_dec(v_attributes_x3f_808_);
lean_dec(v___y_806_);
lean_dec(v_x_670_);
v___x_817_ = l_Lean_Fmt_Error_partialFormatter;
v___x_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v___y_810_);
return v___x_818_;
}
else
{
lean_object* v_binder_x3f_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_binder_x3f_819_ = l_Lean_Syntax_getArg(v___x_814_, v___x_677_);
lean_dec(v___x_814_);
v___x_820_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__13));
lean_inc(v_binder_x3f_819_);
v___x_821_ = l_Lean_Syntax_isOfKind(v_binder_x3f_819_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec(v_binder_x3f_819_);
lean_dec(v_postUpdateTk_812_);
lean_dec(v_attributes_x3f_808_);
lean_dec(v___y_806_);
lean_dec(v_x_670_);
v___x_822_ = l_Lean_Fmt_Error_partialFormatter;
v___x_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___y_810_);
return v___x_823_;
}
else
{
lean_object* v___x_824_; 
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v_binder_x3f_819_);
v___y_752_ = v___x_813_;
v___y_753_ = v___x_811_;
v___y_754_ = v_attributes_x3f_808_;
v___y_755_ = v___y_806_;
v___y_756_ = v___y_807_;
v___y_757_ = v_postUpdateTk_812_;
v_binder_x3f_758_ = v___x_824_;
v___y_759_ = v___y_809_;
v___y_760_ = v___y_810_;
goto v___jp_751_;
}
}
}
else
{
lean_object* v___x_825_; 
lean_dec(v___x_814_);
v___x_825_ = lean_box(0);
v___y_752_ = v___x_813_;
v___y_753_ = v___x_811_;
v___y_754_ = v_attributes_x3f_808_;
v___y_755_ = v___y_806_;
v___y_756_ = v___y_807_;
v___y_757_ = v_postUpdateTk_812_;
v_binder_x3f_758_ = v___x_825_;
v___y_759_ = v___y_809_;
v___y_760_ = v___y_810_;
goto v___jp_751_;
}
}
v___jp_826_:
{
lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = l_Lean_Syntax_getArg(v_x_670_, v___x_830_);
v___x_832_ = l_Lean_Syntax_isNone(v___x_831_);
if (v___x_832_ == 0)
{
uint8_t v___x_833_; 
lean_inc(v___x_831_);
v___x_833_ = l_Lean_Syntax_matchesNull(v___x_831_, v___x_830_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec(v___x_831_);
lean_dec(v_docComment_x3f_827_);
lean_dec(v_x_670_);
v___x_834_ = l_Lean_Fmt_Error_partialFormatter;
v___x_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___y_829_);
return v___x_835_;
}
else
{
lean_object* v_attributes_x3f_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v_attributes_x3f_836_ = l_Lean_Syntax_getArg(v___x_831_, v___x_677_);
lean_dec(v___x_831_);
v___x_837_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_836_);
v___x_838_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_836_, v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v_attributes_x3f_836_);
lean_dec(v_docComment_x3f_827_);
lean_dec(v_x_670_);
v___x_839_ = l_Lean_Fmt_Error_partialFormatter;
v___x_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v___y_829_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v_attributes_x3f_836_);
v___y_806_ = v_docComment_x3f_827_;
v___y_807_ = v___x_830_;
v_attributes_x3f_808_ = v___x_841_;
v___y_809_ = v___y_828_;
v___y_810_ = v___y_829_;
goto v___jp_805_;
}
}
}
else
{
lean_object* v___x_842_; 
lean_dec(v___x_831_);
v___x_842_ = lean_box(0);
v___y_806_ = v_docComment_x3f_827_;
v___y_807_ = v___x_830_;
v_attributes_x3f_808_ = v___x_842_;
v___y_809_ = v___y_828_;
v___y_810_ = v___y_829_;
goto v___jp_805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPostUpdateDecl___boxed(lean_object* v_x_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lake_Formatters_fmtPostUpdateDecl(v_x_856_, v_a_857_, v_a_858_);
lean_dec_ref(v_a_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1(){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_866_ = l_Lean_Fmt_fmtAttribute;
v___x_867_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__1));
v___x_868_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___closed__1));
v___x_869_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtPostUpdateDecl___boxed), 3, 0);
v___x_870_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_866_, v___x_867_, v___x_868_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1___boxed(lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1();
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromPath(lean_object* v_x_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lake_Formatters_fmtFromPath___closed__1));
lean_inc(v_x_878_);
v___x_882_ = l_Lean_Syntax_isOfKind(v_x_878_, v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec(v_x_878_);
v___x_883_ = l_Lean_Fmt_Error_partialFormatter;
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_a_880_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = l_Lean_Syntax_getArg(v_x_878_, v___x_885_);
v___x_887_ = l_Lean_Syntax_matchesNull(v___x_886_, v___x_885_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v_x_878_);
v___x_888_ = l_Lean_Fmt_Error_partialFormatter;
v___x_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v_a_880_);
return v___x_889_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = l_Lean_Syntax_getArg(v_x_878_, v___x_890_);
lean_dec(v_x_878_);
v___x_892_ = l_Lean_Fmt_fmt(v___x_891_, v_a_879_, v_a_880_);
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromPath___boxed(lean_object* v_x_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lake_Formatters_fmtFromPath(v_x_893_, v_a_894_, v_a_895_);
lean_dec_ref(v_a_894_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1(){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_903_ = l_Lean_Fmt_fmtAttribute;
v___x_904_ = ((lean_object*)(l_Lake_Formatters_fmtFromPath___closed__1));
v___x_905_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___closed__1));
v___x_906_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtFromPath___boxed), 3, 0);
v___x_907_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_903_, v___x_904_, v___x_905_, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1___boxed(lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1();
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromGit(lean_object* v_x_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; 
v___x_918_ = ((lean_object*)(l_Lake_Formatters_fmtFromGit___closed__1));
lean_inc(v_x_915_);
v___x_919_ = l_Lean_Syntax_isOfKind(v_x_915_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec(v_x_915_);
v___x_979_ = l_Lean_Fmt_Error_partialFormatter;
v___x_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v_a_917_);
return v___x_980_;
}
else
{
lean_object* v___x_981_; lean_object* v_gitTk_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v_slashTk_x3f_988_; lean_object* v_subDir_x3f_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___x_1012_; lean_object* v_atTk_x3f_1014_; lean_object* v_rev_x3f_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_981_ = lean_unsigned_to_nat(0u);
v_gitTk_982_ = l_Lean_Syntax_getArg(v_x_915_, v___x_981_);
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = l_Lean_Syntax_getArg(v_x_915_, v___x_983_);
v___x_1012_ = lean_unsigned_to_nat(2u);
v___x_1029_ = l_Lean_Syntax_getArg(v_x_915_, v___x_1012_);
v___x_1030_ = l_Lean_Syntax_isNone(v___x_1029_);
if (v___x_1030_ == 0)
{
uint8_t v___x_1031_; 
lean_inc(v___x_1029_);
v___x_1031_ = l_Lean_Syntax_matchesNull(v___x_1029_, v___x_1012_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec(v___x_1029_);
lean_dec(v___x_984_);
lean_dec(v_gitTk_982_);
lean_dec(v_x_915_);
v___x_1032_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v_a_917_);
return v___x_1033_;
}
else
{
lean_object* v_atTk_x3f_1034_; lean_object* v_rev_x3f_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_atTk_x3f_1034_ = l_Lean_Syntax_getArg(v___x_1029_, v___x_981_);
v_rev_x3f_1035_ = l_Lean_Syntax_getArg(v___x_1029_, v___x_983_);
lean_dec(v___x_1029_);
v___x_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1036_, 0, v_atTk_x3f_1034_);
v___x_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1037_, 0, v_rev_x3f_1035_);
v_atTk_x3f_1014_ = v___x_1036_;
v_rev_x3f_1015_ = v___x_1037_;
v___y_1016_ = v_a_916_;
v___y_1017_ = v_a_917_;
goto v___jp_1013_;
}
}
else
{
lean_object* v___x_1038_; 
lean_dec(v___x_1029_);
v___x_1038_ = lean_box(0);
v_atTk_x3f_1014_ = v___x_1038_;
v_rev_x3f_1015_ = v___x_1038_;
v___y_1016_ = v_a_916_;
v___y_1017_ = v_a_917_;
goto v___jp_1013_;
}
v___jp_985_:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Fmt_fmt(v_gitTk_982_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v_a_994_; lean_object* v___x_995_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
v_a_994_ = lean_ctor_get(v___x_992_, 1);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_992_, 2);
v___x_995_ = l_Lean_Fmt_fmt(v___x_984_, v___y_990_, v_a_994_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v_a_997_; lean_object* v___x_998_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
v_a_997_ = lean_ctor_get(v___x_995_, 1);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_995_, 2);
v___x_998_ = l_Lean_Fmt_fmt_x3f(v___y_986_, v___y_990_, v_a_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
if (lean_obj_tag(v___y_987_) == 0)
{
lean_object* v_a_999_; lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
v_a_1000_ = lean_ctor_get(v___x_998_, 1);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_998_, 2);
v___x_1001_ = lean_box(0);
v___y_954_ = v_subDir_x3f_989_;
v___y_955_ = v_a_996_;
v___y_956_ = v_a_993_;
v___y_957_ = v_slashTk_x3f_988_;
v___y_958_ = v_a_999_;
v___y_959_ = v_a_1000_;
v___y_960_ = v___y_990_;
v___y_961_ = v___x_1001_;
goto v___jp_953_;
}
else
{
lean_object* v_a_1002_; lean_object* v_a_1003_; lean_object* v_val_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
v_a_1002_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_1002_);
v_a_1003_ = lean_ctor_get(v___x_998_, 1);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_998_, 2);
v_val_1004_ = lean_ctor_get(v___y_987_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___y_987_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___y_987_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_val_1004_);
lean_dec(v___y_987_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_val_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
v___y_954_ = v_subDir_x3f_989_;
v___y_955_ = v_a_996_;
v___y_956_ = v_a_993_;
v___y_957_ = v_slashTk_x3f_988_;
v___y_958_ = v_a_1002_;
v___y_959_ = v_a_1003_;
v___y_960_ = v___y_990_;
v___y_961_ = v___x_1009_;
goto v___jp_953_;
}
}
}
}
else
{
lean_dec(v_a_996_);
lean_dec(v_a_993_);
lean_dec(v_subDir_x3f_989_);
lean_dec(v_slashTk_x3f_988_);
lean_dec(v___y_987_);
return v___x_998_;
}
}
else
{
lean_dec(v_a_993_);
lean_dec(v_subDir_x3f_989_);
lean_dec(v_slashTk_x3f_988_);
lean_dec(v___y_987_);
lean_dec(v___y_986_);
return v___x_995_;
}
}
else
{
lean_dec(v_subDir_x3f_989_);
lean_dec(v_slashTk_x3f_988_);
lean_dec(v___y_987_);
lean_dec(v___y_986_);
lean_dec(v___x_984_);
return v___x_992_;
}
}
v___jp_1013_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1018_ = lean_unsigned_to_nat(3u);
v___x_1019_ = l_Lean_Syntax_getArg(v_x_915_, v___x_1018_);
lean_dec(v_x_915_);
v___x_1020_ = l_Lean_Syntax_isNone(v___x_1019_);
if (v___x_1020_ == 0)
{
uint8_t v___x_1021_; 
lean_inc(v___x_1019_);
v___x_1021_ = l_Lean_Syntax_matchesNull(v___x_1019_, v___x_1012_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec(v___x_1019_);
lean_dec(v_rev_x3f_1015_);
lean_dec(v_atTk_x3f_1014_);
lean_dec(v___x_984_);
lean_dec(v_gitTk_982_);
v___x_1022_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___y_1017_);
return v___x_1023_;
}
else
{
lean_object* v_slashTk_x3f_1024_; lean_object* v_subDir_x3f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_slashTk_x3f_1024_ = l_Lean_Syntax_getArg(v___x_1019_, v___x_981_);
v_subDir_x3f_1025_ = l_Lean_Syntax_getArg(v___x_1019_, v___x_983_);
lean_dec(v___x_1019_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_slashTk_x3f_1024_);
v___x_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_subDir_x3f_1025_);
v___y_986_ = v_atTk_x3f_1014_;
v___y_987_ = v_rev_x3f_1015_;
v_slashTk_x3f_988_ = v___x_1026_;
v_subDir_x3f_989_ = v___x_1027_;
v___y_990_ = v___y_1016_;
v___y_991_ = v___y_1017_;
goto v___jp_985_;
}
}
else
{
lean_object* v___x_1028_; 
lean_dec(v___x_1019_);
v___x_1028_ = lean_box(0);
v___y_986_ = v_atTk_x3f_1014_;
v___y_987_ = v_rev_x3f_1015_;
v_slashTk_x3f_988_ = v___x_1028_;
v_subDir_x3f_989_ = v___x_1028_;
v___y_990_ = v___y_1016_;
v___y_991_ = v___y_1017_;
goto v___jp_985_;
}
}
}
v___jp_920_:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_Fmt_fmt_x3f(v___y_928_, v___y_927_, v___y_924_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_952_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_a_931_ = lean_ctor_get(v___x_929_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_952_ == 0)
{
v___x_933_ = v___x_929_;
v_isShared_934_ = v_isSharedCheck_952_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_952_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_935_ = lean_unsigned_to_nat(3u);
v___x_936_ = lean_mk_empty_array_with_capacity(v___x_935_);
lean_inc_ref(v___x_936_);
v___x_937_ = lean_array_push(v___x_936_, v___y_922_);
v___x_938_ = lean_array_push(v___x_937_, v___y_926_);
v___x_939_ = lean_array_push(v___x_938_, v___y_925_);
v___x_940_ = 0;
v___x_941_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_941_, 0, v___x_919_);
lean_ctor_set_uint8(v___x_941_, 1, v___x_940_);
lean_ctor_set_uint8(v___x_941_, 2, v___x_919_);
lean_ctor_set_uint8(v___x_941_, 3, v___x_919_);
v___x_942_ = l_Lean_Fmt_Layouts_infixOperator(v___x_939_, v___x_941_);
v___x_943_ = lean_array_push(v___x_936_, v___x_942_);
v___x_944_ = lean_array_push(v___x_943_, v___y_921_);
v___x_945_ = lean_array_push(v___x_944_, v_a_930_);
v___x_946_ = l_Lean_Fmt_Layouts_infixOperator(v___x_945_, v___x_941_);
lean_dec_ref_known(v___x_941_, 0);
v___x_947_ = 0;
v___x_948_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v___y_923_, v___x_946_, v___x_947_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_948_);
v___x_950_ = v___x_933_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_a_931_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
else
{
lean_dec_ref(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec_ref(v___y_921_);
return v___x_929_;
}
}
v___jp_953_:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_Fmt_fmt_x3f(v___y_961_, v___y_960_, v___y_959_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v_a_964_; lean_object* v___x_965_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
v_a_964_ = lean_ctor_get(v___x_962_, 1);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_962_, 2);
v___x_965_ = l_Lean_Fmt_fmt_x3f(v___y_957_, v___y_960_, v_a_964_);
if (lean_obj_tag(v___x_965_) == 0)
{
if (lean_obj_tag(v___y_954_) == 0)
{
lean_object* v_a_966_; lean_object* v_a_967_; lean_object* v___x_968_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
v_a_967_ = lean_ctor_get(v___x_965_, 1);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_965_, 2);
v___x_968_ = lean_box(0);
v___y_921_ = v_a_966_;
v___y_922_ = v___y_955_;
v___y_923_ = v___y_956_;
v___y_924_ = v_a_967_;
v___y_925_ = v_a_963_;
v___y_926_ = v___y_958_;
v___y_927_ = v___y_960_;
v___y_928_ = v___x_968_;
goto v___jp_920_;
}
else
{
lean_object* v_a_969_; lean_object* v_a_970_; lean_object* v_val_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_a_969_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_969_);
v_a_970_ = lean_ctor_get(v___x_965_, 1);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_965_, 2);
v_val_971_ = lean_ctor_get(v___y_954_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___y_954_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___y_954_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_val_971_);
lean_dec(v___y_954_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_val_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
v___y_921_ = v_a_969_;
v___y_922_ = v___y_955_;
v___y_923_ = v___y_956_;
v___y_924_ = v_a_970_;
v___y_925_ = v_a_963_;
v___y_926_ = v___y_958_;
v___y_927_ = v___y_960_;
v___y_928_ = v___x_976_;
goto v___jp_920_;
}
}
}
}
else
{
lean_dec(v_a_963_);
lean_dec_ref(v___y_958_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
return v___x_965_;
}
}
else
{
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
return v___x_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromGit___boxed(lean_object* v_x_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lake_Formatters_fmtFromGit(v_x_1039_, v_a_1040_, v_a_1041_);
lean_dec_ref(v_a_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1(){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1049_ = l_Lean_Fmt_fmtAttribute;
v___x_1050_ = ((lean_object*)(l_Lake_Formatters_fmtFromGit___closed__1));
v___x_1051_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___closed__1));
v___x_1052_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtFromGit___boxed), 3, 0);
v___x_1053_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1049_, v___x_1050_, v___x_1051_, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1___boxed(lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1();
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromSource(lean_object* v_x_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lake_Formatters_fmtFromSource___closed__1));
lean_inc(v_x_1061_);
v___x_1065_ = l_Lean_Syntax_isOfKind(v_x_1061_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec(v_x_1061_);
v___x_1066_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v_a_1063_);
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = l_Lean_Syntax_getArg(v_x_1061_, v___x_1068_);
lean_dec(v_x_1061_);
v___x_1070_ = ((lean_object*)(l_Lake_Formatters_fmtFromGit___closed__1));
lean_inc(v___x_1069_);
v___x_1071_ = l_Lean_Syntax_isOfKind(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lake_Formatters_fmtFromPath___closed__1));
lean_inc(v___x_1069_);
v___x_1073_ = l_Lean_Syntax_isOfKind(v___x_1069_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec(v___x_1069_);
v___x_1074_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v_a_1063_);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Fmt_fmt(v___x_1069_, v_a_1062_, v_a_1063_);
return v___x_1076_;
}
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Fmt_fmt(v___x_1069_, v_a_1062_, v_a_1063_);
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromSource___boxed(lean_object* v_x_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lake_Formatters_fmtFromSource(v_x_1078_, v_a_1079_, v_a_1080_);
lean_dec_ref(v_a_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1(){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1088_ = l_Lean_Fmt_fmtAttribute;
v___x_1089_ = ((lean_object*)(l_Lake_Formatters_fmtFromSource___closed__1));
v___x_1090_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___closed__1));
v___x_1091_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtFromSource___boxed), 3, 0);
v___x_1092_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1088_, v___x_1089_, v___x_1090_, v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1___boxed(lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1();
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromClause(lean_object* v_x_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lake_Formatters_fmtFromClause___closed__1));
lean_inc(v_x_1100_);
v___x_1104_ = l_Lean_Syntax_isOfKind(v_x_1100_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v_x_1100_);
v___x_1105_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v_a_1102_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = l_Lean_Syntax_getArg(v_x_1100_, v___x_1107_);
v___x_1109_ = ((lean_object*)(l_Lake_Formatters_fmtFromSource___closed__1));
lean_inc(v___x_1108_);
v___x_1110_ = l_Lean_Syntax_isOfKind(v___x_1108_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v___x_1108_);
lean_dec(v_x_1100_);
v___x_1111_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v_a_1102_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; lean_object* v_fromTk_1114_; lean_object* v___x_1115_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v_fromTk_1114_ = l_Lean_Syntax_getArg(v_x_1100_, v___x_1113_);
lean_dec(v_x_1100_);
v___x_1115_ = l_Lean_Fmt_fmt(v_fromTk_1114_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
v_a_1117_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1115_, 2);
v___x_1118_ = l_Lean_Fmt_fmt(v___x_1108_, v_a_1101_, v_a_1117_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1129_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_a_1120_ = lean_ctor_get(v___x_1118_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1122_ = v___x_1118_;
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1124_ = 1;
v___x_1125_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_a_1116_, v_a_1119_, v___x_1124_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1125_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_a_1120_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
else
{
lean_dec(v_a_1116_);
return v___x_1118_;
}
}
else
{
lean_dec(v___x_1108_);
return v___x_1115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFromClause___boxed(lean_object* v_x_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lake_Formatters_fmtFromClause(v_x_1130_, v_a_1131_, v_a_1132_);
lean_dec_ref(v_a_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1(){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1140_ = l_Lean_Fmt_fmtAttribute;
v___x_1141_ = ((lean_object*)(l_Lake_Formatters_fmtFromClause___closed__1));
v___x_1142_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___closed__1));
v___x_1143_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtFromClause___boxed), 3, 0);
v___x_1144_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1140_, v___x_1141_, v___x_1142_, v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1___boxed(lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1();
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithClause(lean_object* v_x_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = ((lean_object*)(l_Lake_Formatters_fmtWithClause___closed__1));
lean_inc(v_x_1152_);
v___x_1156_ = l_Lean_Syntax_isOfKind(v_x_1152_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v_x_1152_);
v___x_1157_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v_a_1154_);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; lean_object* v_withTk_1160_; lean_object* v___x_1161_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
v_withTk_1160_ = l_Lean_Syntax_getArg(v_x_1152_, v___x_1159_);
v___x_1161_ = l_Lean_Fmt_fmt(v_withTk_1160_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
v_a_1163_ = lean_ctor_get(v___x_1161_, 1);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1161_, 2);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = l_Lean_Syntax_getArg(v_x_1152_, v___x_1164_);
lean_dec(v_x_1152_);
v___x_1166_ = l_Lean_Fmt_fmt(v___x_1165_, v_a_1153_, v_a_1163_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1177_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_a_1168_ = lean_ctor_get(v___x_1166_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1170_ = v___x_1166_;
v_isShared_1171_ = v_isSharedCheck_1177_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1177_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1172_ = 1;
v___x_1173_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_a_1162_, v_a_1167_, v___x_1172_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1173_);
v___x_1175_ = v___x_1170_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_a_1168_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
else
{
lean_dec(v_a_1162_);
return v___x_1166_;
}
}
else
{
lean_dec(v_x_1152_);
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithClause___boxed(lean_object* v_x_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lake_Formatters_fmtWithClause(v_x_1178_, v_a_1179_, v_a_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1(){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1188_ = l_Lean_Fmt_fmtAttribute;
v___x_1189_ = ((lean_object*)(l_Lake_Formatters_fmtWithClause___closed__1));
v___x_1190_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___closed__1));
v___x_1191_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtWithClause___boxed), 3, 0);
v___x_1192_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1188_, v___x_1189_, v___x_1190_, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1___boxed(lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1();
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDepName(lean_object* v_x_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1206_; uint8_t v___x_1207_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v_scope_x3f_1239_; lean_object* v_slashTk_x3f_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; 
v___x_1206_ = ((lean_object*)(l_Lake_Formatters_fmtDepName___closed__1));
lean_inc(v_x_1203_);
v___x_1207_ = l_Lean_Syntax_isOfKind(v_x_1203_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec(v_x_1203_);
v___x_1258_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v_a_1205_);
return v___x_1259_;
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = l_Lean_Syntax_getArg(v_x_1203_, v___x_1260_);
v___x_1262_ = l_Lean_Syntax_isNone(v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1261_);
v___x_1264_ = l_Lean_Syntax_matchesNull(v___x_1261_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v___x_1261_);
lean_dec(v_x_1203_);
v___x_1265_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v_a_1205_);
return v___x_1266_;
}
else
{
lean_object* v_scope_x3f_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_scope_x3f_1267_ = l_Lean_Syntax_getArg(v___x_1261_, v___x_1260_);
v___x_1268_ = ((lean_object*)(l_Lake_Formatters_fmtDepName___closed__3));
lean_inc(v_scope_x3f_1267_);
v___x_1269_ = l_Lean_Syntax_isOfKind(v_scope_x3f_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_scope_x3f_1267_);
lean_dec(v___x_1261_);
lean_dec(v_x_1203_);
v___x_1270_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v_a_1205_);
return v___x_1271_;
}
else
{
lean_object* v___x_1272_; lean_object* v_slashTk_x3f_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = lean_unsigned_to_nat(1u);
v_slashTk_x3f_1273_ = l_Lean_Syntax_getArg(v___x_1261_, v___x_1272_);
lean_dec(v___x_1261_);
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_scope_x3f_1267_);
v___x_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_slashTk_x3f_1273_);
v_scope_x3f_1239_ = v___x_1274_;
v_slashTk_x3f_1240_ = v___x_1275_;
v___y_1241_ = v_a_1204_;
v___y_1242_ = v_a_1205_;
goto v___jp_1238_;
}
}
}
else
{
lean_object* v___x_1276_; 
lean_dec(v___x_1261_);
v___x_1276_ = lean_box(0);
v_scope_x3f_1239_ = v___x_1276_;
v_slashTk_x3f_1240_ = v___x_1276_;
v___y_1241_ = v_a_1204_;
v___y_1242_ = v_a_1205_;
goto v___jp_1238_;
}
}
v___jp_1208_:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Fmt_fmt_x3f(v___y_1213_, v___y_1211_, v___y_1210_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v_a_1216_; lean_object* v___x_1217_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
v_a_1216_ = lean_ctor_get(v___x_1214_, 1);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1214_, 2);
v___x_1217_ = l_Lean_Fmt_fmt_x3f(v___y_1212_, v___y_1211_, v_a_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v_a_1219_; lean_object* v___x_1220_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
v_a_1219_ = lean_ctor_get(v___x_1217_, 1);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1217_, 2);
v___x_1220_ = l_Lean_Fmt_fmt(v___y_1209_, v___y_1211_, v_a_1219_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1237_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_a_1222_ = lean_ctor_get(v___x_1220_, 1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1224_ = v___x_1220_;
v_isShared_1225_ = v_isSharedCheck_1237_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1237_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1226_ = lean_unsigned_to_nat(3u);
v___x_1227_ = lean_mk_empty_array_with_capacity(v___x_1226_);
v___x_1228_ = lean_array_push(v___x_1227_, v_a_1215_);
v___x_1229_ = lean_array_push(v___x_1228_, v_a_1218_);
v___x_1230_ = lean_array_push(v___x_1229_, v_a_1221_);
v___x_1231_ = 0;
v___x_1232_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1232_, 0, v___x_1207_);
lean_ctor_set_uint8(v___x_1232_, 1, v___x_1231_);
lean_ctor_set_uint8(v___x_1232_, 2, v___x_1207_);
lean_ctor_set_uint8(v___x_1232_, 3, v___x_1207_);
v___x_1233_ = l_Lean_Fmt_Layouts_infixOperator(v___x_1230_, v___x_1232_);
lean_dec_ref_known(v___x_1232_, 0);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1233_);
v___x_1235_ = v___x_1224_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_a_1222_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
else
{
lean_dec(v_a_1218_);
lean_dec(v_a_1215_);
return v___x_1220_;
}
}
else
{
lean_dec(v_a_1215_);
lean_dec(v___y_1209_);
return v___x_1217_;
}
}
else
{
lean_dec(v___y_1212_);
lean_dec(v___y_1209_);
return v___x_1214_;
}
}
v___jp_1238_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = l_Lean_Syntax_getArg(v_x_1203_, v___x_1243_);
lean_dec(v_x_1203_);
v___x_1245_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__6));
lean_inc(v___x_1244_);
v___x_1246_ = l_Lean_Syntax_isOfKind(v___x_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec(v___x_1244_);
lean_dec(v_slashTk_x3f_1240_);
lean_dec(v_scope_x3f_1239_);
v___x_1247_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set(v___x_1248_, 1, v___y_1242_);
return v___x_1248_;
}
else
{
if (lean_obj_tag(v_scope_x3f_1239_) == 0)
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_box(0);
v___y_1209_ = v___x_1244_;
v___y_1210_ = v___y_1242_;
v___y_1211_ = v___y_1241_;
v___y_1212_ = v_slashTk_x3f_1240_;
v___y_1213_ = v___x_1249_;
goto v___jp_1208_;
}
else
{
lean_object* v_val_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
v_val_1250_ = lean_ctor_get(v_scope_x3f_1239_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_scope_x3f_1239_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v_scope_x3f_1239_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_val_1250_);
lean_dec(v_scope_x3f_1239_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_val_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
v___y_1209_ = v___x_1244_;
v___y_1210_ = v___y_1242_;
v___y_1211_ = v___y_1241_;
v___y_1212_ = v_slashTk_x3f_1240_;
v___y_1213_ = v___x_1255_;
goto v___jp_1208_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtDepName___boxed(lean_object* v_x_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lake_Formatters_fmtDepName(v_x_1277_, v_a_1278_, v_a_1279_);
lean_dec_ref(v_a_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1(){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1287_ = l_Lean_Fmt_fmtAttribute;
v___x_1288_ = ((lean_object*)(l_Lake_Formatters_fmtDepName___closed__1));
v___x_1289_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___closed__1));
v___x_1290_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtDepName___boxed), 3, 0);
v___x_1291_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1287_, v___x_1288_, v___x_1289_, v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1___boxed(lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1();
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtVerSpec(lean_object* v_x_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_gitTk_x3f_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = ((lean_object*)(l_Lake_Formatters_fmtVerSpec___closed__1));
lean_inc(v_x_1299_);
v___x_1324_ = l_Lean_Syntax_isOfKind(v_x_1299_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec(v_x_1299_);
v___x_1325_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v_a_1301_);
return v___x_1326_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = l_Lean_Syntax_getArg(v_x_1299_, v___x_1327_);
v___x_1329_ = l_Lean_Syntax_isNone(v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1328_);
v___x_1331_ = l_Lean_Syntax_matchesNull(v___x_1328_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec(v___x_1328_);
lean_dec(v_x_1299_);
v___x_1332_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v_a_1301_);
return v___x_1333_;
}
else
{
lean_object* v_gitTk_x3f_1334_; lean_object* v___x_1335_; 
v_gitTk_x3f_1334_ = l_Lean_Syntax_getArg(v___x_1328_, v___x_1327_);
lean_dec(v___x_1328_);
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_gitTk_x3f_1334_);
v_gitTk_x3f_1303_ = v___x_1335_;
v___y_1304_ = v_a_1300_;
v___y_1305_ = v_a_1301_;
goto v___jp_1302_;
}
}
else
{
lean_object* v___x_1336_; 
lean_dec(v___x_1328_);
v___x_1336_ = lean_box(0);
v_gitTk_x3f_1303_ = v___x_1336_;
v___y_1304_ = v_a_1300_;
v___y_1305_ = v_a_1301_;
goto v___jp_1302_;
}
}
v___jp_1302_:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Fmt_fmt_x3f(v_gitTk_x3f_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v_a_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
v_a_1308_ = lean_ctor_get(v___x_1306_, 1);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1306_, 2);
v___x_1309_ = lean_unsigned_to_nat(1u);
v___x_1310_ = l_Lean_Syntax_getArg(v_x_1299_, v___x_1309_);
lean_dec(v_x_1299_);
v___x_1311_ = l_Lean_Fmt_fmt(v___x_1310_, v___y_1304_, v_a_1308_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1322_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_a_1313_ = lean_ctor_get(v___x_1311_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1315_ = v___x_1311_;
v_isShared_1316_ = v_isSharedCheck_1322_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1322_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1317_ = 1;
v___x_1318_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_a_1307_, v_a_1312_, v___x_1317_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1318_);
v___x_1320_ = v___x_1315_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_a_1313_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
else
{
lean_dec(v_a_1307_);
return v___x_1311_;
}
}
else
{
lean_dec(v_x_1299_);
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtVerSpec___boxed(lean_object* v_x_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lake_Formatters_fmtVerSpec(v_x_1337_, v_a_1338_, v_a_1339_);
lean_dec_ref(v_a_1338_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1(){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1347_ = l_Lean_Fmt_fmtAttribute;
v___x_1348_ = ((lean_object*)(l_Lake_Formatters_fmtVerSpec___closed__1));
v___x_1349_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___closed__1));
v___x_1350_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtVerSpec___boxed), 3, 0);
v___x_1351_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1347_, v___x_1348_, v___x_1349_, v___x_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1___boxed(lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1();
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtRequireDecl(lean_object* v_x_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = ((lean_object*)(l_Lake_Formatters_fmtRequireDecl___closed__1));
lean_inc(v_x_1369_);
v___x_1373_ = l_Lean_Syntax_isOfKind(v_x_1369_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec(v_x_1369_);
v___x_1374_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v_a_1371_);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v_withClause_x3f_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v_fromClause_x3f_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v_atTk_x3f_1521_; lean_object* v_ver_x3f_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v_docComment_x3f_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1573_ = l_Lean_Syntax_getArg(v_x_1369_, v___x_1376_);
v___x_1574_ = l_Lean_Syntax_isNone(v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1573_);
v___x_1576_ = l_Lean_Syntax_matchesNull(v___x_1573_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec(v___x_1573_);
lean_dec(v_x_1369_);
v___x_1577_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v_a_1371_);
return v___x_1578_;
}
else
{
lean_object* v_docComment_x3f_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v_docComment_x3f_1579_ = l_Lean_Syntax_getArg(v___x_1573_, v___x_1376_);
lean_dec(v___x_1573_);
v___x_1580_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_1579_);
v___x_1581_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_1579_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v_docComment_x3f_1579_);
lean_dec(v_x_1369_);
v___x_1582_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v_a_1371_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1584_, 0, v_docComment_x3f_1579_);
v_docComment_x3f_1538_ = v___x_1584_;
v___y_1539_ = v_a_1370_;
v___y_1540_ = v_a_1371_;
goto v___jp_1537_;
}
}
}
else
{
lean_object* v___x_1585_; 
lean_dec(v___x_1573_);
v___x_1585_ = lean_box(0);
v_docComment_x3f_1538_ = v___x_1585_;
v___y_1539_ = v_a_1370_;
v___y_1540_ = v_a_1371_;
goto v___jp_1537_;
}
v___jp_1377_:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_Fmt_fmt_x3f(v___y_1386_, v___y_1378_, v___y_1385_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v_a_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
v_a_1389_ = lean_ctor_get(v___x_1387_, 1);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1387_, 2);
v___x_1390_ = lean_unsigned_to_nat(3u);
v___x_1391_ = lean_mk_empty_array_with_capacity(v___x_1390_);
v___x_1392_ = lean_array_push(v___x_1391_, v___y_1380_);
v___x_1393_ = lean_array_push(v___x_1392_, v___y_1383_);
v___x_1394_ = lean_array_push(v___x_1393_, v___y_1379_);
v___x_1395_ = 0;
v___x_1396_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1396_, 0, v___x_1373_);
lean_ctor_set_uint8(v___x_1396_, 1, v___x_1395_);
lean_ctor_set_uint8(v___x_1396_, 2, v___x_1373_);
lean_ctor_set_uint8(v___x_1396_, 3, v___x_1373_);
v___x_1397_ = l_Lean_Fmt_Layouts_infixOperator(v___x_1394_, v___x_1396_);
lean_dec_ref_known(v___x_1396_, 0);
v___x_1398_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1398_, 0, v___y_1384_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*1, v___x_1373_);
v___x_1399_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1399_, 0, v___x_1397_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*1, v___x_1373_);
v___x_1400_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1400_, 0, v___y_1382_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*1, v___x_1373_);
v___x_1401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1401_, 0, v_a_1388_);
lean_ctor_set_uint8(v___x_1401_, sizeof(void*)*1, v___x_1373_);
v___x_1402_ = lean_unsigned_to_nat(4u);
v___x_1403_ = lean_mk_empty_array_with_capacity(v___x_1402_);
v___x_1404_ = lean_array_push(v___x_1403_, v___x_1398_);
v___x_1405_ = lean_array_push(v___x_1404_, v___x_1399_);
v___x_1406_ = lean_array_push(v___x_1405_, v___x_1400_);
v___x_1407_ = lean_array_push(v___x_1406_, v___x_1401_);
v___x_1408_ = l_Lean_Fmt_Layouts_blocks(v___x_1407_, v___x_1373_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = lean_box(0);
v___x_1410_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_1411_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_1381_, v___x_1409_, v___x_1410_, v___x_1408_, v___y_1378_, v_a_1389_);
return v___x_1411_;
}
else
{
lean_dec_ref(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v___x_1387_;
}
}
v___jp_1412_:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Fmt_fmt_x3f(v___y_1421_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1422_) == 0)
{
if (lean_obj_tag(v___y_1418_) == 0)
{
lean_object* v_a_1423_; lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
v_a_1424_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1422_, 2);
v___x_1425_ = lean_box(0);
v___y_1378_ = v___y_1413_;
v___y_1379_ = v___y_1416_;
v___y_1380_ = v___y_1415_;
v___y_1381_ = v___y_1417_;
v___y_1382_ = v_a_1423_;
v___y_1383_ = v___y_1419_;
v___y_1384_ = v___y_1420_;
v___y_1385_ = v_a_1424_;
v___y_1386_ = v___x_1425_;
goto v___jp_1377_;
}
else
{
lean_object* v_a_1426_; lean_object* v_a_1427_; lean_object* v_val_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
v_a_1426_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1426_);
v_a_1427_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1422_, 2);
v_val_1428_ = lean_ctor_get(v___y_1418_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___y_1418_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___y_1418_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_val_1428_);
lean_dec(v___y_1418_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_val_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
v___y_1378_ = v___y_1413_;
v___y_1379_ = v___y_1416_;
v___y_1380_ = v___y_1415_;
v___y_1381_ = v___y_1417_;
v___y_1382_ = v_a_1426_;
v___y_1383_ = v___y_1419_;
v___y_1384_ = v___y_1420_;
v___y_1385_ = v_a_1427_;
v___y_1386_ = v___x_1433_;
goto v___jp_1377_;
}
}
}
}
else
{
lean_dec_ref(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v___x_1422_;
}
}
v___jp_1436_:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Fmt_fmt_x3f(v___y_1445_, v___y_1437_, v___y_1444_);
if (lean_obj_tag(v___x_1446_) == 0)
{
if (lean_obj_tag(v___y_1440_) == 0)
{
lean_object* v_a_1447_; lean_object* v_a_1448_; lean_object* v___x_1449_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
v_a_1448_ = lean_ctor_get(v___x_1446_, 1);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1446_, 2);
v___x_1449_ = lean_box(0);
v___y_1413_ = v___y_1437_;
v___y_1414_ = v_a_1448_;
v___y_1415_ = v___y_1438_;
v___y_1416_ = v_a_1447_;
v___y_1417_ = v___y_1439_;
v___y_1418_ = v___y_1441_;
v___y_1419_ = v___y_1442_;
v___y_1420_ = v___y_1443_;
v___y_1421_ = v___x_1449_;
goto v___jp_1412_;
}
else
{
lean_object* v_a_1450_; lean_object* v_a_1451_; lean_object* v_val_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
v_a_1450_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1450_);
v_a_1451_ = lean_ctor_get(v___x_1446_, 1);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1446_, 2);
v_val_1452_ = lean_ctor_get(v___y_1440_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___y_1440_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___y_1440_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_val_1452_);
lean_dec(v___y_1440_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_val_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
v___y_1413_ = v___y_1437_;
v___y_1414_ = v_a_1451_;
v___y_1415_ = v___y_1438_;
v___y_1416_ = v_a_1450_;
v___y_1417_ = v___y_1439_;
v___y_1418_ = v___y_1441_;
v___y_1419_ = v___y_1442_;
v___y_1420_ = v___y_1443_;
v___y_1421_ = v___x_1457_;
goto v___jp_1412_;
}
}
}
}
else
{
lean_dec_ref(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v___x_1446_;
}
}
v___jp_1460_:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Fmt_fmt(v___y_1466_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v_a_1472_; lean_object* v___x_1473_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
v_a_1472_ = lean_ctor_get(v___x_1470_, 1);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1470_, 2);
v___x_1473_ = l_Lean_Fmt_fmt(v___y_1465_, v___y_1468_, v_a_1472_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v_a_1475_; lean_object* v___x_1476_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
v_a_1475_ = lean_ctor_get(v___x_1473_, 1);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1473_, 2);
v___x_1476_ = l_Lean_Fmt_fmt_x3f(v___y_1464_, v___y_1468_, v_a_1475_);
if (lean_obj_tag(v___x_1476_) == 0)
{
if (lean_obj_tag(v___y_1461_) == 0)
{
lean_object* v_a_1477_; lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
v_a_1478_ = lean_ctor_get(v___x_1476_, 1);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1476_, 2);
v___x_1479_ = lean_box(0);
v___y_1437_ = v___y_1468_;
v___y_1438_ = v_a_1474_;
v___y_1439_ = v___y_1462_;
v___y_1440_ = v___y_1463_;
v___y_1441_ = v_withClause_x3f_1467_;
v___y_1442_ = v_a_1477_;
v___y_1443_ = v_a_1471_;
v___y_1444_ = v_a_1478_;
v___y_1445_ = v___x_1479_;
goto v___jp_1436_;
}
else
{
lean_object* v_a_1480_; lean_object* v_a_1481_; lean_object* v_val_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_a_1480_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1480_);
v_a_1481_ = lean_ctor_get(v___x_1476_, 1);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1476_, 2);
v_val_1482_ = lean_ctor_get(v___y_1461_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___y_1461_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___y_1461_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_val_1482_);
lean_dec(v___y_1461_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_val_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
v___y_1437_ = v___y_1468_;
v___y_1438_ = v_a_1474_;
v___y_1439_ = v___y_1462_;
v___y_1440_ = v___y_1463_;
v___y_1441_ = v_withClause_x3f_1467_;
v___y_1442_ = v_a_1480_;
v___y_1443_ = v_a_1471_;
v___y_1444_ = v_a_1481_;
v___y_1445_ = v___x_1487_;
goto v___jp_1436_;
}
}
}
}
else
{
lean_dec(v_a_1474_);
lean_dec(v_a_1471_);
lean_dec(v_withClause_x3f_1467_);
lean_dec(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec(v___y_1461_);
return v___x_1476_;
}
}
else
{
lean_dec(v_a_1471_);
lean_dec(v_withClause_x3f_1467_);
lean_dec(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec(v___y_1461_);
return v___x_1473_;
}
}
else
{
lean_dec(v_withClause_x3f_1467_);
lean_dec(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec(v___y_1461_);
return v___x_1470_;
}
}
v___jp_1490_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = lean_unsigned_to_nat(3u);
v___x_1502_ = l_Lean_Syntax_getArg(v___y_1493_, v___x_1501_);
lean_dec(v___y_1493_);
v___x_1503_ = l_Lean_Syntax_isNone(v___x_1502_);
if (v___x_1503_ == 0)
{
uint8_t v___x_1504_; 
lean_inc(v___x_1502_);
v___x_1504_ = l_Lean_Syntax_matchesNull(v___x_1502_, v___y_1495_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec(v___x_1502_);
lean_dec(v_fromClause_x3f_1498_);
lean_dec(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec(v___y_1494_);
lean_dec(v___y_1492_);
lean_dec(v___y_1491_);
v___x_1505_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___y_1500_);
return v___x_1506_;
}
else
{
lean_object* v_withClause_x3f_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_withClause_x3f_1507_ = l_Lean_Syntax_getArg(v___x_1502_, v___x_1376_);
lean_dec(v___x_1502_);
v___x_1508_ = ((lean_object*)(l_Lake_Formatters_fmtWithClause___closed__1));
lean_inc(v_withClause_x3f_1507_);
v___x_1509_ = l_Lean_Syntax_isOfKind(v_withClause_x3f_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec(v_withClause_x3f_1507_);
lean_dec(v_fromClause_x3f_1498_);
lean_dec(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec(v___y_1494_);
lean_dec(v___y_1492_);
lean_dec(v___y_1491_);
v___x_1510_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v___y_1500_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_withClause_x3f_1507_);
v___y_1461_ = v___y_1491_;
v___y_1462_ = v___y_1492_;
v___y_1463_ = v_fromClause_x3f_1498_;
v___y_1464_ = v___y_1494_;
v___y_1465_ = v___y_1496_;
v___y_1466_ = v___y_1497_;
v_withClause_x3f_1467_ = v___x_1512_;
v___y_1468_ = v___y_1499_;
v___y_1469_ = v___y_1500_;
goto v___jp_1460_;
}
}
}
else
{
lean_object* v___x_1513_; 
lean_dec(v___x_1502_);
v___x_1513_ = lean_box(0);
v___y_1461_ = v___y_1491_;
v___y_1462_ = v___y_1492_;
v___y_1463_ = v_fromClause_x3f_1498_;
v___y_1464_ = v___y_1494_;
v___y_1465_ = v___y_1496_;
v___y_1466_ = v___y_1497_;
v_withClause_x3f_1467_ = v___x_1513_;
v___y_1468_ = v___y_1499_;
v___y_1469_ = v___y_1500_;
goto v___jp_1460_;
}
}
v___jp_1514_:
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = l_Lean_Syntax_getArg(v___y_1516_, v___y_1518_);
v___x_1526_ = l_Lean_Syntax_isNone(v___x_1525_);
if (v___x_1526_ == 0)
{
uint8_t v___x_1527_; 
lean_inc(v___x_1525_);
v___x_1527_ = l_Lean_Syntax_matchesNull(v___x_1525_, v___y_1517_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v___x_1525_);
lean_dec(v_ver_x3f_1522_);
lean_dec(v_atTk_x3f_1521_);
lean_dec(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v___y_1516_);
lean_dec(v___y_1515_);
v___x_1528_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v___y_1524_);
return v___x_1529_;
}
else
{
lean_object* v_fromClause_x3f_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v_fromClause_x3f_1530_ = l_Lean_Syntax_getArg(v___x_1525_, v___x_1376_);
lean_dec(v___x_1525_);
v___x_1531_ = ((lean_object*)(l_Lake_Formatters_fmtFromClause___closed__1));
lean_inc(v_fromClause_x3f_1530_);
v___x_1532_ = l_Lean_Syntax_isOfKind(v_fromClause_x3f_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec(v_fromClause_x3f_1530_);
lean_dec(v_ver_x3f_1522_);
lean_dec(v_atTk_x3f_1521_);
lean_dec(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v___y_1516_);
lean_dec(v___y_1515_);
v___x_1533_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___y_1524_);
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_fromClause_x3f_1530_);
v___y_1491_ = v_ver_x3f_1522_;
v___y_1492_ = v___y_1515_;
v___y_1493_ = v___y_1516_;
v___y_1494_ = v_atTk_x3f_1521_;
v___y_1495_ = v___y_1517_;
v___y_1496_ = v___y_1519_;
v___y_1497_ = v___y_1520_;
v_fromClause_x3f_1498_ = v___x_1535_;
v___y_1499_ = v___y_1523_;
v___y_1500_ = v___y_1524_;
goto v___jp_1490_;
}
}
}
else
{
lean_object* v___x_1536_; 
lean_dec(v___x_1525_);
v___x_1536_ = lean_box(0);
v___y_1491_ = v_ver_x3f_1522_;
v___y_1492_ = v___y_1515_;
v___y_1493_ = v___y_1516_;
v___y_1494_ = v_atTk_x3f_1521_;
v___y_1495_ = v___y_1517_;
v___y_1496_ = v___y_1519_;
v___y_1497_ = v___y_1520_;
v_fromClause_x3f_1498_ = v___x_1536_;
v___y_1499_ = v___y_1523_;
v___y_1500_ = v___y_1524_;
goto v___jp_1490_;
}
}
v___jp_1537_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1541_ = lean_unsigned_to_nat(2u);
v___x_1542_ = l_Lean_Syntax_getArg(v_x_1369_, v___x_1541_);
v___x_1543_ = ((lean_object*)(l_Lake_Formatters_fmtRequireDecl___closed__3));
lean_inc(v___x_1542_);
v___x_1544_ = l_Lean_Syntax_isOfKind(v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_dec(v___x_1542_);
lean_dec(v_docComment_x3f_1538_);
lean_dec(v_x_1369_);
v___x_1545_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___y_1540_);
return v___x_1546_;
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1547_ = l_Lean_Syntax_getArg(v___x_1542_, v___x_1376_);
v___x_1548_ = ((lean_object*)(l_Lake_Formatters_fmtDepName___closed__1));
lean_inc(v___x_1547_);
v___x_1549_ = l_Lean_Syntax_isOfKind(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec(v___x_1547_);
lean_dec(v___x_1542_);
lean_dec(v_docComment_x3f_1538_);
lean_dec(v_x_1369_);
v___x_1550_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v___y_1540_);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; lean_object* v_requireTk_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1552_ = lean_unsigned_to_nat(1u);
v_requireTk_1553_ = l_Lean_Syntax_getArg(v_x_1369_, v___x_1552_);
lean_dec(v_x_1369_);
v___x_1554_ = l_Lean_Syntax_getArg(v___x_1542_, v___x_1552_);
v___x_1555_ = l_Lean_Syntax_isNone(v___x_1554_);
if (v___x_1555_ == 0)
{
uint8_t v___x_1556_; 
lean_inc(v___x_1554_);
v___x_1556_ = l_Lean_Syntax_matchesNull(v___x_1554_, v___x_1552_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec(v___x_1554_);
lean_dec(v_requireTk_1553_);
lean_dec(v___x_1547_);
lean_dec(v___x_1542_);
lean_dec(v_docComment_x3f_1538_);
v___x_1557_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v___y_1540_);
return v___x_1558_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1559_ = l_Lean_Syntax_getArg(v___x_1554_, v___x_1376_);
lean_dec(v___x_1554_);
v___x_1560_ = ((lean_object*)(l_Lake_Formatters_fmtRequireDecl___closed__5));
lean_inc(v___x_1559_);
v___x_1561_ = l_Lean_Syntax_isOfKind(v___x_1559_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v___x_1559_);
lean_dec(v_requireTk_1553_);
lean_dec(v___x_1547_);
lean_dec(v___x_1542_);
lean_dec(v_docComment_x3f_1538_);
v___x_1562_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v___y_1540_);
return v___x_1563_;
}
else
{
lean_object* v_ver_x3f_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v_ver_x3f_1564_ = l_Lean_Syntax_getArg(v___x_1559_, v___x_1552_);
v___x_1565_ = ((lean_object*)(l_Lake_Formatters_fmtVerSpec___closed__1));
lean_inc(v_ver_x3f_1564_);
v___x_1566_ = l_Lean_Syntax_isOfKind(v_ver_x3f_1564_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec(v_ver_x3f_1564_);
lean_dec(v___x_1559_);
lean_dec(v_requireTk_1553_);
lean_dec(v___x_1547_);
lean_dec(v___x_1542_);
lean_dec(v_docComment_x3f_1538_);
v___x_1567_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v___y_1540_);
return v___x_1568_;
}
else
{
lean_object* v_atTk_x3f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_atTk_x3f_1569_ = l_Lean_Syntax_getArg(v___x_1559_, v___x_1376_);
lean_dec(v___x_1559_);
v___x_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_atTk_x3f_1569_);
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_ver_x3f_1564_);
v___y_1515_ = v_docComment_x3f_1538_;
v___y_1516_ = v___x_1542_;
v___y_1517_ = v___x_1552_;
v___y_1518_ = v___x_1541_;
v___y_1519_ = v___x_1547_;
v___y_1520_ = v_requireTk_1553_;
v_atTk_x3f_1521_ = v___x_1570_;
v_ver_x3f_1522_ = v___x_1571_;
v___y_1523_ = v___y_1539_;
v___y_1524_ = v___y_1540_;
goto v___jp_1514_;
}
}
}
}
else
{
lean_object* v___x_1572_; 
lean_dec(v___x_1554_);
v___x_1572_ = lean_box(0);
v___y_1515_ = v_docComment_x3f_1538_;
v___y_1516_ = v___x_1542_;
v___y_1517_ = v___x_1552_;
v___y_1518_ = v___x_1541_;
v___y_1519_ = v___x_1547_;
v___y_1520_ = v_requireTk_1553_;
v_atTk_x3f_1521_ = v___x_1572_;
v_ver_x3f_1522_ = v___x_1572_;
v___y_1523_ = v___y_1539_;
v___y_1524_ = v___y_1540_;
goto v___jp_1514_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtRequireDecl___boxed(lean_object* v_x_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lake_Formatters_fmtRequireDecl(v_x_1586_, v_a_1587_, v_a_1588_);
lean_dec_ref(v_a_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1(){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1596_ = l_Lean_Fmt_fmtAttribute;
v___x_1597_ = ((lean_object*)(l_Lake_Formatters_fmtRequireDecl___closed__1));
v___x_1598_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___closed__1));
v___x_1599_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtRequireDecl___boxed), 3, 0);
v___x_1600_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1596_, v___x_1597_, v___x_1598_, v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1___boxed(lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1();
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg(lean_object* v_binder_x3f_1620_, lean_object* v_a_1621_){
_start:
{
if (lean_obj_tag(v_binder_x3f_1620_) == 1)
{
lean_object* v_val_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1701_; 
v_val_1622_ = lean_ctor_get(v_binder_x3f_1620_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_binder_x3f_1620_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1624_ = v_binder_x3f_1620_;
v_isShared_1625_ = v_isSharedCheck_1701_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_val_1622_);
lean_dec(v_binder_x3f_1620_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1701_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__13));
lean_inc(v_val_1622_);
v___x_1627_ = l_Lean_Syntax_isOfKind(v_val_1622_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_del_object(v___x_1624_);
lean_dec(v_val_1622_);
v___x_1628_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v_a_1621_);
return v___x_1629_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = l_Lean_Syntax_getArg(v_val_1622_, v___x_1630_);
lean_dec(v_val_1622_);
v___x_1632_ = ((lean_object*)(l_Lake_Formatters_fmtGetConfig___closed__5));
lean_inc(v___x_1631_);
v___x_1633_ = l_Lean_Syntax_isOfKind(v___x_1631_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__1));
lean_inc(v___x_1631_);
v___x_1635_ = l_Lean_Syntax_isOfKind(v___x_1631_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v___x_1631_);
lean_del_object(v___x_1624_);
v___x_1636_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v_a_1621_);
return v___x_1637_;
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = l_Lean_Syntax_getArg(v___x_1631_, v___x_1638_);
lean_inc(v___x_1639_);
v___x_1640_ = l_Lean_Syntax_isOfKind(v___x_1639_, v___x_1632_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_dec(v___x_1639_);
lean_dec(v___x_1631_);
lean_del_object(v___x_1624_);
v___x_1641_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_a_1621_);
return v___x_1642_;
}
else
{
lean_object* v_lbTk_1643_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v_typeAscriptionTk_x3f_1670_; lean_object* v_type_x3f_1671_; lean_object* v___y_1672_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v_lbTk_1643_ = l_Lean_Syntax_getArg(v___x_1631_, v___x_1630_);
v___x_1684_ = lean_unsigned_to_nat(2u);
v___x_1685_ = l_Lean_Syntax_getArg(v___x_1631_, v___x_1684_);
v___x_1686_ = l_Lean_Syntax_isNone(v___x_1685_);
if (v___x_1686_ == 0)
{
uint8_t v___x_1687_; 
lean_inc(v___x_1685_);
v___x_1687_ = l_Lean_Syntax_matchesNull(v___x_1685_, v___x_1684_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_dec(v___x_1685_);
lean_dec(v_lbTk_1643_);
lean_dec(v___x_1639_);
lean_dec(v___x_1631_);
lean_del_object(v___x_1624_);
v___x_1688_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v_a_1621_);
return v___x_1689_;
}
else
{
lean_object* v_typeAscriptionTk_x3f_1690_; lean_object* v_type_x3f_1691_; lean_object* v___x_1693_; 
v_typeAscriptionTk_x3f_1690_ = l_Lean_Syntax_getArg(v___x_1685_, v___x_1630_);
v_type_x3f_1691_ = l_Lean_Syntax_getArg(v___x_1685_, v___x_1638_);
lean_dec(v___x_1685_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v_typeAscriptionTk_x3f_1690_);
v___x_1693_ = v___x_1624_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_typeAscriptionTk_x3f_1690_);
v___x_1693_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1694_, 0, v_type_x3f_1691_);
v_typeAscriptionTk_x3f_1670_ = v___x_1693_;
v_type_x3f_1671_ = v___x_1694_;
v___y_1672_ = v_a_1621_;
goto v___jp_1669_;
}
}
}
else
{
lean_object* v___x_1696_; 
lean_dec(v___x_1685_);
lean_del_object(v___x_1624_);
v___x_1696_ = lean_box(0);
v_typeAscriptionTk_x3f_1670_ = v___x_1696_;
v_type_x3f_1671_ = v___x_1696_;
v___y_1672_ = v_a_1621_;
goto v___jp_1669_;
}
v___jp_1644_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1648_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__3));
v___x_1649_ = lean_mk_empty_array_with_capacity(v___x_1638_);
lean_inc_ref(v___x_1649_);
v___x_1650_ = lean_array_push(v___x_1649_, v___x_1639_);
v___x_1651_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__5));
v___x_1652_ = lean_box(2);
v___x_1653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___x_1651_);
lean_ctor_set(v___x_1653_, 2, v___x_1650_);
v___x_1654_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__5));
v___x_1655_ = lean_unsigned_to_nat(5u);
v___x_1656_ = lean_mk_empty_array_with_capacity(v___x_1655_);
v___x_1657_ = lean_array_push(v___x_1656_, v_lbTk_1643_);
v___x_1658_ = lean_array_push(v___x_1657_, v___x_1653_);
v___x_1659_ = lean_array_push(v___x_1658_, v___y_1647_);
v___x_1660_ = lean_array_push(v___x_1659_, v___x_1654_);
v___x_1661_ = lean_array_push(v___x_1660_, v___y_1645_);
v___x_1662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1652_);
lean_ctor_set(v___x_1662_, 1, v___x_1648_);
lean_ctor_set(v___x_1662_, 2, v___x_1661_);
v___x_1663_ = lean_array_push(v___x_1649_, v___x_1662_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v___y_1646_);
return v___x_1664_;
}
v___jp_1665_:
{
lean_object* v___x_1668_; 
v___x_1668_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg___closed__5));
v___y_1645_ = v___y_1666_;
v___y_1646_ = v___y_1667_;
v___y_1647_ = v___x_1668_;
goto v___jp_1644_;
}
v___jp_1669_:
{
lean_object* v___x_1673_; lean_object* v_rbTk_1674_; 
v___x_1673_ = lean_unsigned_to_nat(3u);
v_rbTk_1674_ = l_Lean_Syntax_getArg(v___x_1631_, v___x_1673_);
lean_dec(v___x_1631_);
if (lean_obj_tag(v_typeAscriptionTk_x3f_1670_) == 1)
{
if (lean_obj_tag(v_type_x3f_1671_) == 1)
{
lean_object* v_val_1675_; lean_object* v_val_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_val_1675_ = lean_ctor_get(v_typeAscriptionTk_x3f_1670_, 0);
lean_inc(v_val_1675_);
lean_dec_ref_known(v_typeAscriptionTk_x3f_1670_, 1);
v_val_1676_ = lean_ctor_get(v_type_x3f_1671_, 0);
lean_inc(v_val_1676_);
lean_dec_ref_known(v_type_x3f_1671_, 1);
v___x_1677_ = lean_unsigned_to_nat(2u);
v___x_1678_ = lean_mk_empty_array_with_capacity(v___x_1677_);
v___x_1679_ = lean_array_push(v___x_1678_, v_val_1675_);
v___x_1680_ = lean_array_push(v___x_1679_, v_val_1676_);
v___x_1681_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__5));
v___x_1682_ = lean_box(2);
v___x_1683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v___x_1681_);
lean_ctor_set(v___x_1683_, 2, v___x_1680_);
v___y_1645_ = v_rbTk_1674_;
v___y_1646_ = v___y_1672_;
v___y_1647_ = v___x_1683_;
goto v___jp_1644_;
}
else
{
lean_dec_ref_known(v_typeAscriptionTk_x3f_1670_, 1);
lean_dec(v_type_x3f_1671_);
v___y_1666_ = v_rbTk_1674_;
v___y_1667_ = v___y_1672_;
goto v___jp_1665_;
}
}
else
{
lean_dec(v_type_x3f_1671_);
lean_dec(v_typeAscriptionTk_x3f_1670_);
v___y_1666_ = v_rbTk_1674_;
v___y_1667_ = v___y_1672_;
goto v___jp_1665_;
}
}
}
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_del_object(v___x_1624_);
v___x_1697_ = lean_unsigned_to_nat(1u);
v___x_1698_ = lean_mk_empty_array_with_capacity(v___x_1697_);
v___x_1699_ = lean_array_push(v___x_1698_, v___x_1631_);
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
lean_ctor_set(v___x_1700_, 1, v_a_1621_);
return v___x_1700_;
}
}
}
}
else
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec(v_binder_x3f_1620_);
v___x_1702_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__2));
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v_a_1621_);
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders(lean_object* v_binder_x3f_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg(v_binder_x3f_1704_, v_a_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___boxed(lean_object* v_binder_x3f_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders(v_binder_x3f_1708_, v_a_1709_, v_a_1710_);
lean_dec_ref(v_a_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithBuildDeclSig(lean_object* v_kw_1723_, lean_object* v_sig_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_Lake_Formatters_fmtWithBuildDeclSig___closed__1));
lean_inc(v_sig_1724_);
v___x_1728_ = l_Lean_Syntax_isOfKind(v_sig_1724_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_sig_1724_);
lean_dec(v_kw_1723_);
v___x_1729_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v_a_1726_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v_whereDecls_x3f_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1731_ = lean_unsigned_to_nat(0u);
v___x_1732_ = l_Lean_Syntax_getArg(v_sig_1724_, v___x_1731_);
v___x_1762_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__6));
lean_inc(v___x_1732_);
v___x_1763_ = l_Lean_Syntax_isOfKind(v___x_1732_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v___x_1732_);
lean_dec(v_sig_1724_);
lean_dec(v_kw_1723_);
v___x_1764_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
lean_ctor_set(v___x_1765_, 1, v_a_1726_);
return v___x_1765_;
}
else
{
lean_object* v___x_1766_; lean_object* v_binder_x3f_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1766_ = lean_unsigned_to_nat(1u);
v___x_1804_ = l_Lean_Syntax_getArg(v_sig_1724_, v___x_1766_);
v___x_1805_ = l_Lean_Syntax_isNone(v___x_1804_);
if (v___x_1805_ == 0)
{
uint8_t v___x_1806_; 
lean_inc(v___x_1804_);
v___x_1806_ = l_Lean_Syntax_matchesNull(v___x_1804_, v___x_1766_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v___x_1804_);
lean_dec(v___x_1732_);
lean_dec(v_sig_1724_);
lean_dec(v_kw_1723_);
v___x_1807_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v_a_1726_);
return v___x_1808_;
}
else
{
lean_object* v_binder_x3f_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v_binder_x3f_1809_ = l_Lean_Syntax_getArg(v___x_1804_, v___x_1731_);
lean_dec(v___x_1804_);
v___x_1810_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__13));
lean_inc(v_binder_x3f_1809_);
v___x_1811_ = l_Lean_Syntax_isOfKind(v_binder_x3f_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec(v_binder_x3f_1809_);
lean_dec(v___x_1732_);
lean_dec(v_sig_1724_);
lean_dec(v_kw_1723_);
v___x_1812_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v_a_1726_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v_binder_x3f_1809_);
v_binder_x3f_1768_ = v___x_1814_;
v___y_1769_ = v_a_1725_;
v___y_1770_ = v_a_1726_;
goto v___jp_1767_;
}
}
}
else
{
lean_object* v___x_1815_; 
lean_dec(v___x_1804_);
v___x_1815_ = lean_box(0);
v_binder_x3f_1768_ = v___x_1815_;
v___y_1769_ = v_a_1725_;
v___y_1770_ = v_a_1726_;
goto v___jp_1767_;
}
v___jp_1767_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1771_ = lean_unsigned_to_nat(2u);
v___x_1772_ = l_Lean_Syntax_getArg(v_sig_1724_, v___x_1771_);
v___x_1773_ = ((lean_object*)(l_Lake_Formatters_fmtWithBuildDeclSig___closed__3));
lean_inc(v___x_1772_);
v___x_1774_ = l_Lean_Syntax_isOfKind(v___x_1772_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v___x_1772_);
lean_dec(v_binder_x3f_1768_);
lean_dec(v___x_1732_);
lean_dec(v_sig_1724_);
lean_dec(v_kw_1723_);
v___x_1775_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___y_1770_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1777_ = lean_unsigned_to_nat(3u);
v___x_1778_ = l_Lean_Syntax_getArg(v_sig_1724_, v___x_1777_);
lean_dec(v_sig_1724_);
v___x_1779_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__5));
lean_inc(v___x_1778_);
v___x_1780_ = l_Lean_Syntax_isOfKind(v___x_1778_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec(v___x_1778_);
lean_dec(v___x_1772_);
lean_dec(v_binder_x3f_1768_);
lean_dec(v___x_1732_);
lean_dec(v_kw_1723_);
v___x_1781_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v___y_1770_);
return v___x_1782_;
}
else
{
lean_object* v_terminationSuffix_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_terminationSuffix_1783_ = l_Lean_Syntax_getArg(v___x_1778_, v___x_1771_);
v___x_1784_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3));
lean_inc(v_terminationSuffix_1783_);
v___x_1785_ = l_Lean_Syntax_isOfKind(v_terminationSuffix_1783_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_dec(v_terminationSuffix_1783_);
lean_dec(v___x_1778_);
lean_dec(v___x_1772_);
lean_dec(v_binder_x3f_1768_);
lean_dec(v___x_1732_);
lean_dec(v_kw_1723_);
v___x_1786_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
lean_ctor_set(v___x_1787_, 1, v___y_1770_);
return v___x_1787_;
}
else
{
lean_object* v_typeAscriptionTk_1788_; lean_object* v___x_1789_; lean_object* v_colonEqTk_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_typeAscriptionTk_1788_ = l_Lean_Syntax_getArg(v___x_1772_, v___x_1731_);
v___x_1789_ = l_Lean_Syntax_getArg(v___x_1772_, v___x_1766_);
lean_dec(v___x_1772_);
v_colonEqTk_1790_ = l_Lean_Syntax_getArg(v___x_1778_, v___x_1731_);
v___x_1791_ = l_Lean_Syntax_getArg(v___x_1778_, v___x_1766_);
v___x_1792_ = l_Lean_Syntax_getArg(v___x_1778_, v___x_1777_);
lean_dec(v___x_1778_);
v___x_1793_ = l_Lean_Syntax_isNone(v___x_1792_);
if (v___x_1793_ == 0)
{
uint8_t v___x_1794_; 
lean_inc(v___x_1792_);
v___x_1794_ = l_Lean_Syntax_matchesNull(v___x_1792_, v___x_1766_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v___x_1792_);
lean_dec(v___x_1791_);
lean_dec(v_colonEqTk_1790_);
lean_dec(v___x_1789_);
lean_dec(v_typeAscriptionTk_1788_);
lean_dec(v_terminationSuffix_1783_);
lean_dec(v_binder_x3f_1768_);
lean_dec(v___x_1732_);
lean_dec(v_kw_1723_);
v___x_1795_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v___y_1770_);
return v___x_1796_;
}
else
{
lean_object* v_whereDecls_x3f_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_whereDecls_x3f_1797_ = l_Lean_Syntax_getArg(v___x_1792_, v___x_1731_);
lean_dec(v___x_1792_);
v___x_1798_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__11));
lean_inc(v_whereDecls_x3f_1797_);
v___x_1799_ = l_Lean_Syntax_isOfKind(v_whereDecls_x3f_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v_whereDecls_x3f_1797_);
lean_dec(v___x_1791_);
lean_dec(v_colonEqTk_1790_);
lean_dec(v___x_1789_);
lean_dec(v_typeAscriptionTk_1788_);
lean_dec(v_terminationSuffix_1783_);
lean_dec(v_binder_x3f_1768_);
lean_dec(v___x_1732_);
lean_dec(v_kw_1723_);
v___x_1800_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___y_1770_);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1802_, 0, v_whereDecls_x3f_1797_);
v___y_1734_ = v_colonEqTk_1790_;
v___y_1735_ = v___x_1789_;
v___y_1736_ = v___x_1791_;
v___y_1737_ = v_binder_x3f_1768_;
v___y_1738_ = v_terminationSuffix_1783_;
v___y_1739_ = v_typeAscriptionTk_1788_;
v_whereDecls_x3f_1740_ = v___x_1802_;
v___y_1741_ = v___y_1769_;
v___y_1742_ = v___y_1770_;
goto v___jp_1733_;
}
}
}
else
{
lean_object* v___x_1803_; 
lean_dec(v___x_1792_);
v___x_1803_ = lean_box(0);
v___y_1734_ = v_colonEqTk_1790_;
v___y_1735_ = v___x_1789_;
v___y_1736_ = v___x_1791_;
v___y_1737_ = v_binder_x3f_1768_;
v___y_1738_ = v_terminationSuffix_1783_;
v___y_1739_ = v_typeAscriptionTk_1788_;
v_whereDecls_x3f_1740_ = v___x_1803_;
v___y_1741_ = v___y_1769_;
v___y_1742_ = v___y_1770_;
goto v___jp_1733_;
}
}
}
}
}
}
v___jp_1733_:
{
lean_object* v___x_1743_; 
v___x_1743_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg(v___y_1737_, v___y_1742_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v_a_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
v_a_1745_ = lean_ctor_get(v___x_1743_, 1);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___x_1743_, 2);
v___x_1746_ = lean_box(0);
v___x_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1732_);
v___x_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___y_1739_);
v___x_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___y_1735_);
v___x_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___y_1734_);
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___y_1738_);
v___x_1752_ = l_Lean_Fmt_fmtAssignmentDeclaration(v_kw_1723_, v___x_1746_, v___x_1747_, v_a_1744_, v___x_1748_, v___x_1749_, v___x_1750_, v___y_1736_, v___x_1751_, v_whereDecls_x3f_1740_, v___y_1741_, v_a_1745_);
return v___x_1752_;
}
else
{
lean_object* v_a_1753_; lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_whereDecls_x3f_1740_);
lean_dec(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec(v___x_1732_);
lean_dec(v_kw_1723_);
v_a_1753_ = lean_ctor_get(v___x_1743_, 0);
v_a_1754_ = lean_ctor_get(v___x_1743_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1743_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_inc(v_a_1753_);
lean_dec(v___x_1743_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1753_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtWithBuildDeclSig___boxed(lean_object* v_kw_1816_, lean_object* v_sig_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lake_Formatters_fmtWithBuildDeclSig(v_kw_1816_, v_sig_1817_, v_a_1818_, v_a_1819_);
lean_dec_ref(v_a_1818_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleFacetDecl(lean_object* v_x_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = ((lean_object*)(l_Lake_Formatters_fmtModuleFacetDecl___closed__1));
lean_inc(v_x_1826_);
v___x_1830_ = l_Lean_Syntax_isOfKind(v_x_1826_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v_x_1826_);
v___x_1831_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v_a_1828_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; lean_object* v___y_1835_; lean_object* v_attributes_x3f_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v_docComment_x3f_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1833_ = lean_unsigned_to_nat(0u);
v___x_1869_ = l_Lean_Syntax_getArg(v_x_1826_, v___x_1833_);
v___x_1870_ = l_Lean_Syntax_isNone(v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1869_);
v___x_1872_ = l_Lean_Syntax_matchesNull(v___x_1869_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec(v___x_1869_);
lean_dec(v_x_1826_);
v___x_1873_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v_a_1828_);
return v___x_1874_;
}
else
{
lean_object* v_docComment_x3f_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v_docComment_x3f_1875_ = l_Lean_Syntax_getArg(v___x_1869_, v___x_1833_);
lean_dec(v___x_1869_);
v___x_1876_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_1875_);
v___x_1877_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_1875_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec(v_docComment_x3f_1875_);
lean_dec(v_x_1826_);
v___x_1878_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v_a_1828_);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_docComment_x3f_1875_);
v_docComment_x3f_1853_ = v___x_1880_;
v___y_1854_ = v_a_1827_;
v___y_1855_ = v_a_1828_;
goto v___jp_1852_;
}
}
}
else
{
lean_object* v___x_1881_; 
lean_dec(v___x_1869_);
v___x_1881_ = lean_box(0);
v_docComment_x3f_1853_ = v___x_1881_;
v___y_1854_ = v_a_1827_;
v___y_1855_ = v_a_1828_;
goto v___jp_1852_;
}
v___jp_1834_:
{
lean_object* v___x_1839_; lean_object* v_sig_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1839_ = lean_unsigned_to_nat(3u);
v_sig_1840_ = l_Lean_Syntax_getArg(v_x_1826_, v___x_1839_);
v___x_1841_ = ((lean_object*)(l_Lake_Formatters_fmtWithBuildDeclSig___closed__1));
lean_inc(v_sig_1840_);
v___x_1842_ = l_Lean_Syntax_isOfKind(v_sig_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec(v_sig_1840_);
lean_dec(v_attributes_x3f_1836_);
lean_dec(v___y_1835_);
lean_dec(v_x_1826_);
v___x_1843_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v___y_1838_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; lean_object* v_moduleFacetTk_1846_; lean_object* v___x_1847_; 
v___x_1845_ = lean_unsigned_to_nat(2u);
v_moduleFacetTk_1846_ = l_Lean_Syntax_getArg(v_x_1826_, v___x_1845_);
lean_dec(v_x_1826_);
v___x_1847_ = l_Lake_Formatters_fmtWithBuildDeclSig(v_moduleFacetTk_1846_, v_sig_1840_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
v_a_1849_ = lean_ctor_get(v___x_1847_, 1);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1847_, 2);
v___x_1850_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_1851_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_1835_, v_attributes_x3f_1836_, v___x_1850_, v_a_1848_, v___y_1837_, v_a_1849_);
return v___x_1851_;
}
else
{
lean_dec(v_attributes_x3f_1836_);
lean_dec(v___y_1835_);
return v___x_1847_;
}
}
}
v___jp_1852_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1856_ = lean_unsigned_to_nat(1u);
v___x_1857_ = l_Lean_Syntax_getArg(v_x_1826_, v___x_1856_);
v___x_1858_ = l_Lean_Syntax_isNone(v___x_1857_);
if (v___x_1858_ == 0)
{
uint8_t v___x_1859_; 
lean_inc(v___x_1857_);
v___x_1859_ = l_Lean_Syntax_matchesNull(v___x_1857_, v___x_1856_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec(v___x_1857_);
lean_dec(v_docComment_x3f_1853_);
lean_dec(v_x_1826_);
v___x_1860_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v___y_1855_);
return v___x_1861_;
}
else
{
lean_object* v_attributes_x3f_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v_attributes_x3f_1862_ = l_Lean_Syntax_getArg(v___x_1857_, v___x_1833_);
lean_dec(v___x_1857_);
v___x_1863_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_1862_);
v___x_1864_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_1862_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_dec(v_attributes_x3f_1862_);
lean_dec(v_docComment_x3f_1853_);
lean_dec(v_x_1826_);
v___x_1865_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
lean_ctor_set(v___x_1866_, 1, v___y_1855_);
return v___x_1866_;
}
else
{
lean_object* v___x_1867_; 
v___x_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_attributes_x3f_1862_);
v___y_1835_ = v_docComment_x3f_1853_;
v_attributes_x3f_1836_ = v___x_1867_;
v___y_1837_ = v___y_1854_;
v___y_1838_ = v___y_1855_;
goto v___jp_1834_;
}
}
}
else
{
lean_object* v___x_1868_; 
lean_dec(v___x_1857_);
v___x_1868_ = lean_box(0);
v___y_1835_ = v_docComment_x3f_1853_;
v_attributes_x3f_1836_ = v___x_1868_;
v___y_1837_ = v___y_1854_;
v___y_1838_ = v___y_1855_;
goto v___jp_1834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleFacetDecl___boxed(lean_object* v_x_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lake_Formatters_fmtModuleFacetDecl(v_x_1882_, v_a_1883_, v_a_1884_);
lean_dec_ref(v_a_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1(){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1892_ = l_Lean_Fmt_fmtAttribute;
v___x_1893_ = ((lean_object*)(l_Lake_Formatters_fmtModuleFacetDecl___closed__1));
v___x_1894_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___closed__1));
v___x_1895_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtModuleFacetDecl___boxed), 3, 0);
v___x_1896_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1892_, v___x_1893_, v___x_1894_, v___x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1___boxed(lean_object* v_a_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1();
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageFacetDecl(lean_object* v_x_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = ((lean_object*)(l_Lake_Formatters_fmtPackageFacetDecl___closed__1));
lean_inc(v_x_1904_);
v___x_1908_ = l_Lean_Syntax_isOfKind(v_x_1904_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
lean_dec(v_x_1904_);
v___x_1909_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v_a_1906_);
return v___x_1910_;
}
else
{
lean_object* v___x_1911_; lean_object* v___y_1913_; lean_object* v_attributes_x3f_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v_docComment_x3f_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1911_ = lean_unsigned_to_nat(0u);
v___x_1947_ = l_Lean_Syntax_getArg(v_x_1904_, v___x_1911_);
v___x_1948_ = l_Lean_Syntax_isNone(v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1947_);
v___x_1950_ = l_Lean_Syntax_matchesNull(v___x_1947_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec(v___x_1947_);
lean_dec(v_x_1904_);
v___x_1951_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v_a_1906_);
return v___x_1952_;
}
else
{
lean_object* v_docComment_x3f_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v_docComment_x3f_1953_ = l_Lean_Syntax_getArg(v___x_1947_, v___x_1911_);
lean_dec(v___x_1947_);
v___x_1954_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_1953_);
v___x_1955_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_1953_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_dec(v_docComment_x3f_1953_);
lean_dec(v_x_1904_);
v___x_1956_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
lean_ctor_set(v___x_1957_, 1, v_a_1906_);
return v___x_1957_;
}
else
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_docComment_x3f_1953_);
v_docComment_x3f_1931_ = v___x_1958_;
v___y_1932_ = v_a_1905_;
v___y_1933_ = v_a_1906_;
goto v___jp_1930_;
}
}
}
else
{
lean_object* v___x_1959_; 
lean_dec(v___x_1947_);
v___x_1959_ = lean_box(0);
v_docComment_x3f_1931_ = v___x_1959_;
v___y_1932_ = v_a_1905_;
v___y_1933_ = v_a_1906_;
goto v___jp_1930_;
}
v___jp_1912_:
{
lean_object* v___x_1917_; lean_object* v_sig_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1917_ = lean_unsigned_to_nat(3u);
v_sig_1918_ = l_Lean_Syntax_getArg(v_x_1904_, v___x_1917_);
v___x_1919_ = ((lean_object*)(l_Lake_Formatters_fmtWithBuildDeclSig___closed__1));
lean_inc(v_sig_1918_);
v___x_1920_ = l_Lean_Syntax_isOfKind(v_sig_1918_, v___x_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
lean_dec(v_sig_1918_);
lean_dec(v_attributes_x3f_1914_);
lean_dec(v___y_1913_);
lean_dec(v_x_1904_);
v___x_1921_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v___y_1916_);
return v___x_1922_;
}
else
{
lean_object* v___x_1923_; lean_object* v_packageFacetTk_1924_; lean_object* v___x_1925_; 
v___x_1923_ = lean_unsigned_to_nat(2u);
v_packageFacetTk_1924_ = l_Lean_Syntax_getArg(v_x_1904_, v___x_1923_);
lean_dec(v_x_1904_);
v___x_1925_ = l_Lake_Formatters_fmtWithBuildDeclSig(v_packageFacetTk_1924_, v_sig_1918_, v___y_1915_, v___y_1916_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v_a_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
v_a_1927_ = lean_ctor_get(v___x_1925_, 1);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1925_, 2);
v___x_1928_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_1929_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_1913_, v_attributes_x3f_1914_, v___x_1928_, v_a_1926_, v___y_1915_, v_a_1927_);
return v___x_1929_;
}
else
{
lean_dec(v_attributes_x3f_1914_);
lean_dec(v___y_1913_);
return v___x_1925_;
}
}
}
v___jp_1930_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = l_Lean_Syntax_getArg(v_x_1904_, v___x_1934_);
v___x_1936_ = l_Lean_Syntax_isNone(v___x_1935_);
if (v___x_1936_ == 0)
{
uint8_t v___x_1937_; 
lean_inc(v___x_1935_);
v___x_1937_ = l_Lean_Syntax_matchesNull(v___x_1935_, v___x_1934_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_dec(v___x_1935_);
lean_dec(v_docComment_x3f_1931_);
lean_dec(v_x_1904_);
v___x_1938_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___y_1933_);
return v___x_1939_;
}
else
{
lean_object* v_attributes_x3f_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v_attributes_x3f_1940_ = l_Lean_Syntax_getArg(v___x_1935_, v___x_1911_);
lean_dec(v___x_1935_);
v___x_1941_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_1940_);
v___x_1942_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_1940_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec(v_attributes_x3f_1940_);
lean_dec(v_docComment_x3f_1931_);
lean_dec(v_x_1904_);
v___x_1943_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v___y_1933_);
return v___x_1944_;
}
else
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1945_, 0, v_attributes_x3f_1940_);
v___y_1913_ = v_docComment_x3f_1931_;
v_attributes_x3f_1914_ = v___x_1945_;
v___y_1915_ = v___y_1932_;
v___y_1916_ = v___y_1933_;
goto v___jp_1912_;
}
}
}
else
{
lean_object* v___x_1946_; 
lean_dec(v___x_1935_);
v___x_1946_ = lean_box(0);
v___y_1913_ = v_docComment_x3f_1931_;
v_attributes_x3f_1914_ = v___x_1946_;
v___y_1915_ = v___y_1932_;
v___y_1916_ = v___y_1933_;
goto v___jp_1912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageFacetDecl___boxed(lean_object* v_x_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lake_Formatters_fmtPackageFacetDecl(v_x_1960_, v_a_1961_, v_a_1962_);
lean_dec_ref(v_a_1961_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1(){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1970_ = l_Lean_Fmt_fmtAttribute;
v___x_1971_ = ((lean_object*)(l_Lake_Formatters_fmtPackageFacetDecl___closed__1));
v___x_1972_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___closed__1));
v___x_1973_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtPackageFacetDecl___boxed), 3, 0);
v___x_1974_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1970_, v___x_1971_, v___x_1972_, v___x_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1___boxed(lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1();
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLibraryFacetDecl(lean_object* v_x_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = ((lean_object*)(l_Lake_Formatters_fmtLibraryFacetDecl___closed__1));
lean_inc(v_x_1982_);
v___x_1986_ = l_Lean_Syntax_isOfKind(v_x_1982_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_dec(v_x_1982_);
v___x_1987_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
lean_ctor_set(v___x_1988_, 1, v_a_1984_);
return v___x_1988_;
}
else
{
lean_object* v___x_1989_; lean_object* v___y_1991_; lean_object* v_attributes_x3f_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v_docComment_x3f_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_2025_ = l_Lean_Syntax_getArg(v_x_1982_, v___x_1989_);
v___x_2026_ = l_Lean_Syntax_isNone(v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2025_);
v___x_2028_ = l_Lean_Syntax_matchesNull(v___x_2025_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec(v___x_2025_);
lean_dec(v_x_1982_);
v___x_2029_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v_a_1984_);
return v___x_2030_;
}
else
{
lean_object* v_docComment_x3f_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_docComment_x3f_2031_ = l_Lean_Syntax_getArg(v___x_2025_, v___x_1989_);
lean_dec(v___x_2025_);
v___x_2032_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_2031_);
v___x_2033_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec(v_docComment_x3f_2031_);
lean_dec(v_x_1982_);
v___x_2034_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
lean_ctor_set(v___x_2035_, 1, v_a_1984_);
return v___x_2035_;
}
else
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_docComment_x3f_2031_);
v_docComment_x3f_2009_ = v___x_2036_;
v___y_2010_ = v_a_1983_;
v___y_2011_ = v_a_1984_;
goto v___jp_2008_;
}
}
}
else
{
lean_object* v___x_2037_; 
lean_dec(v___x_2025_);
v___x_2037_ = lean_box(0);
v_docComment_x3f_2009_ = v___x_2037_;
v___y_2010_ = v_a_1983_;
v___y_2011_ = v_a_1984_;
goto v___jp_2008_;
}
v___jp_1990_:
{
lean_object* v___x_1995_; lean_object* v_sig_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1995_ = lean_unsigned_to_nat(3u);
v_sig_1996_ = l_Lean_Syntax_getArg(v_x_1982_, v___x_1995_);
v___x_1997_ = ((lean_object*)(l_Lake_Formatters_fmtWithBuildDeclSig___closed__1));
lean_inc(v_sig_1996_);
v___x_1998_ = l_Lean_Syntax_isOfKind(v_sig_1996_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_dec(v_sig_1996_);
lean_dec(v_attributes_x3f_1992_);
lean_dec(v___y_1991_);
lean_dec(v_x_1982_);
v___x_1999_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set(v___x_2000_, 1, v___y_1994_);
return v___x_2000_;
}
else
{
lean_object* v___x_2001_; lean_object* v_libraryFacetTk_2002_; lean_object* v___x_2003_; 
v___x_2001_ = lean_unsigned_to_nat(2u);
v_libraryFacetTk_2002_ = l_Lean_Syntax_getArg(v_x_1982_, v___x_2001_);
lean_dec(v_x_1982_);
v___x_2003_ = l_Lake_Formatters_fmtWithBuildDeclSig(v_libraryFacetTk_2002_, v_sig_1996_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v_a_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
v_a_2005_ = lean_ctor_get(v___x_2003_, 1);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2003_, 2);
v___x_2006_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_2007_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_1991_, v_attributes_x3f_1992_, v___x_2006_, v_a_2004_, v___y_1993_, v_a_2005_);
return v___x_2007_;
}
else
{
lean_dec(v_attributes_x3f_1992_);
lean_dec(v___y_1991_);
return v___x_2003_;
}
}
}
v___jp_2008_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = l_Lean_Syntax_getArg(v_x_1982_, v___x_2012_);
v___x_2014_ = l_Lean_Syntax_isNone(v___x_2013_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; 
lean_inc(v___x_2013_);
v___x_2015_ = l_Lean_Syntax_matchesNull(v___x_2013_, v___x_2012_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_dec(v___x_2013_);
lean_dec(v_docComment_x3f_2009_);
lean_dec(v_x_1982_);
v___x_2016_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v___y_2011_);
return v___x_2017_;
}
else
{
lean_object* v_attributes_x3f_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_attributes_x3f_2018_ = l_Lean_Syntax_getArg(v___x_2013_, v___x_1989_);
lean_dec(v___x_2013_);
v___x_2019_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_2018_);
v___x_2020_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec(v_attributes_x3f_2018_);
lean_dec(v_docComment_x3f_2009_);
lean_dec(v_x_1982_);
v___x_2021_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
lean_ctor_set(v___x_2022_, 1, v___y_2011_);
return v___x_2022_;
}
else
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2023_, 0, v_attributes_x3f_2018_);
v___y_1991_ = v_docComment_x3f_2009_;
v_attributes_x3f_1992_ = v___x_2023_;
v___y_1993_ = v___y_2010_;
v___y_1994_ = v___y_2011_;
goto v___jp_1990_;
}
}
}
else
{
lean_object* v___x_2024_; 
lean_dec(v___x_2013_);
v___x_2024_ = lean_box(0);
v___y_1991_ = v_docComment_x3f_2009_;
v_attributes_x3f_1992_ = v___x_2024_;
v___y_1993_ = v___y_2010_;
v___y_1994_ = v___y_2011_;
goto v___jp_1990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtLibraryFacetDecl___boxed(lean_object* v_x_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lake_Formatters_fmtLibraryFacetDecl(v_x_2038_, v_a_2039_, v_a_2040_);
lean_dec_ref(v_a_2039_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1(){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2048_ = l_Lean_Fmt_fmtAttribute;
v___x_2049_ = ((lean_object*)(l_Lake_Formatters_fmtLibraryFacetDecl___closed__1));
v___x_2050_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___closed__1));
v___x_2051_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtLibraryFacetDecl___boxed), 3, 0);
v___x_2052_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2048_, v___x_2049_, v___x_2050_, v___x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1___boxed(lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1();
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtTargetCommand(lean_object* v_x_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = ((lean_object*)(l_Lake_Formatters_fmtTargetCommand___closed__1));
lean_inc(v_x_2060_);
v___x_2064_ = l_Lean_Syntax_isOfKind(v_x_2060_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec(v_x_2060_);
v___x_2065_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v_a_2062_);
return v___x_2066_;
}
else
{
lean_object* v___x_2067_; lean_object* v___y_2069_; lean_object* v_attributes_x3f_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v_docComment_x3f_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2103_ = l_Lean_Syntax_getArg(v_x_2060_, v___x_2067_);
v___x_2104_ = l_Lean_Syntax_isNone(v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2103_);
v___x_2106_ = l_Lean_Syntax_matchesNull(v___x_2103_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec(v___x_2103_);
lean_dec(v_x_2060_);
v___x_2107_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v_a_2062_);
return v___x_2108_;
}
else
{
lean_object* v_docComment_x3f_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v_docComment_x3f_2109_ = l_Lean_Syntax_getArg(v___x_2103_, v___x_2067_);
lean_dec(v___x_2103_);
v___x_2110_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_2109_);
v___x_2111_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_2109_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v_docComment_x3f_2109_);
lean_dec(v_x_2060_);
v___x_2112_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v_a_2062_);
return v___x_2113_;
}
else
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_docComment_x3f_2109_);
v_docComment_x3f_2087_ = v___x_2114_;
v___y_2088_ = v_a_2061_;
v___y_2089_ = v_a_2062_;
goto v___jp_2086_;
}
}
}
else
{
lean_object* v___x_2115_; 
lean_dec(v___x_2103_);
v___x_2115_ = lean_box(0);
v_docComment_x3f_2087_ = v___x_2115_;
v___y_2088_ = v_a_2061_;
v___y_2089_ = v_a_2062_;
goto v___jp_2086_;
}
v___jp_2068_:
{
lean_object* v___x_2073_; lean_object* v_sig_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2073_ = lean_unsigned_to_nat(3u);
v_sig_2074_ = l_Lean_Syntax_getArg(v_x_2060_, v___x_2073_);
v___x_2075_ = ((lean_object*)(l_Lake_Formatters_fmtWithBuildDeclSig___closed__1));
lean_inc(v_sig_2074_);
v___x_2076_ = l_Lean_Syntax_isOfKind(v_sig_2074_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec(v_sig_2074_);
lean_dec(v_attributes_x3f_2070_);
lean_dec(v___y_2069_);
lean_dec(v_x_2060_);
v___x_2077_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___y_2072_);
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; lean_object* v_targetTk_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_unsigned_to_nat(2u);
v_targetTk_2080_ = l_Lean_Syntax_getArg(v_x_2060_, v___x_2079_);
lean_dec(v_x_2060_);
v___x_2081_ = l_Lake_Formatters_fmtWithBuildDeclSig(v_targetTk_2080_, v_sig_2074_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v_a_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
v_a_2083_ = lean_ctor_get(v___x_2081_, 1);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2081_, 2);
v___x_2084_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_2085_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_2069_, v_attributes_x3f_2070_, v___x_2084_, v_a_2082_, v___y_2071_, v_a_2083_);
return v___x_2085_;
}
else
{
lean_dec(v_attributes_x3f_2070_);
lean_dec(v___y_2069_);
return v___x_2081_;
}
}
}
v___jp_2086_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2090_ = lean_unsigned_to_nat(1u);
v___x_2091_ = l_Lean_Syntax_getArg(v_x_2060_, v___x_2090_);
v___x_2092_ = l_Lean_Syntax_isNone(v___x_2091_);
if (v___x_2092_ == 0)
{
uint8_t v___x_2093_; 
lean_inc(v___x_2091_);
v___x_2093_ = l_Lean_Syntax_matchesNull(v___x_2091_, v___x_2090_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec(v___x_2091_);
lean_dec(v_docComment_x3f_2087_);
lean_dec(v_x_2060_);
v___x_2094_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v___y_2089_);
return v___x_2095_;
}
else
{
lean_object* v_attributes_x3f_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_attributes_x3f_2096_ = l_Lean_Syntax_getArg(v___x_2091_, v___x_2067_);
lean_dec(v___x_2091_);
v___x_2097_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_2096_);
v___x_2098_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_2096_, v___x_2097_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec(v_attributes_x3f_2096_);
lean_dec(v_docComment_x3f_2087_);
lean_dec(v_x_2060_);
v___x_2099_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v___y_2089_);
return v___x_2100_;
}
else
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v_attributes_x3f_2096_);
v___y_2069_ = v_docComment_x3f_2087_;
v_attributes_x3f_2070_ = v___x_2101_;
v___y_2071_ = v___y_2088_;
v___y_2072_ = v___y_2089_;
goto v___jp_2068_;
}
}
}
else
{
lean_object* v___x_2102_; 
lean_dec(v___x_2091_);
v___x_2102_ = lean_box(0);
v___y_2069_ = v_docComment_x3f_2087_;
v_attributes_x3f_2070_ = v___x_2102_;
v___y_2071_ = v___y_2088_;
v___y_2072_ = v___y_2089_;
goto v___jp_2068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtTargetCommand___boxed(lean_object* v_x_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lake_Formatters_fmtTargetCommand(v_x_2116_, v_a_2117_, v_a_2118_);
lean_dec_ref(v_a_2117_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1(){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2126_ = l_Lean_Fmt_fmtAttribute;
v___x_2127_ = ((lean_object*)(l_Lake_Formatters_fmtTargetCommand___closed__1));
v___x_2128_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___closed__1));
v___x_2129_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtTargetCommand___boxed), 3, 0);
v___x_2130_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2126_, v___x_2127_, v___x_2128_, v___x_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1___boxed(lean_object* v_a_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1();
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtExternLibCommand(lean_object* v_x_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = ((lean_object*)(l_Lake_Formatters_fmtExternLibCommand___closed__1));
lean_inc(v_x_2143_);
v___x_2147_ = l_Lean_Syntax_isOfKind(v_x_2143_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec(v_x_2143_);
v___x_2148_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
lean_ctor_set(v___x_2149_, 1, v_a_2145_);
return v___x_2149_;
}
else
{
lean_object* v___x_2150_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v_whereDecls_x3f_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v_binder_x3f_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v_attributes_x3f_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v_docComment_x3f_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2150_ = lean_unsigned_to_nat(0u);
v___x_2268_ = l_Lean_Syntax_getArg(v_x_2143_, v___x_2150_);
v___x_2269_ = l_Lean_Syntax_isNone(v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2270_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2268_);
v___x_2271_ = l_Lean_Syntax_matchesNull(v___x_2268_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec(v___x_2268_);
lean_dec(v_x_2143_);
v___x_2272_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v_a_2145_);
return v___x_2273_;
}
else
{
lean_object* v_docComment_x3f_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v_docComment_x3f_2274_ = l_Lean_Syntax_getArg(v___x_2268_, v___x_2150_);
lean_dec(v___x_2268_);
v___x_2275_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_2274_);
v___x_2276_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_dec(v_docComment_x3f_2274_);
lean_dec(v_x_2143_);
v___x_2277_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v_a_2145_);
return v___x_2278_;
}
else
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_docComment_x3f_2274_);
v_docComment_x3f_2252_ = v___x_2279_;
v___y_2253_ = v_a_2144_;
v___y_2254_ = v_a_2145_;
goto v___jp_2251_;
}
}
}
else
{
lean_object* v___x_2280_; 
lean_dec(v___x_2268_);
v___x_2280_ = lean_box(0);
v_docComment_x3f_2252_ = v___x_2280_;
v___y_2253_ = v_a_2144_;
v___y_2254_ = v_a_2145_;
goto v___jp_2251_;
}
v___jp_2151_:
{
lean_object* v___x_2163_; 
v___x_2163_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg(v___y_2155_, v___y_2162_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v_a_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
v_a_2165_ = lean_ctor_get(v___x_2163_, 1);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2163_, 2);
v___x_2166_ = lean_box(0);
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___y_2153_);
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___y_2157_);
v___x_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___y_2154_);
v___x_2170_ = l_Lean_Fmt_fmtAssignmentDeclaration(v___y_2156_, v___x_2166_, v___x_2167_, v_a_2164_, v___x_2166_, v___x_2166_, v___x_2168_, v___y_2152_, v___x_2169_, v_whereDecls_x3f_2160_, v___y_2161_, v_a_2165_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v_a_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
v_a_2172_ = lean_ctor_get(v___x_2170_, 1);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2170_, 2);
v___x_2173_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_2174_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_2158_, v___y_2159_, v___x_2173_, v_a_2171_, v___y_2161_, v_a_2172_);
return v___x_2174_;
}
else
{
lean_dec(v___y_2159_);
lean_dec(v___y_2158_);
return v___x_2170_;
}
}
else
{
lean_object* v_a_2175_; lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_whereDecls_x3f_2160_);
lean_dec(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec(v___y_2152_);
v_a_2175_ = lean_ctor_get(v___x_2163_, 0);
v_a_2176_ = lean_ctor_get(v___x_2163_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2163_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_inc(v_a_2175_);
lean_dec(v___x_2163_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2175_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
v___jp_2184_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2196_ = l_Lean_Syntax_getArg(v___y_2189_, v___y_2191_);
lean_dec(v___y_2189_);
v___x_2197_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__5));
lean_inc(v___x_2196_);
v___x_2198_ = l_Lean_Syntax_isOfKind(v___x_2196_, v___x_2197_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec(v___x_2196_);
lean_dec(v_binder_x3f_2193_);
lean_dec(v___y_2192_);
lean_dec(v___y_2190_);
lean_dec(v___y_2187_);
lean_dec(v___y_2185_);
v___x_2199_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v___y_2195_);
return v___x_2200_;
}
else
{
lean_object* v_terminationSuffix_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v_terminationSuffix_2201_ = l_Lean_Syntax_getArg(v___x_2196_, v___y_2191_);
v___x_2202_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3));
lean_inc(v_terminationSuffix_2201_);
v___x_2203_ = l_Lean_Syntax_isOfKind(v_terminationSuffix_2201_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec(v_terminationSuffix_2201_);
lean_dec(v___x_2196_);
lean_dec(v_binder_x3f_2193_);
lean_dec(v___y_2192_);
lean_dec(v___y_2190_);
lean_dec(v___y_2187_);
lean_dec(v___y_2185_);
v___x_2204_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v___y_2195_);
return v___x_2205_;
}
else
{
lean_object* v_colonEqTk_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v_colonEqTk_2206_ = l_Lean_Syntax_getArg(v___x_2196_, v___x_2150_);
v___x_2207_ = l_Lean_Syntax_getArg(v___x_2196_, v___y_2186_);
v___x_2208_ = l_Lean_Syntax_getArg(v___x_2196_, v___y_2188_);
lean_dec(v___x_2196_);
v___x_2209_ = l_Lean_Syntax_isNone(v___x_2208_);
if (v___x_2209_ == 0)
{
uint8_t v___x_2210_; 
lean_inc(v___x_2208_);
v___x_2210_ = l_Lean_Syntax_matchesNull(v___x_2208_, v___y_2186_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_dec(v___x_2208_);
lean_dec(v___x_2207_);
lean_dec(v_colonEqTk_2206_);
lean_dec(v_terminationSuffix_2201_);
lean_dec(v_binder_x3f_2193_);
lean_dec(v___y_2192_);
lean_dec(v___y_2190_);
lean_dec(v___y_2187_);
lean_dec(v___y_2185_);
v___x_2211_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v___y_2195_);
return v___x_2212_;
}
else
{
lean_object* v_whereDecls_x3f_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v_whereDecls_x3f_2213_ = l_Lean_Syntax_getArg(v___x_2208_, v___x_2150_);
lean_dec(v___x_2208_);
v___x_2214_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__11));
lean_inc(v_whereDecls_x3f_2213_);
v___x_2215_ = l_Lean_Syntax_isOfKind(v_whereDecls_x3f_2213_, v___x_2214_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec(v_whereDecls_x3f_2213_);
lean_dec(v___x_2207_);
lean_dec(v_colonEqTk_2206_);
lean_dec(v_terminationSuffix_2201_);
lean_dec(v_binder_x3f_2193_);
lean_dec(v___y_2192_);
lean_dec(v___y_2190_);
lean_dec(v___y_2187_);
lean_dec(v___y_2185_);
v___x_2216_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v___y_2195_);
return v___x_2217_;
}
else
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2218_, 0, v_whereDecls_x3f_2213_);
v___y_2152_ = v___x_2207_;
v___y_2153_ = v___y_2185_;
v___y_2154_ = v_terminationSuffix_2201_;
v___y_2155_ = v_binder_x3f_2193_;
v___y_2156_ = v___y_2187_;
v___y_2157_ = v_colonEqTk_2206_;
v___y_2158_ = v___y_2190_;
v___y_2159_ = v___y_2192_;
v_whereDecls_x3f_2160_ = v___x_2218_;
v___y_2161_ = v___y_2194_;
v___y_2162_ = v___y_2195_;
goto v___jp_2151_;
}
}
}
else
{
lean_object* v___x_2219_; 
lean_dec(v___x_2208_);
v___x_2219_ = lean_box(0);
v___y_2152_ = v___x_2207_;
v___y_2153_ = v___y_2185_;
v___y_2154_ = v_terminationSuffix_2201_;
v___y_2155_ = v_binder_x3f_2193_;
v___y_2156_ = v___y_2187_;
v___y_2157_ = v_colonEqTk_2206_;
v___y_2158_ = v___y_2190_;
v___y_2159_ = v___y_2192_;
v_whereDecls_x3f_2160_ = v___x_2219_;
v___y_2161_ = v___y_2194_;
v___y_2162_ = v___y_2195_;
goto v___jp_2151_;
}
}
}
}
v___jp_2220_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2226_ = lean_unsigned_to_nat(3u);
v___x_2227_ = l_Lean_Syntax_getArg(v_x_2143_, v___x_2226_);
v___x_2228_ = ((lean_object*)(l_Lake_Formatters_fmtExternLibCommand___closed__3));
lean_inc(v___x_2227_);
v___x_2229_ = l_Lean_Syntax_isOfKind(v___x_2227_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v___x_2227_);
lean_dec(v_attributes_x3f_2223_);
lean_dec(v___y_2222_);
lean_dec(v_x_2143_);
v___x_2230_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v___y_2225_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2232_ = l_Lean_Syntax_getArg(v___x_2227_, v___x_2150_);
v___x_2233_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__6));
lean_inc(v___x_2232_);
v___x_2234_ = l_Lean_Syntax_isOfKind(v___x_2232_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_dec(v___x_2232_);
lean_dec(v___x_2227_);
lean_dec(v_attributes_x3f_2223_);
lean_dec(v___y_2222_);
lean_dec(v_x_2143_);
v___x_2235_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set(v___x_2236_, 1, v___y_2225_);
return v___x_2236_;
}
else
{
lean_object* v___x_2237_; lean_object* v_externLibTk_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2237_ = lean_unsigned_to_nat(2u);
v_externLibTk_2238_ = l_Lean_Syntax_getArg(v_x_2143_, v___x_2237_);
lean_dec(v_x_2143_);
v___x_2239_ = l_Lean_Syntax_getArg(v___x_2227_, v___y_2221_);
v___x_2240_ = l_Lean_Syntax_isNone(v___x_2239_);
if (v___x_2240_ == 0)
{
uint8_t v___x_2241_; 
lean_inc(v___x_2239_);
v___x_2241_ = l_Lean_Syntax_matchesNull(v___x_2239_, v___y_2221_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_dec(v___x_2239_);
lean_dec(v_externLibTk_2238_);
lean_dec(v___x_2232_);
lean_dec(v___x_2227_);
lean_dec(v_attributes_x3f_2223_);
lean_dec(v___y_2222_);
v___x_2242_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v___y_2225_);
return v___x_2243_;
}
else
{
lean_object* v_binder_x3f_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v_binder_x3f_2244_ = l_Lean_Syntax_getArg(v___x_2239_, v___x_2150_);
lean_dec(v___x_2239_);
v___x_2245_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__13));
lean_inc(v_binder_x3f_2244_);
v___x_2246_ = l_Lean_Syntax_isOfKind(v_binder_x3f_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec(v_binder_x3f_2244_);
lean_dec(v_externLibTk_2238_);
lean_dec(v___x_2232_);
lean_dec(v___x_2227_);
lean_dec(v_attributes_x3f_2223_);
lean_dec(v___y_2222_);
v___x_2247_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v___y_2225_);
return v___x_2248_;
}
else
{
lean_object* v___x_2249_; 
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_binder_x3f_2244_);
v___y_2185_ = v___x_2232_;
v___y_2186_ = v___y_2221_;
v___y_2187_ = v_externLibTk_2238_;
v___y_2188_ = v___x_2226_;
v___y_2189_ = v___x_2227_;
v___y_2190_ = v___y_2222_;
v___y_2191_ = v___x_2237_;
v___y_2192_ = v_attributes_x3f_2223_;
v_binder_x3f_2193_ = v___x_2249_;
v___y_2194_ = v___y_2224_;
v___y_2195_ = v___y_2225_;
goto v___jp_2184_;
}
}
}
else
{
lean_object* v___x_2250_; 
lean_dec(v___x_2239_);
v___x_2250_ = lean_box(0);
v___y_2185_ = v___x_2232_;
v___y_2186_ = v___y_2221_;
v___y_2187_ = v_externLibTk_2238_;
v___y_2188_ = v___x_2226_;
v___y_2189_ = v___x_2227_;
v___y_2190_ = v___y_2222_;
v___y_2191_ = v___x_2237_;
v___y_2192_ = v_attributes_x3f_2223_;
v_binder_x3f_2193_ = v___x_2250_;
v___y_2194_ = v___y_2224_;
v___y_2195_ = v___y_2225_;
goto v___jp_2184_;
}
}
}
}
v___jp_2251_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2255_ = lean_unsigned_to_nat(1u);
v___x_2256_ = l_Lean_Syntax_getArg(v_x_2143_, v___x_2255_);
v___x_2257_ = l_Lean_Syntax_isNone(v___x_2256_);
if (v___x_2257_ == 0)
{
uint8_t v___x_2258_; 
lean_inc(v___x_2256_);
v___x_2258_ = l_Lean_Syntax_matchesNull(v___x_2256_, v___x_2255_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_dec(v___x_2256_);
lean_dec(v_docComment_x3f_2252_);
lean_dec(v_x_2143_);
v___x_2259_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
lean_ctor_set(v___x_2260_, 1, v___y_2254_);
return v___x_2260_;
}
else
{
lean_object* v_attributes_x3f_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_attributes_x3f_2261_ = l_Lean_Syntax_getArg(v___x_2256_, v___x_2150_);
lean_dec(v___x_2256_);
v___x_2262_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_2261_);
v___x_2263_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_dec(v_attributes_x3f_2261_);
lean_dec(v_docComment_x3f_2252_);
lean_dec(v_x_2143_);
v___x_2264_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v___y_2254_);
return v___x_2265_;
}
else
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2266_, 0, v_attributes_x3f_2261_);
v___y_2221_ = v___x_2255_;
v___y_2222_ = v_docComment_x3f_2252_;
v_attributes_x3f_2223_ = v___x_2266_;
v___y_2224_ = v___y_2253_;
v___y_2225_ = v___y_2254_;
goto v___jp_2220_;
}
}
}
else
{
lean_object* v___x_2267_; 
lean_dec(v___x_2256_);
v___x_2267_ = lean_box(0);
v___y_2221_ = v___x_2255_;
v___y_2222_ = v_docComment_x3f_2252_;
v_attributes_x3f_2223_ = v___x_2267_;
v___y_2224_ = v___y_2253_;
v___y_2225_ = v___y_2254_;
goto v___jp_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtExternLibCommand___boxed(lean_object* v_x_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lake_Formatters_fmtExternLibCommand(v_x_2281_, v_a_2282_, v_a_2283_);
lean_dec_ref(v_a_2282_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1(){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2291_ = l_Lean_Fmt_fmtAttribute;
v___x_2292_ = ((lean_object*)(l_Lake_Formatters_fmtExternLibCommand___closed__1));
v___x_2293_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___closed__1));
v___x_2294_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtExternLibCommand___boxed), 3, 0);
v___x_2295_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2291_, v___x_2292_, v___x_2293_, v___x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1___boxed(lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1();
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtCacheServiceCommand(lean_object* v_x_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = ((lean_object*)(l_Lake_Formatters_fmtCacheServiceCommand___closed__1));
lean_inc(v_x_2333_);
v___x_2337_ = l_Lean_Syntax_isOfKind(v_x_2333_, v___x_2336_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_dec(v_x_2333_);
v___x_2338_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
lean_ctor_set(v___x_2339_, 1, v_a_2335_);
return v___x_2339_;
}
else
{
lean_object* v___x_2340_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v_whereDecls_x3f_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v_whereDecls_x3f_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v_whereDecls_x3f_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v_name_x3f_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v_attributes_x3f_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v_docComment_x3f_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v___x_2340_ = lean_unsigned_to_nat(0u);
v___x_2575_ = l_Lean_Syntax_getArg(v_x_2333_, v___x_2340_);
v___x_2576_ = l_Lean_Syntax_isNone(v___x_2575_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2577_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2575_);
v___x_2578_ = l_Lean_Syntax_matchesNull(v___x_2575_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec(v___x_2575_);
lean_dec(v_x_2333_);
v___x_2579_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v_a_2335_);
return v___x_2580_;
}
else
{
lean_object* v_docComment_x3f_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v_docComment_x3f_2581_ = l_Lean_Syntax_getArg(v___x_2575_, v___x_2340_);
lean_dec(v___x_2575_);
v___x_2582_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_2581_);
v___x_2583_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_2581_, v___x_2582_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec(v_docComment_x3f_2581_);
lean_dec(v_x_2333_);
v___x_2584_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v_a_2335_);
return v___x_2585_;
}
else
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_docComment_x3f_2581_);
v_docComment_x3f_2559_ = v___x_2586_;
v___y_2560_ = v_a_2334_;
v___y_2561_ = v_a_2335_;
goto v___jp_2558_;
}
}
}
else
{
lean_object* v___x_2587_; 
lean_dec(v___x_2575_);
v___x_2587_ = lean_box(0);
v_docComment_x3f_2559_ = v___x_2587_;
v___y_2560_ = v_a_2334_;
v___y_2561_ = v_a_2335_;
goto v___jp_2558_;
}
v___jp_2341_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__2));
lean_inc_n(v___y_2344_, 2);
v___x_2353_ = l_Lean_Fmt_fmtWhereDeclaration(v___y_2348_, v___y_2344_, v___y_2351_, v___x_2352_, v___y_2344_, v___y_2344_, v___y_2347_, v___y_2343_, v___y_2346_, v___y_2349_, v___y_2342_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v_a_2355_; lean_object* v___x_2356_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
v_a_2355_ = lean_ctor_get(v___x_2353_, 1);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2353_, 2);
v___x_2356_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_2345_, v___y_2350_, v___x_2352_, v_a_2354_, v___y_2349_, v_a_2355_);
return v___x_2356_;
}
else
{
lean_dec(v___y_2350_);
lean_dec(v___y_2345_);
return v___x_2353_;
}
}
v___jp_2357_:
{
lean_object* v_fields_2367_; lean_object* v___x_2368_; 
v_fields_2367_ = l_Lean_Syntax_getArgs(v___y_2362_);
lean_dec(v___y_2362_);
v___x_2368_ = lean_box(0);
if (lean_obj_tag(v___y_2358_) == 0)
{
v___y_2342_ = v___y_2366_;
v___y_2343_ = v_fields_2367_;
v___y_2344_ = v___x_2368_;
v___y_2345_ = v___y_2359_;
v___y_2346_ = v_whereDecls_x3f_2364_;
v___y_2347_ = v___y_2360_;
v___y_2348_ = v___y_2361_;
v___y_2349_ = v___y_2365_;
v___y_2350_ = v___y_2363_;
v___y_2351_ = v___x_2368_;
goto v___jp_2341_;
}
else
{
lean_object* v_val_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_val_2369_ = lean_ctor_get(v___y_2358_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___y_2358_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___y_2358_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_val_2369_);
lean_dec(v___y_2358_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_val_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
v___y_2342_ = v___y_2366_;
v___y_2343_ = v_fields_2367_;
v___y_2344_ = v___x_2368_;
v___y_2345_ = v___y_2359_;
v___y_2346_ = v_whereDecls_x3f_2364_;
v___y_2347_ = v___y_2360_;
v___y_2348_ = v___y_2361_;
v___y_2349_ = v___y_2365_;
v___y_2350_ = v___y_2363_;
v___y_2351_ = v___x_2374_;
goto v___jp_2341_;
}
}
}
}
v___jp_2377_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__2));
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___y_2380_);
lean_inc_n(v___y_2385_, 2);
v___x_2390_ = l_Lean_Fmt_fmtMatchDeclaration(v___y_2383_, v___y_2385_, v___y_2387_, v___x_2388_, v___y_2385_, v___y_2385_, v___y_2379_, v___x_2389_, v___y_2382_, v___y_2384_, v___y_2381_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v_a_2392_; lean_object* v___x_2393_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
v_a_2392_ = lean_ctor_get(v___x_2390_, 1);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2390_, 2);
v___x_2393_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_2378_, v___y_2386_, v___x_2388_, v_a_2391_, v___y_2384_, v_a_2392_);
return v___x_2393_;
}
else
{
lean_dec(v___y_2386_);
lean_dec(v___y_2378_);
return v___x_2390_;
}
}
v___jp_2394_:
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_box(0);
if (lean_obj_tag(v___y_2395_) == 0)
{
v___y_2378_ = v___y_2396_;
v___y_2379_ = v___y_2398_;
v___y_2380_ = v___y_2397_;
v___y_2381_ = v___y_2403_;
v___y_2382_ = v_whereDecls_x3f_2401_;
v___y_2383_ = v___y_2399_;
v___y_2384_ = v___y_2402_;
v___y_2385_ = v___x_2404_;
v___y_2386_ = v___y_2400_;
v___y_2387_ = v___x_2404_;
goto v___jp_2377_;
}
else
{
lean_object* v_val_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
v_val_2405_ = lean_ctor_get(v___y_2395_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___y_2395_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___y_2395_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_val_2405_);
lean_dec(v___y_2395_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_val_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
v___y_2378_ = v___y_2396_;
v___y_2379_ = v___y_2398_;
v___y_2380_ = v___y_2397_;
v___y_2381_ = v___y_2403_;
v___y_2382_ = v_whereDecls_x3f_2401_;
v___y_2383_ = v___y_2399_;
v___y_2384_ = v___y_2402_;
v___y_2385_ = v___x_2404_;
v___y_2386_ = v___y_2400_;
v___y_2387_ = v___x_2410_;
goto v___jp_2377_;
}
}
}
}
v___jp_2413_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__2));
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___y_2421_);
v___x_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___y_2420_);
lean_inc_n(v___y_2415_, 2);
v___x_2428_ = l_Lean_Fmt_fmtAssignmentDeclaration(v___y_2419_, v___y_2415_, v___y_2424_, v___x_2425_, v___y_2415_, v___y_2415_, v___x_2426_, v___y_2416_, v___x_2427_, v___y_2422_, v___y_2414_, v___y_2418_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v_a_2430_; lean_object* v___x_2431_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
v_a_2430_ = lean_ctor_get(v___x_2428_, 1);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2428_, 2);
v___x_2431_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_2417_, v___y_2423_, v___x_2425_, v_a_2429_, v___y_2414_, v_a_2430_);
return v___x_2431_;
}
else
{
lean_dec(v___y_2423_);
lean_dec(v___y_2417_);
return v___x_2428_;
}
}
v___jp_2432_:
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_box(0);
if (lean_obj_tag(v___y_2433_) == 0)
{
v___y_2414_ = v___y_2441_;
v___y_2415_ = v___x_2443_;
v___y_2416_ = v___y_2434_;
v___y_2417_ = v___y_2435_;
v___y_2418_ = v___y_2442_;
v___y_2419_ = v___y_2437_;
v___y_2420_ = v___y_2436_;
v___y_2421_ = v___y_2438_;
v___y_2422_ = v_whereDecls_x3f_2440_;
v___y_2423_ = v___y_2439_;
v___y_2424_ = v___x_2443_;
goto v___jp_2413_;
}
else
{
lean_object* v_val_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
v_val_2444_ = lean_ctor_get(v___y_2433_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___y_2433_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___y_2433_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_val_2444_);
lean_dec(v___y_2433_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_val_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
v___y_2414_ = v___y_2441_;
v___y_2415_ = v___x_2443_;
v___y_2416_ = v___y_2434_;
v___y_2417_ = v___y_2435_;
v___y_2418_ = v___y_2442_;
v___y_2419_ = v___y_2437_;
v___y_2420_ = v___y_2436_;
v___y_2421_ = v___y_2438_;
v___y_2422_ = v_whereDecls_x3f_2440_;
v___y_2423_ = v___y_2439_;
v___y_2424_ = v___x_2449_;
goto v___jp_2413_;
}
}
}
}
v___jp_2452_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2462_ = lean_unsigned_to_nat(4u);
v___x_2463_ = l_Lean_Syntax_getArg(v_x_2333_, v___x_2462_);
lean_dec(v_x_2333_);
v___x_2464_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__5));
lean_inc(v___x_2463_);
v___x_2465_ = l_Lean_Syntax_isOfKind(v___x_2463_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = ((lean_object*)(l_Lake_Formatters_fmtCacheServiceCommand___closed__3));
lean_inc(v___x_2463_);
v___x_2467_ = l_Lean_Syntax_isOfKind(v___x_2463_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2468_ = ((lean_object*)(l_Lake_Formatters_fmtCacheServiceCommand___closed__5));
lean_inc(v___x_2463_);
v___x_2469_ = l_Lean_Syntax_isOfKind(v___x_2463_, v___x_2468_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_dec(v___x_2463_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2470_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
lean_ctor_set(v___x_2471_, 1, v___y_2461_);
return v___x_2471_;
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2472_ = l_Lean_Syntax_getArg(v___x_2463_, v___y_2455_);
v___x_2473_ = ((lean_object*)(l_Lake_Formatters_fmtCacheServiceCommand___closed__7));
lean_inc(v___x_2472_);
v___x_2474_ = l_Lean_Syntax_isOfKind(v___x_2472_, v___x_2473_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_dec(v___x_2472_);
lean_dec(v___x_2463_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2475_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___y_2461_);
return v___x_2476_;
}
else
{
lean_object* v_whereTk_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v_whereTk_2477_ = l_Lean_Syntax_getArg(v___x_2463_, v___x_2340_);
v___x_2478_ = l_Lean_Syntax_getArg(v___x_2472_, v___x_2340_);
lean_dec(v___x_2472_);
v___x_2479_ = l_Lean_Syntax_getArg(v___x_2463_, v___y_2457_);
lean_dec(v___x_2463_);
v___x_2480_ = l_Lean_Syntax_isNone(v___x_2479_);
if (v___x_2480_ == 0)
{
uint8_t v___x_2481_; 
lean_inc(v___x_2479_);
v___x_2481_ = l_Lean_Syntax_matchesNull(v___x_2479_, v___y_2455_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec(v___x_2479_);
lean_dec(v___x_2478_);
lean_dec(v_whereTk_2477_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2482_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
lean_ctor_set(v___x_2483_, 1, v___y_2461_);
return v___x_2483_;
}
else
{
lean_object* v_whereDecls_x3f_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_whereDecls_x3f_2484_ = l_Lean_Syntax_getArg(v___x_2479_, v___x_2340_);
lean_dec(v___x_2479_);
v___x_2485_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__11));
lean_inc(v_whereDecls_x3f_2484_);
v___x_2486_ = l_Lean_Syntax_isOfKind(v_whereDecls_x3f_2484_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
lean_dec(v_whereDecls_x3f_2484_);
lean_dec(v___x_2478_);
lean_dec(v_whereTk_2477_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2487_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___y_2461_);
return v___x_2488_;
}
else
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_whereDecls_x3f_2484_);
v___y_2358_ = v_name_x3f_2459_;
v___y_2359_ = v___y_2454_;
v___y_2360_ = v_whereTk_2477_;
v___y_2361_ = v___y_2456_;
v___y_2362_ = v___x_2478_;
v___y_2363_ = v___y_2458_;
v_whereDecls_x3f_2364_ = v___x_2489_;
v___y_2365_ = v___y_2460_;
v___y_2366_ = v___y_2461_;
goto v___jp_2357_;
}
}
}
else
{
lean_object* v___x_2490_; 
lean_dec(v___x_2479_);
v___x_2490_ = lean_box(0);
v___y_2358_ = v_name_x3f_2459_;
v___y_2359_ = v___y_2454_;
v___y_2360_ = v_whereTk_2477_;
v___y_2361_ = v___y_2456_;
v___y_2362_ = v___x_2478_;
v___y_2363_ = v___y_2458_;
v_whereDecls_x3f_2364_ = v___x_2490_;
v___y_2365_ = v___y_2460_;
v___y_2366_ = v___y_2461_;
goto v___jp_2357_;
}
}
}
}
else
{
lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2491_ = l_Lean_Syntax_getArg(v___x_2463_, v___x_2340_);
lean_dec(v___x_2463_);
v___x_2492_ = ((lean_object*)(l_Lake_Formatters_fmtCacheServiceCommand___closed__9));
lean_inc(v___x_2491_);
v___x_2493_ = l_Lean_Syntax_isOfKind(v___x_2491_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_dec(v___x_2491_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2494_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v___y_2461_);
return v___x_2495_;
}
else
{
lean_object* v_matchAlts_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v_matchAlts_2496_ = l_Lean_Syntax_getArg(v___x_2491_, v___x_2340_);
v___x_2497_ = ((lean_object*)(l_Lake_Formatters_fmtCacheServiceCommand___closed__11));
lean_inc(v_matchAlts_2496_);
v___x_2498_ = l_Lean_Syntax_isOfKind(v_matchAlts_2496_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec(v_matchAlts_2496_);
lean_dec(v___x_2491_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2499_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v___y_2461_);
return v___x_2500_;
}
else
{
lean_object* v_terminationSuffix_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v_terminationSuffix_2501_ = l_Lean_Syntax_getArg(v___x_2491_, v___y_2455_);
v___x_2502_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3));
lean_inc(v_terminationSuffix_2501_);
v___x_2503_ = l_Lean_Syntax_isOfKind(v_terminationSuffix_2501_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec(v_terminationSuffix_2501_);
lean_dec(v_matchAlts_2496_);
lean_dec(v___x_2491_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2504_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
lean_ctor_set(v___x_2505_, 1, v___y_2461_);
return v___x_2505_;
}
else
{
lean_object* v___x_2506_; uint8_t v___x_2507_; 
v___x_2506_ = l_Lean_Syntax_getArg(v___x_2491_, v___y_2457_);
lean_dec(v___x_2491_);
v___x_2507_ = l_Lean_Syntax_isNone(v___x_2506_);
if (v___x_2507_ == 0)
{
uint8_t v___x_2508_; 
lean_inc(v___x_2506_);
v___x_2508_ = l_Lean_Syntax_matchesNull(v___x_2506_, v___y_2455_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec(v___x_2506_);
lean_dec(v_terminationSuffix_2501_);
lean_dec(v_matchAlts_2496_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2509_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v___y_2461_);
return v___x_2510_;
}
else
{
lean_object* v_whereDecls_x3f_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_whereDecls_x3f_2511_ = l_Lean_Syntax_getArg(v___x_2506_, v___x_2340_);
lean_dec(v___x_2506_);
v___x_2512_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__11));
lean_inc(v_whereDecls_x3f_2511_);
v___x_2513_ = l_Lean_Syntax_isOfKind(v_whereDecls_x3f_2511_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec(v_whereDecls_x3f_2511_);
lean_dec(v_terminationSuffix_2501_);
lean_dec(v_matchAlts_2496_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2514_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
lean_ctor_set(v___x_2515_, 1, v___y_2461_);
return v___x_2515_;
}
else
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_whereDecls_x3f_2511_);
v___y_2395_ = v_name_x3f_2459_;
v___y_2396_ = v___y_2454_;
v___y_2397_ = v_terminationSuffix_2501_;
v___y_2398_ = v_matchAlts_2496_;
v___y_2399_ = v___y_2456_;
v___y_2400_ = v___y_2458_;
v_whereDecls_x3f_2401_ = v___x_2516_;
v___y_2402_ = v___y_2460_;
v___y_2403_ = v___y_2461_;
goto v___jp_2394_;
}
}
}
else
{
lean_object* v___x_2517_; 
lean_dec(v___x_2506_);
v___x_2517_ = lean_box(0);
v___y_2395_ = v_name_x3f_2459_;
v___y_2396_ = v___y_2454_;
v___y_2397_ = v_terminationSuffix_2501_;
v___y_2398_ = v_matchAlts_2496_;
v___y_2399_ = v___y_2456_;
v___y_2400_ = v___y_2458_;
v_whereDecls_x3f_2401_ = v___x_2517_;
v___y_2402_ = v___y_2460_;
v___y_2403_ = v___y_2461_;
goto v___jp_2394_;
}
}
}
}
}
}
else
{
lean_object* v_terminationSuffix_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; 
v_terminationSuffix_2518_ = l_Lean_Syntax_getArg(v___x_2463_, v___y_2457_);
v___x_2519_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3));
lean_inc(v_terminationSuffix_2518_);
v___x_2520_ = l_Lean_Syntax_isOfKind(v_terminationSuffix_2518_, v___x_2519_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec(v_terminationSuffix_2518_);
lean_dec(v___x_2463_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2521_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___y_2461_);
return v___x_2522_;
}
else
{
lean_object* v_colonEqTk_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_colonEqTk_2523_ = l_Lean_Syntax_getArg(v___x_2463_, v___x_2340_);
v___x_2524_ = l_Lean_Syntax_getArg(v___x_2463_, v___y_2455_);
v___x_2525_ = l_Lean_Syntax_getArg(v___x_2463_, v___y_2453_);
lean_dec(v___x_2463_);
v___x_2526_ = l_Lean_Syntax_isNone(v___x_2525_);
if (v___x_2526_ == 0)
{
uint8_t v___x_2527_; 
lean_inc(v___x_2525_);
v___x_2527_ = l_Lean_Syntax_matchesNull(v___x_2525_, v___y_2455_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec(v___x_2525_);
lean_dec(v___x_2524_);
lean_dec(v_colonEqTk_2523_);
lean_dec(v_terminationSuffix_2518_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2528_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v___y_2461_);
return v___x_2529_;
}
else
{
lean_object* v_whereDecls_x3f_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v_whereDecls_x3f_2530_ = l_Lean_Syntax_getArg(v___x_2525_, v___x_2340_);
lean_dec(v___x_2525_);
v___x_2531_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__11));
lean_inc(v_whereDecls_x3f_2530_);
v___x_2532_ = l_Lean_Syntax_isOfKind(v_whereDecls_x3f_2530_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_dec(v_whereDecls_x3f_2530_);
lean_dec(v___x_2524_);
lean_dec(v_colonEqTk_2523_);
lean_dec(v_terminationSuffix_2518_);
lean_dec(v_name_x3f_2459_);
lean_dec(v___y_2458_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
v___x_2533_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
lean_ctor_set(v___x_2534_, 1, v___y_2461_);
return v___x_2534_;
}
else
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_whereDecls_x3f_2530_);
v___y_2433_ = v_name_x3f_2459_;
v___y_2434_ = v___x_2524_;
v___y_2435_ = v___y_2454_;
v___y_2436_ = v_terminationSuffix_2518_;
v___y_2437_ = v___y_2456_;
v___y_2438_ = v_colonEqTk_2523_;
v___y_2439_ = v___y_2458_;
v_whereDecls_x3f_2440_ = v___x_2535_;
v___y_2441_ = v___y_2460_;
v___y_2442_ = v___y_2461_;
goto v___jp_2432_;
}
}
}
else
{
lean_object* v___x_2536_; 
lean_dec(v___x_2525_);
v___x_2536_ = lean_box(0);
v___y_2433_ = v_name_x3f_2459_;
v___y_2434_ = v___x_2524_;
v___y_2435_ = v___y_2454_;
v___y_2436_ = v_terminationSuffix_2518_;
v___y_2437_ = v___y_2456_;
v___y_2438_ = v_colonEqTk_2523_;
v___y_2439_ = v___y_2458_;
v_whereDecls_x3f_2440_ = v___x_2536_;
v___y_2441_ = v___y_2460_;
v___y_2442_ = v___y_2461_;
goto v___jp_2432_;
}
}
}
}
v___jp_2537_:
{
lean_object* v___x_2543_; lean_object* v_cacheServiceTk_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2543_ = lean_unsigned_to_nat(2u);
v_cacheServiceTk_2544_ = l_Lean_Syntax_getArg(v_x_2333_, v___x_2543_);
v___x_2545_ = lean_unsigned_to_nat(3u);
v___x_2546_ = l_Lean_Syntax_getArg(v_x_2333_, v___x_2545_);
v___x_2547_ = l_Lean_Syntax_isNone(v___x_2546_);
if (v___x_2547_ == 0)
{
uint8_t v___x_2548_; 
lean_inc(v___x_2546_);
v___x_2548_ = l_Lean_Syntax_matchesNull(v___x_2546_, v___y_2539_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
lean_dec(v___x_2546_);
lean_dec(v_cacheServiceTk_2544_);
lean_dec(v_attributes_x3f_2540_);
lean_dec(v___y_2538_);
lean_dec(v_x_2333_);
v___x_2549_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___y_2542_);
return v___x_2550_;
}
else
{
lean_object* v_name_x3f_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v_name_x3f_2551_ = l_Lean_Syntax_getArg(v___x_2546_, v___x_2340_);
lean_dec(v___x_2546_);
v___x_2552_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__6));
lean_inc(v_name_x3f_2551_);
v___x_2553_ = l_Lean_Syntax_isOfKind(v_name_x3f_2551_, v___x_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec(v_name_x3f_2551_);
lean_dec(v_cacheServiceTk_2544_);
lean_dec(v_attributes_x3f_2540_);
lean_dec(v___y_2538_);
lean_dec(v_x_2333_);
v___x_2554_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v___y_2542_);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_name_x3f_2551_);
v___y_2453_ = v___x_2545_;
v___y_2454_ = v___y_2538_;
v___y_2455_ = v___y_2539_;
v___y_2456_ = v_cacheServiceTk_2544_;
v___y_2457_ = v___x_2543_;
v___y_2458_ = v_attributes_x3f_2540_;
v_name_x3f_2459_ = v___x_2556_;
v___y_2460_ = v___y_2541_;
v___y_2461_ = v___y_2542_;
goto v___jp_2452_;
}
}
}
else
{
lean_object* v___x_2557_; 
lean_dec(v___x_2546_);
v___x_2557_ = lean_box(0);
v___y_2453_ = v___x_2545_;
v___y_2454_ = v___y_2538_;
v___y_2455_ = v___y_2539_;
v___y_2456_ = v_cacheServiceTk_2544_;
v___y_2457_ = v___x_2543_;
v___y_2458_ = v_attributes_x3f_2540_;
v_name_x3f_2459_ = v___x_2557_;
v___y_2460_ = v___y_2541_;
v___y_2461_ = v___y_2542_;
goto v___jp_2452_;
}
}
v___jp_2558_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2562_ = lean_unsigned_to_nat(1u);
v___x_2563_ = l_Lean_Syntax_getArg(v_x_2333_, v___x_2562_);
v___x_2564_ = l_Lean_Syntax_isNone(v___x_2563_);
if (v___x_2564_ == 0)
{
uint8_t v___x_2565_; 
lean_inc(v___x_2563_);
v___x_2565_ = l_Lean_Syntax_matchesNull(v___x_2563_, v___x_2562_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v___x_2563_);
lean_dec(v_docComment_x3f_2559_);
lean_dec(v_x_2333_);
v___x_2566_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v___y_2561_);
return v___x_2567_;
}
else
{
lean_object* v_attributes_x3f_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v_attributes_x3f_2568_ = l_Lean_Syntax_getArg(v___x_2563_, v___x_2340_);
lean_dec(v___x_2563_);
v___x_2569_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_2568_);
v___x_2570_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_2568_, v___x_2569_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec(v_attributes_x3f_2568_);
lean_dec(v_docComment_x3f_2559_);
lean_dec(v_x_2333_);
v___x_2571_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___y_2561_);
return v___x_2572_;
}
else
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_attributes_x3f_2568_);
v___y_2538_ = v_docComment_x3f_2559_;
v___y_2539_ = v___x_2562_;
v_attributes_x3f_2540_ = v___x_2573_;
v___y_2541_ = v___y_2560_;
v___y_2542_ = v___y_2561_;
goto v___jp_2537_;
}
}
}
else
{
lean_object* v___x_2574_; 
lean_dec(v___x_2563_);
v___x_2574_ = lean_box(0);
v___y_2538_ = v_docComment_x3f_2559_;
v___y_2539_ = v___x_2562_;
v_attributes_x3f_2540_ = v___x_2574_;
v___y_2541_ = v___y_2560_;
v___y_2542_ = v___y_2561_;
goto v___jp_2537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtCacheServiceCommand___boxed(lean_object* v_x_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lake_Formatters_fmtCacheServiceCommand(v_x_2588_, v_a_2589_, v_a_2590_);
lean_dec_ref(v_a_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1(){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2598_ = l_Lean_Fmt_fmtAttribute;
v___x_2599_ = ((lean_object*)(l_Lake_Formatters_fmtCacheServiceCommand___closed__1));
v___x_2600_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___closed__1));
v___x_2601_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtCacheServiceCommand___boxed), 3, 0);
v___x_2602_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2598_, v___x_2599_, v___x_2600_, v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1___boxed(lean_object* v_a_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1();
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtScriptDecl(lean_object* v_x_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = ((lean_object*)(l_Lake_Formatters_fmtScriptDecl___closed__1));
lean_inc(v_x_2615_);
v___x_2619_ = l_Lean_Syntax_isOfKind(v_x_2615_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_dec(v_x_2615_);
v___x_2620_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v_a_2617_);
return v___x_2621_;
}
else
{
lean_object* v___x_2622_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v_whereDecls_x3f_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v_whereDecls_x3f_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v_binder_x3f_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v_attributes_x3f_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v_docComment_x3f_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2789_ = l_Lean_Syntax_getArg(v_x_2615_, v___x_2622_);
v___x_2790_ = l_Lean_Syntax_isNone(v___x_2789_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2791_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2789_);
v___x_2792_ = l_Lean_Syntax_matchesNull(v___x_2789_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec(v___x_2789_);
lean_dec(v_x_2615_);
v___x_2793_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v_a_2617_);
return v___x_2794_;
}
else
{
lean_object* v_docComment_x3f_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v_docComment_x3f_2795_ = l_Lean_Syntax_getArg(v___x_2789_, v___x_2622_);
lean_dec(v___x_2789_);
v___x_2796_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__14));
lean_inc(v_docComment_x3f_2795_);
v___x_2797_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_2795_, v___x_2796_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
lean_dec(v_docComment_x3f_2795_);
lean_dec(v_x_2615_);
v___x_2798_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v_a_2617_);
return v___x_2799_;
}
else
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2800_, 0, v_docComment_x3f_2795_);
v_docComment_x3f_2773_ = v___x_2800_;
v___y_2774_ = v_a_2616_;
v___y_2775_ = v_a_2617_;
goto v___jp_2772_;
}
}
}
else
{
lean_object* v___x_2801_; 
lean_dec(v___x_2789_);
v___x_2801_ = lean_box(0);
v_docComment_x3f_2773_ = v___x_2801_;
v___y_2774_ = v_a_2616_;
v___y_2775_ = v_a_2617_;
goto v___jp_2772_;
}
v___jp_2623_:
{
lean_object* v___x_2633_; 
v___x_2633_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg(v___y_2624_, v___y_2632_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v_a_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
v_a_2635_ = lean_ctor_get(v___x_2633_, 1);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2633_, 2);
v___x_2636_ = lean_box(0);
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___y_2626_);
v___x_2638_ = lean_obj_once(&l_Lake_Formatters_fmtPostUpdateDecl___closed__3, &l_Lake_Formatters_fmtPostUpdateDecl___closed__3_once, _init_l_Lake_Formatters_fmtPostUpdateDecl___closed__3);
v___x_2639_ = l_Lean_Fmt_fmtAssignmentDeclaration(v___y_2625_, v___x_2636_, v___x_2637_, v_a_2634_, v___x_2636_, v___x_2636_, v___x_2636_, v___y_2629_, v___x_2638_, v_whereDecls_x3f_2630_, v___y_2631_, v_a_2635_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v_a_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
v_a_2641_ = lean_ctor_get(v___x_2639_, 1);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2639_, 2);
v___x_2642_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_2643_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_2627_, v___y_2628_, v___x_2642_, v_a_2640_, v___y_2631_, v_a_2641_);
return v___x_2643_;
}
else
{
lean_dec(v___y_2628_);
lean_dec(v___y_2627_);
return v___x_2639_;
}
}
else
{
lean_object* v_a_2644_; lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_whereDecls_x3f_2630_);
lean_dec(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec(v___y_2625_);
v_a_2644_ = lean_ctor_get(v___x_2633_, 0);
v_a_2645_ = lean_ctor_get(v___x_2633_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2633_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_inc(v_a_2644_);
lean_dec(v___x_2633_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2644_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
v___jp_2653_:
{
lean_object* v___x_2665_; 
v___x_2665_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_toDeclarationBinders___redArg(v___y_2654_, v___y_2664_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v_a_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
v_a_2667_ = lean_ctor_get(v___x_2665_, 1);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2665_, 2);
v___x_2668_ = lean_box(0);
v___x_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___y_2656_);
v___x_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___y_2658_);
v___x_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___y_2660_);
v___x_2672_ = l_Lean_Fmt_fmtAssignmentDeclaration(v___y_2655_, v___x_2668_, v___x_2669_, v_a_2666_, v___x_2668_, v___x_2668_, v___x_2670_, v___y_2657_, v___x_2671_, v_whereDecls_x3f_2662_, v___y_2663_, v_a_2667_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v_a_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
v_a_2674_ = lean_ctor_get(v___x_2672_, 1);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2672_, 2);
v___x_2675_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__4));
v___x_2676_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_2659_, v___y_2661_, v___x_2675_, v_a_2673_, v___y_2663_, v_a_2674_);
return v___x_2676_;
}
else
{
lean_dec(v___y_2661_);
lean_dec(v___y_2659_);
return v___x_2672_;
}
}
else
{
lean_object* v_a_2677_; lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_whereDecls_x3f_2662_);
lean_dec(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec(v___y_2655_);
v_a_2677_ = lean_ctor_get(v___x_2665_, 0);
v_a_2678_ = lean_ctor_get(v___x_2665_, 1);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2665_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_inc(v_a_2677_);
lean_dec(v___x_2665_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2677_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
v___jp_2686_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2698_ = l_Lean_Syntax_getArg(v___y_2692_, v___y_2689_);
lean_dec(v___y_2692_);
v___x_2699_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__5));
lean_inc(v___x_2698_);
v___x_2700_ = l_Lean_Syntax_isOfKind(v___x_2698_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2701_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__7));
lean_inc(v___x_2698_);
v___x_2702_ = l_Lean_Syntax_isOfKind(v___x_2698_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_dec(v___x_2698_);
lean_dec(v_binder_x3f_2695_);
lean_dec(v___y_2694_);
lean_dec(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2688_);
v___x_2703_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v___y_2697_);
return v___x_2704_;
}
else
{
lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2705_ = l_Lean_Syntax_getArg(v___x_2698_, v___x_2622_);
v___x_2706_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__9));
lean_inc(v___x_2705_);
v___x_2707_ = l_Lean_Syntax_isOfKind(v___x_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec(v___x_2705_);
lean_dec(v___x_2698_);
lean_dec(v_binder_x3f_2695_);
lean_dec(v___y_2694_);
lean_dec(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2688_);
v___x_2708_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v___y_2697_);
return v___x_2709_;
}
else
{
lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2710_ = l_Lean_Syntax_getArg(v___x_2698_, v___y_2687_);
lean_dec(v___x_2698_);
v___x_2711_ = l_Lean_Syntax_isNone(v___x_2710_);
if (v___x_2711_ == 0)
{
uint8_t v___x_2712_; 
lean_inc(v___x_2710_);
v___x_2712_ = l_Lean_Syntax_matchesNull(v___x_2710_, v___y_2687_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec(v___x_2710_);
lean_dec(v___x_2705_);
lean_dec(v_binder_x3f_2695_);
lean_dec(v___y_2694_);
lean_dec(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2688_);
v___x_2713_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v___y_2697_);
return v___x_2714_;
}
else
{
lean_object* v_whereDecls_x3f_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v_whereDecls_x3f_2715_ = l_Lean_Syntax_getArg(v___x_2710_, v___x_2622_);
lean_dec(v___x_2710_);
v___x_2716_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__11));
lean_inc(v_whereDecls_x3f_2715_);
v___x_2717_ = l_Lean_Syntax_isOfKind(v_whereDecls_x3f_2715_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_dec(v_whereDecls_x3f_2715_);
lean_dec(v___x_2705_);
lean_dec(v_binder_x3f_2695_);
lean_dec(v___y_2694_);
lean_dec(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2688_);
v___x_2718_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v___y_2697_);
return v___x_2719_;
}
else
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_whereDecls_x3f_2715_);
v___y_2624_ = v_binder_x3f_2695_;
v___y_2625_ = v___y_2688_;
v___y_2626_ = v___y_2690_;
v___y_2627_ = v___y_2691_;
v___y_2628_ = v___y_2694_;
v___y_2629_ = v___x_2705_;
v_whereDecls_x3f_2630_ = v___x_2720_;
v___y_2631_ = v___y_2696_;
v___y_2632_ = v___y_2697_;
goto v___jp_2623_;
}
}
}
else
{
lean_object* v___x_2721_; 
lean_dec(v___x_2710_);
v___x_2721_ = lean_box(0);
v___y_2624_ = v_binder_x3f_2695_;
v___y_2625_ = v___y_2688_;
v___y_2626_ = v___y_2690_;
v___y_2627_ = v___y_2691_;
v___y_2628_ = v___y_2694_;
v___y_2629_ = v___x_2705_;
v_whereDecls_x3f_2630_ = v___x_2721_;
v___y_2631_ = v___y_2696_;
v___y_2632_ = v___y_2697_;
goto v___jp_2623_;
}
}
}
}
else
{
lean_object* v_terminationSuffix_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v_terminationSuffix_2722_ = l_Lean_Syntax_getArg(v___x_2698_, v___y_2689_);
v___x_2723_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix___closed__3));
lean_inc(v_terminationSuffix_2722_);
v___x_2724_ = l_Lean_Syntax_isOfKind(v_terminationSuffix_2722_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_dec(v_terminationSuffix_2722_);
lean_dec(v___x_2698_);
lean_dec(v_binder_x3f_2695_);
lean_dec(v___y_2694_);
lean_dec(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2688_);
v___x_2725_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
lean_ctor_set(v___x_2726_, 1, v___y_2697_);
return v___x_2726_;
}
else
{
lean_object* v_colonEqTk_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v_colonEqTk_2727_ = l_Lean_Syntax_getArg(v___x_2698_, v___x_2622_);
v___x_2728_ = l_Lean_Syntax_getArg(v___x_2698_, v___y_2687_);
v___x_2729_ = l_Lean_Syntax_getArg(v___x_2698_, v___y_2693_);
lean_dec(v___x_2698_);
v___x_2730_ = l_Lean_Syntax_isNone(v___x_2729_);
if (v___x_2730_ == 0)
{
uint8_t v___x_2731_; 
lean_inc(v___x_2729_);
v___x_2731_ = l_Lean_Syntax_matchesNull(v___x_2729_, v___y_2687_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_dec(v___x_2729_);
lean_dec(v___x_2728_);
lean_dec(v_colonEqTk_2727_);
lean_dec(v_terminationSuffix_2722_);
lean_dec(v_binder_x3f_2695_);
lean_dec(v___y_2694_);
lean_dec(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2688_);
v___x_2732_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v___y_2697_);
return v___x_2733_;
}
else
{
lean_object* v_whereDecls_x3f_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
v_whereDecls_x3f_2734_ = l_Lean_Syntax_getArg(v___x_2729_, v___x_2622_);
lean_dec(v___x_2729_);
v___x_2735_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__11));
lean_inc(v_whereDecls_x3f_2734_);
v___x_2736_ = l_Lean_Syntax_isOfKind(v_whereDecls_x3f_2734_, v___x_2735_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_dec(v_whereDecls_x3f_2734_);
lean_dec(v___x_2728_);
lean_dec(v_colonEqTk_2727_);
lean_dec(v_terminationSuffix_2722_);
lean_dec(v_binder_x3f_2695_);
lean_dec(v___y_2694_);
lean_dec(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2688_);
v___x_2737_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v___y_2697_);
return v___x_2738_;
}
else
{
lean_object* v___x_2739_; 
v___x_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2739_, 0, v_whereDecls_x3f_2734_);
v___y_2654_ = v_binder_x3f_2695_;
v___y_2655_ = v___y_2688_;
v___y_2656_ = v___y_2690_;
v___y_2657_ = v___x_2728_;
v___y_2658_ = v_colonEqTk_2727_;
v___y_2659_ = v___y_2691_;
v___y_2660_ = v_terminationSuffix_2722_;
v___y_2661_ = v___y_2694_;
v_whereDecls_x3f_2662_ = v___x_2739_;
v___y_2663_ = v___y_2696_;
v___y_2664_ = v___y_2697_;
goto v___jp_2653_;
}
}
}
else
{
lean_object* v___x_2740_; 
lean_dec(v___x_2729_);
v___x_2740_ = lean_box(0);
v___y_2654_ = v_binder_x3f_2695_;
v___y_2655_ = v___y_2688_;
v___y_2656_ = v___y_2690_;
v___y_2657_ = v___x_2728_;
v___y_2658_ = v_colonEqTk_2727_;
v___y_2659_ = v___y_2691_;
v___y_2660_ = v_terminationSuffix_2722_;
v___y_2661_ = v___y_2694_;
v_whereDecls_x3f_2662_ = v___x_2740_;
v___y_2663_ = v___y_2696_;
v___y_2664_ = v___y_2697_;
goto v___jp_2653_;
}
}
}
}
v___jp_2741_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2747_ = lean_unsigned_to_nat(3u);
v___x_2748_ = l_Lean_Syntax_getArg(v_x_2615_, v___x_2747_);
v___x_2749_ = ((lean_object*)(l_Lake_Formatters_fmtScriptDecl___closed__3));
lean_inc(v___x_2748_);
v___x_2750_ = l_Lean_Syntax_isOfKind(v___x_2748_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_dec(v___x_2748_);
lean_dec(v_attributes_x3f_2744_);
lean_dec(v___y_2743_);
lean_dec(v_x_2615_);
v___x_2751_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
lean_ctor_set(v___x_2752_, 1, v___y_2746_);
return v___x_2752_;
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2753_ = l_Lean_Syntax_getArg(v___x_2748_, v___x_2622_);
v___x_2754_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__6));
lean_inc(v___x_2753_);
v___x_2755_ = l_Lean_Syntax_isOfKind(v___x_2753_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
lean_dec(v___x_2753_);
lean_dec(v___x_2748_);
lean_dec(v_attributes_x3f_2744_);
lean_dec(v___y_2743_);
lean_dec(v_x_2615_);
v___x_2756_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
lean_ctor_set(v___x_2757_, 1, v___y_2746_);
return v___x_2757_;
}
else
{
lean_object* v___x_2758_; lean_object* v_scriptTk_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v___x_2758_ = lean_unsigned_to_nat(2u);
v_scriptTk_2759_ = l_Lean_Syntax_getArg(v_x_2615_, v___x_2758_);
lean_dec(v_x_2615_);
v___x_2760_ = l_Lean_Syntax_getArg(v___x_2748_, v___y_2742_);
v___x_2761_ = l_Lean_Syntax_isNone(v___x_2760_);
if (v___x_2761_ == 0)
{
uint8_t v___x_2762_; 
lean_inc(v___x_2760_);
v___x_2762_ = l_Lean_Syntax_matchesNull(v___x_2760_, v___y_2742_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec(v___x_2760_);
lean_dec(v_scriptTk_2759_);
lean_dec(v___x_2753_);
lean_dec(v___x_2748_);
lean_dec(v_attributes_x3f_2744_);
lean_dec(v___y_2743_);
v___x_2763_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
lean_ctor_set(v___x_2764_, 1, v___y_2746_);
return v___x_2764_;
}
else
{
lean_object* v_binder_x3f_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_binder_x3f_2765_ = l_Lean_Syntax_getArg(v___x_2760_, v___x_2622_);
lean_dec(v___x_2760_);
v___x_2766_ = ((lean_object*)(l_Lake_Formatters_fmtPostUpdateDecl___closed__13));
lean_inc(v_binder_x3f_2765_);
v___x_2767_ = l_Lean_Syntax_isOfKind(v_binder_x3f_2765_, v___x_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_dec(v_binder_x3f_2765_);
lean_dec(v_scriptTk_2759_);
lean_dec(v___x_2753_);
lean_dec(v___x_2748_);
lean_dec(v_attributes_x3f_2744_);
lean_dec(v___y_2743_);
v___x_2768_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
lean_ctor_set(v___x_2769_, 1, v___y_2746_);
return v___x_2769_;
}
else
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2770_, 0, v_binder_x3f_2765_);
v___y_2687_ = v___y_2742_;
v___y_2688_ = v_scriptTk_2759_;
v___y_2689_ = v___x_2758_;
v___y_2690_ = v___x_2753_;
v___y_2691_ = v___y_2743_;
v___y_2692_ = v___x_2748_;
v___y_2693_ = v___x_2747_;
v___y_2694_ = v_attributes_x3f_2744_;
v_binder_x3f_2695_ = v___x_2770_;
v___y_2696_ = v___y_2745_;
v___y_2697_ = v___y_2746_;
goto v___jp_2686_;
}
}
}
else
{
lean_object* v___x_2771_; 
lean_dec(v___x_2760_);
v___x_2771_ = lean_box(0);
v___y_2687_ = v___y_2742_;
v___y_2688_ = v_scriptTk_2759_;
v___y_2689_ = v___x_2758_;
v___y_2690_ = v___x_2753_;
v___y_2691_ = v___y_2743_;
v___y_2692_ = v___x_2748_;
v___y_2693_ = v___x_2747_;
v___y_2694_ = v_attributes_x3f_2744_;
v_binder_x3f_2695_ = v___x_2771_;
v___y_2696_ = v___y_2745_;
v___y_2697_ = v___y_2746_;
goto v___jp_2686_;
}
}
}
}
v___jp_2772_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2776_ = lean_unsigned_to_nat(1u);
v___x_2777_ = l_Lean_Syntax_getArg(v_x_2615_, v___x_2776_);
v___x_2778_ = l_Lean_Syntax_isNone(v___x_2777_);
if (v___x_2778_ == 0)
{
uint8_t v___x_2779_; 
lean_inc(v___x_2777_);
v___x_2779_ = l_Lean_Syntax_matchesNull(v___x_2777_, v___x_2776_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
lean_dec(v___x_2777_);
lean_dec(v_docComment_x3f_2773_);
lean_dec(v_x_2615_);
v___x_2780_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
lean_ctor_set(v___x_2781_, 1, v___y_2775_);
return v___x_2781_;
}
else
{
lean_object* v_attributes_x3f_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v_attributes_x3f_2782_ = l_Lean_Syntax_getArg(v___x_2777_, v___x_2622_);
lean_dec(v___x_2777_);
v___x_2783_ = ((lean_object*)(l_Lake_Formatters_fmtPackageCommand___closed__11));
lean_inc(v_attributes_x3f_2782_);
v___x_2784_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_2782_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec(v_attributes_x3f_2782_);
lean_dec(v_docComment_x3f_2773_);
lean_dec(v_x_2615_);
v___x_2785_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v___y_2775_);
return v___x_2786_;
}
else
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_attributes_x3f_2782_);
v___y_2742_ = v___x_2776_;
v___y_2743_ = v_docComment_x3f_2773_;
v_attributes_x3f_2744_ = v___x_2787_;
v___y_2745_ = v___y_2774_;
v___y_2746_ = v___y_2775_;
goto v___jp_2741_;
}
}
}
else
{
lean_object* v___x_2788_; 
lean_dec(v___x_2777_);
v___x_2788_ = lean_box(0);
v___y_2742_ = v___x_2776_;
v___y_2743_ = v_docComment_x3f_2773_;
v_attributes_x3f_2744_ = v___x_2788_;
v___y_2745_ = v___y_2774_;
v___y_2746_ = v___y_2775_;
goto v___jp_2741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtScriptDecl___boxed(lean_object* v_x_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lake_Formatters_fmtScriptDecl(v_x_2802_, v_a_2803_, v_a_2804_);
lean_dec_ref(v_a_2803_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1(){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2812_ = l_Lean_Fmt_fmtAttribute;
v___x_2813_ = ((lean_object*)(l_Lake_Formatters_fmtScriptDecl___closed__1));
v___x_2814_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___closed__1));
v___x_2815_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtScriptDecl___boxed), 3, 0);
v___x_2816_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2812_, v___x_2813_, v___x_2814_, v___x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1___boxed(lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1();
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtEvalVer(lean_object* v_x_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2827_ = ((lean_object*)(l_Lake_Formatters_fmtEvalVer___closed__1));
lean_inc(v_x_2824_);
v___x_2828_ = l_Lean_Syntax_isOfKind(v_x_2824_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec(v_x_2824_);
v___x_2829_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v_a_2826_);
return v___x_2830_;
}
else
{
lean_object* v___x_2831_; lean_object* v_evalVerTk_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2831_ = lean_unsigned_to_nat(0u);
v_evalVerTk_2832_ = l_Lean_Syntax_getArg(v_x_2824_, v___x_2831_);
v___x_2833_ = lean_unsigned_to_nat(1u);
v___x_2834_ = l_Lean_Syntax_getArg(v_x_2824_, v___x_2833_);
lean_dec(v_x_2824_);
v___x_2835_ = lean_unsigned_to_nat(2u);
v___x_2836_ = lean_mk_empty_array_with_capacity(v___x_2835_);
v___x_2837_ = lean_array_push(v___x_2836_, v_evalVerTk_2832_);
v___x_2838_ = lean_array_push(v___x_2837_, v___x_2834_);
v___x_2839_ = l_Lean_Fmt_fmtAppLike(v___x_2838_, v_a_2825_, v_a_2826_);
return v___x_2839_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtEvalVer___boxed(lean_object* v_x_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lake_Formatters_fmtEvalVer(v_x_2840_, v_a_2841_, v_a_2842_);
lean_dec_ref(v_a_2841_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1(){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2850_ = l_Lean_Fmt_fmtAttribute;
v___x_2851_ = ((lean_object*)(l_Lake_Formatters_fmtEvalVer___closed__1));
v___x_2852_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___closed__1));
v___x_2853_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtEvalVer___boxed), 3, 0);
v___x_2854_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2850_, v___x_2851_, v___x_2852_, v___x_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1___boxed(lean_object* v_a_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1();
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtVerLit(lean_object* v_x_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v___x_2868_; uint8_t v___x_2869_; 
v___x_2868_ = ((lean_object*)(l_Lake_Formatters_fmtVerLit___closed__1));
lean_inc(v_x_2865_);
v___x_2869_ = l_Lean_Syntax_isOfKind(v_x_2865_, v___x_2868_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec(v_x_2865_);
v___x_2870_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
lean_ctor_set(v___x_2871_, 1, v_a_2867_);
return v___x_2871_;
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2872_ = lean_unsigned_to_nat(1u);
v___x_2873_ = l_Lean_Syntax_getArg(v_x_2865_, v___x_2872_);
v___x_2874_ = ((lean_object*)(l_Lake_Formatters_fmtVerLit___closed__3));
lean_inc(v___x_2873_);
v___x_2875_ = l_Lean_Syntax_isOfKind(v___x_2873_, v___x_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec(v___x_2873_);
lean_dec(v_x_2865_);
v___x_2876_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v_a_2867_);
return v___x_2877_;
}
else
{
lean_object* v___x_2878_; lean_object* v_verTk_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_unsigned_to_nat(0u);
v_verTk_2879_ = l_Lean_Syntax_getArg(v_x_2865_, v___x_2878_);
lean_dec(v_x_2865_);
v___x_2880_ = l_Lean_Fmt_fmt(v_verTk_2879_, v_a_2866_, v_a_2867_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v_a_2882_; lean_object* v___x_2883_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
v_a_2882_ = lean_ctor_get(v___x_2880_, 1);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2880_, 2);
v___x_2883_ = l_Lean_Fmt_fmt(v___x_2873_, v_a_2866_, v_a_2882_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2893_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
v_a_2885_ = lean_ctor_get(v___x_2883_, 1);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2887_ = v___x_2883_;
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_inc(v_a_2884_);
lean_dec(v___x_2883_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2889_ = l_Lean_Fmt_Layouts_strLit(v_a_2881_, v_a_2884_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2889_);
v___x_2891_ = v___x_2887_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_a_2885_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
else
{
lean_dec(v_a_2881_);
return v___x_2883_;
}
}
else
{
lean_dec(v___x_2873_);
return v___x_2880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtVerLit___boxed(lean_object* v_x_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lake_Formatters_fmtVerLit(v_x_2894_, v_a_2895_, v_a_2896_);
lean_dec_ref(v_a_2895_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1(){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2904_ = l_Lean_Fmt_fmtAttribute;
v___x_2905_ = ((lean_object*)(l_Lake_Formatters_fmtVerLit___closed__1));
v___x_2906_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___closed__1));
v___x_2907_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtVerLit___boxed), 3, 0);
v___x_2908_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2904_, v___x_2905_, v___x_2906_, v___x_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1___boxed(lean_object* v_a_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1();
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFacetSuffix(lean_object* v_x_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = ((lean_object*)(l_Lake_Formatters_fmtFacetSuffix___closed__1));
lean_inc(v_x_2916_);
v___x_2920_ = l_Lean_Syntax_isOfKind(v_x_2916_, v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec(v_x_2916_);
v___x_2921_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
lean_ctor_set(v___x_2922_, 1, v_a_2918_);
return v___x_2922_;
}
else
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2923_ = lean_unsigned_to_nat(1u);
v___x_2924_ = l_Lean_Syntax_getArg(v_x_2916_, v___x_2923_);
v___x_2925_ = ((lean_object*)(l_Lake_Formatters_fmtGetConfig___closed__5));
lean_inc(v___x_2924_);
v___x_2926_ = l_Lean_Syntax_isOfKind(v___x_2924_, v___x_2925_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
lean_dec(v___x_2924_);
lean_dec(v_x_2916_);
v___x_2927_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
lean_ctor_set(v___x_2928_, 1, v_a_2918_);
return v___x_2928_;
}
else
{
lean_object* v___x_2929_; lean_object* v_colonTk_2930_; lean_object* v___x_2931_; 
v___x_2929_ = lean_unsigned_to_nat(0u);
v_colonTk_2930_ = l_Lean_Syntax_getArg(v_x_2916_, v___x_2929_);
lean_dec(v_x_2916_);
v___x_2931_ = l_Lean_Fmt_fmt(v_colonTk_2930_, v_a_2917_, v_a_2918_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v_a_2933_; lean_object* v___x_2934_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
v_a_2933_ = lean_ctor_get(v___x_2931_, 1);
lean_inc(v_a_2933_);
lean_dec_ref_known(v___x_2931_, 2);
v___x_2934_ = l_Lean_Fmt_fmt(v___x_2924_, v_a_2917_, v_a_2933_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2948_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_a_2936_ = lean_ctor_get(v___x_2934_, 1);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2938_ = v___x_2934_;
v_isShared_2939_ = v_isSharedCheck_2948_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2948_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2946_; 
v___x_2940_ = lean_unsigned_to_nat(2u);
v___x_2941_ = lean_mk_empty_array_with_capacity(v___x_2940_);
v___x_2942_ = lean_array_push(v___x_2941_, v_a_2932_);
v___x_2943_ = lean_array_push(v___x_2942_, v_a_2935_);
v___x_2944_ = l_Lean_Fmt_Layouts_atomic(v___x_2943_);
lean_dec_ref(v___x_2943_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2944_);
v___x_2946_ = v___x_2938_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_a_2936_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
else
{
lean_dec(v_a_2932_);
return v___x_2934_;
}
}
else
{
lean_dec(v___x_2924_);
return v___x_2931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFacetSuffix___boxed(lean_object* v_x_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lake_Formatters_fmtFacetSuffix(v_x_2949_, v_a_2950_, v_a_2951_);
lean_dec_ref(v_a_2950_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1(){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2959_ = l_Lean_Fmt_fmtAttribute;
v___x_2960_ = ((lean_object*)(l_Lake_Formatters_fmtFacetSuffix___closed__1));
v___x_2961_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___closed__1));
v___x_2962_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtFacetSuffix___boxed), 3, 0);
v___x_2963_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2959_, v___x_2960_, v___x_2961_, v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1___boxed(lean_object* v_a_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1();
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageTargetLit(lean_object* v_x_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_plusTk_x3f_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3002_ = ((lean_object*)(l_Lake_Formatters_fmtPackageTargetLit___closed__1));
lean_inc(v_x_2971_);
v___x_3003_ = l_Lean_Syntax_isOfKind(v_x_2971_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_dec(v_x_2971_);
v___x_3004_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
lean_ctor_set(v___x_3005_, 1, v_a_2973_);
return v___x_3005_;
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = l_Lean_Syntax_getArg(v_x_2971_, v___x_3006_);
v___x_3008_ = l_Lean_Syntax_isNone(v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3007_);
v___x_3010_ = l_Lean_Syntax_matchesNull(v___x_3007_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec(v___x_3007_);
lean_dec(v_x_2971_);
v___x_3011_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
lean_ctor_set(v___x_3012_, 1, v_a_2973_);
return v___x_3012_;
}
else
{
lean_object* v_plusTk_x3f_3013_; lean_object* v___x_3014_; 
v_plusTk_x3f_3013_ = l_Lean_Syntax_getArg(v___x_3007_, v___x_3006_);
lean_dec(v___x_3007_);
v___x_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3014_, 0, v_plusTk_x3f_3013_);
v_plusTk_x3f_2975_ = v___x_3014_;
v___y_2976_ = v_a_2972_;
v___y_2977_ = v_a_2973_;
goto v___jp_2974_;
}
}
else
{
lean_object* v___x_3015_; 
lean_dec(v___x_3007_);
v___x_3015_ = lean_box(0);
v_plusTk_x3f_2975_ = v___x_3015_;
v___y_2976_ = v_a_2972_;
v___y_2977_ = v_a_2973_;
goto v___jp_2974_;
}
}
v___jp_2974_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2978_ = lean_unsigned_to_nat(1u);
v___x_2979_ = l_Lean_Syntax_getArg(v_x_2971_, v___x_2978_);
lean_dec(v_x_2971_);
v___x_2980_ = ((lean_object*)(l_Lake_Formatters_fmtGetConfig___closed__5));
lean_inc(v___x_2979_);
v___x_2981_ = l_Lean_Syntax_isOfKind(v___x_2979_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
lean_dec(v___x_2979_);
lean_dec(v_plusTk_x3f_2975_);
v___x_2982_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
lean_ctor_set(v___x_2983_, 1, v___y_2977_);
return v___x_2983_;
}
else
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_Fmt_fmt_x3f(v_plusTk_x3f_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v_a_2986_; lean_object* v___x_2987_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
v_a_2986_ = lean_ctor_get(v___x_2984_, 1);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2984_, 2);
v___x_2987_ = l_Lean_Fmt_fmt(v___x_2979_, v___y_2976_, v_a_2986_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3001_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
v_a_2989_ = lean_ctor_get(v___x_2987_, 1);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2991_ = v___x_2987_;
v_isShared_2992_ = v_isSharedCheck_3001_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3001_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2999_; 
v___x_2993_ = lean_unsigned_to_nat(2u);
v___x_2994_ = lean_mk_empty_array_with_capacity(v___x_2993_);
v___x_2995_ = lean_array_push(v___x_2994_, v_a_2985_);
v___x_2996_ = lean_array_push(v___x_2995_, v_a_2988_);
v___x_2997_ = l_Lean_Fmt_Layouts_atomic(v___x_2996_);
lean_dec_ref(v___x_2996_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___x_2997_);
v___x_2999_ = v___x_2991_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2997_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_a_2989_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
else
{
lean_dec(v_a_2985_);
return v___x_2987_;
}
}
else
{
lean_dec(v___x_2979_);
return v___x_2984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageTargetLit___boxed(lean_object* v_x_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lake_Formatters_fmtPackageTargetLit(v_x_3016_, v_a_3017_, v_a_3018_);
lean_dec_ref(v_a_3017_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1(){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3026_ = l_Lean_Fmt_fmtAttribute;
v___x_3027_ = ((lean_object*)(l_Lake_Formatters_fmtPackageTargetLit___closed__1));
v___x_3028_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___closed__1));
v___x_3029_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtPackageTargetLit___boxed), 3, 0);
v___x_3030_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3026_, v___x_3027_, v___x_3028_, v___x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1___boxed(lean_object* v_a_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1();
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtModuleTargetKeyLit_spec__0(size_t v_sz_3033_, size_t v_i_3034_, lean_object* v_bs_3035_){
_start:
{
uint8_t v___x_3036_; 
v___x_3036_ = lean_usize_dec_lt(v_i_3034_, v_sz_3033_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; 
v___x_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3037_, 0, v_bs_3035_);
return v___x_3037_;
}
else
{
lean_object* v_v_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v_v_3038_ = lean_array_uget(v_bs_3035_, v_i_3034_);
v___x_3039_ = ((lean_object*)(l_Lake_Formatters_fmtFacetSuffix___closed__1));
lean_inc(v_v_3038_);
v___x_3040_ = l_Lean_Syntax_isOfKind(v_v_3038_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; 
lean_dec(v_v_3038_);
lean_dec_ref(v_bs_3035_);
v___x_3041_ = lean_box(0);
return v___x_3041_;
}
else
{
lean_object* v___x_3042_; lean_object* v_bs_x27_3043_; size_t v___x_3044_; size_t v___x_3045_; lean_object* v___x_3046_; 
v___x_3042_ = lean_unsigned_to_nat(0u);
v_bs_x27_3043_ = lean_array_uset(v_bs_3035_, v_i_3034_, v___x_3042_);
v___x_3044_ = ((size_t)1ULL);
v___x_3045_ = lean_usize_add(v_i_3034_, v___x_3044_);
v___x_3046_ = lean_array_uset(v_bs_x27_3043_, v_i_3034_, v_v_3038_);
v_i_3034_ = v___x_3045_;
v_bs_3035_ = v___x_3046_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtModuleTargetKeyLit_spec__0___boxed(lean_object* v_sz_3048_, lean_object* v_i_3049_, lean_object* v_bs_3050_){
_start:
{
size_t v_sz_boxed_3051_; size_t v_i_boxed_3052_; lean_object* v_res_3053_; 
v_sz_boxed_3051_ = lean_unbox_usize(v_sz_3048_);
lean_dec(v_sz_3048_);
v_i_boxed_3052_ = lean_unbox_usize(v_i_3049_);
lean_dec(v_i_3049_);
v_res_3053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtModuleTargetKeyLit_spec__0(v_sz_boxed_3051_, v_i_boxed_3052_, v_bs_3050_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleTargetKeyLit(lean_object* v_x_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v___x_3062_; uint8_t v___x_3063_; 
v___x_3062_ = ((lean_object*)(l_Lake_Formatters_fmtModuleTargetKeyLit___closed__1));
lean_inc(v_x_3059_);
v___x_3063_ = l_Lean_Syntax_isOfKind(v_x_3059_, v___x_3062_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec(v_x_3059_);
v___x_3064_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v_a_3061_);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3066_ = lean_unsigned_to_nat(1u);
v___x_3067_ = l_Lean_Syntax_getArg(v_x_3059_, v___x_3066_);
v___x_3068_ = ((lean_object*)(l_Lake_Formatters_fmtGetConfig___closed__5));
lean_inc(v___x_3067_);
v___x_3069_ = l_Lean_Syntax_isOfKind(v___x_3067_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
lean_dec(v___x_3067_);
lean_dec(v_x_3059_);
v___x_3070_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v_a_3061_);
return v___x_3071_;
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; size_t v_sz_3075_; size_t v___x_3076_; lean_object* v___x_3077_; 
v___x_3072_ = lean_unsigned_to_nat(2u);
v___x_3073_ = l_Lean_Syntax_getArg(v_x_3059_, v___x_3072_);
v___x_3074_ = l_Lean_Syntax_getArgs(v___x_3073_);
lean_dec(v___x_3073_);
v_sz_3075_ = lean_array_size(v___x_3074_);
v___x_3076_ = ((size_t)0ULL);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtModuleTargetKeyLit_spec__0(v_sz_3075_, v___x_3076_, v___x_3074_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_dec(v___x_3067_);
lean_dec(v_x_3059_);
v___x_3078_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
lean_ctor_set(v___x_3079_, 1, v_a_3061_);
return v___x_3079_;
}
else
{
lean_object* v_val_3080_; lean_object* v___x_3081_; lean_object* v_keyTk_3082_; lean_object* v___x_3083_; 
v_val_3080_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_val_3080_);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3081_ = lean_unsigned_to_nat(0u);
v_keyTk_3082_ = l_Lean_Syntax_getArg(v_x_3059_, v___x_3081_);
lean_dec(v_x_3059_);
v___x_3083_ = l_Lean_Fmt_fmt(v_keyTk_3082_, v_a_3060_, v_a_3061_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v_a_3085_; lean_object* v___x_3086_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
v_a_3085_ = lean_ctor_get(v___x_3083_, 1);
lean_inc(v_a_3085_);
lean_dec_ref_known(v___x_3083_, 2);
v___x_3086_ = l_Lean_Fmt_fmt(v___x_3067_, v_a_3060_, v_a_3085_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v_a_3088_; lean_object* v___x_3089_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
v_a_3088_ = lean_ctor_get(v___x_3086_, 1);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___x_3086_, 2);
v___x_3089_ = l_Lean_Fmt_fmtArray___redArg(v_val_3080_, v_a_3060_, v_a_3088_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3103_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_a_3091_ = lean_ctor_get(v___x_3089_, 1);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3093_ = v___x_3089_;
v_isShared_3094_ = v_isSharedCheck_3103_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3103_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3095_ = lean_mk_empty_array_with_capacity(v___x_3072_);
v___x_3096_ = lean_array_push(v___x_3095_, v_a_3084_);
v___x_3097_ = lean_array_push(v___x_3096_, v_a_3087_);
v___x_3098_ = l_Array_append___redArg(v___x_3097_, v_a_3090_);
lean_dec(v_a_3090_);
v___x_3099_ = l_Lean_Fmt_Layouts_atomic(v___x_3098_);
lean_dec_ref(v___x_3098_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3099_);
v___x_3101_ = v___x_3093_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_a_3091_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_a_3087_);
lean_dec(v_a_3084_);
v_a_3104_ = lean_ctor_get(v___x_3089_, 0);
v_a_3105_ = lean_ctor_get(v___x_3089_, 1);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3089_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_inc(v_a_3104_);
lean_dec(v___x_3089_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3104_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_dec(v_a_3084_);
lean_dec(v_val_3080_);
return v___x_3086_;
}
}
else
{
lean_dec(v_val_3080_);
lean_dec(v___x_3067_);
return v___x_3083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtModuleTargetKeyLit___boxed(lean_object* v_x_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lake_Formatters_fmtModuleTargetKeyLit(v_x_3113_, v_a_3114_, v_a_3115_);
lean_dec_ref(v_a_3114_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1(){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3123_ = l_Lean_Fmt_fmtAttribute;
v___x_3124_ = ((lean_object*)(l_Lake_Formatters_fmtModuleTargetKeyLit___closed__1));
v___x_3125_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___closed__1));
v___x_3126_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtModuleTargetKeyLit___boxed), 3, 0);
v___x_3127_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3123_, v___x_3124_, v___x_3125_, v___x_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1___boxed(lean_object* v_a_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1();
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageTargetKeyLit(lean_object* v_x_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v___x_3201_ = ((lean_object*)(l_Lake_Formatters_fmtPackageTargetKeyLit___closed__1));
lean_inc(v_x_3135_);
v___x_3202_ = l_Lean_Syntax_isOfKind(v_x_3135_, v___x_3201_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_dec(v_x_3135_);
v___x_3203_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v_a_3137_);
return v___x_3204_;
}
else
{
lean_object* v___x_3205_; lean_object* v_keyTk_3206_; lean_object* v___y_3208_; lean_object* v_slashTk_x3f_3209_; lean_object* v_targetLit_x3f_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___x_3236_; lean_object* v_pkg_x3f_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___x_3256_; uint8_t v___x_3257_; 
v___x_3205_ = lean_unsigned_to_nat(0u);
v_keyTk_3206_ = l_Lean_Syntax_getArg(v_x_3135_, v___x_3205_);
v___x_3236_ = lean_unsigned_to_nat(1u);
v___x_3256_ = l_Lean_Syntax_getArg(v_x_3135_, v___x_3236_);
v___x_3257_ = l_Lean_Syntax_isNone(v___x_3256_);
if (v___x_3257_ == 0)
{
uint8_t v___x_3258_; 
lean_inc(v___x_3256_);
v___x_3258_ = l_Lean_Syntax_matchesNull(v___x_3256_, v___x_3236_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_dec(v___x_3256_);
lean_dec(v_keyTk_3206_);
lean_dec(v_x_3135_);
v___x_3259_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
lean_ctor_set(v___x_3260_, 1, v_a_3137_);
return v___x_3260_;
}
else
{
lean_object* v_pkg_x3f_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v_pkg_x3f_3261_ = l_Lean_Syntax_getArg(v___x_3256_, v___x_3205_);
lean_dec(v___x_3256_);
v___x_3262_ = ((lean_object*)(l_Lake_Formatters_fmtGetConfig___closed__5));
lean_inc(v_pkg_x3f_3261_);
v___x_3263_ = l_Lean_Syntax_isOfKind(v_pkg_x3f_3261_, v___x_3262_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_dec(v_pkg_x3f_3261_);
lean_dec(v_keyTk_3206_);
lean_dec(v_x_3135_);
v___x_3264_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set(v___x_3265_, 1, v_a_3137_);
return v___x_3265_;
}
else
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_pkg_x3f_3261_);
v_pkg_x3f_3238_ = v___x_3266_;
v___y_3239_ = v_a_3136_;
v___y_3240_ = v_a_3137_;
goto v___jp_3237_;
}
}
}
else
{
lean_object* v___x_3267_; 
lean_dec(v___x_3256_);
v___x_3267_ = lean_box(0);
v_pkg_x3f_3238_ = v___x_3267_;
v___y_3239_ = v_a_3136_;
v___y_3240_ = v_a_3137_;
goto v___jp_3237_;
}
v___jp_3207_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; size_t v_sz_3216_; size_t v___x_3217_; lean_object* v___x_3218_; 
v___x_3213_ = lean_unsigned_to_nat(3u);
v___x_3214_ = l_Lean_Syntax_getArg(v_x_3135_, v___x_3213_);
lean_dec(v_x_3135_);
v___x_3215_ = l_Lean_Syntax_getArgs(v___x_3214_);
lean_dec(v___x_3214_);
v_sz_3216_ = lean_array_size(v___x_3215_);
v___x_3217_ = ((size_t)0ULL);
v___x_3218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Formatters_fmtModuleTargetKeyLit_spec__0(v_sz_3216_, v___x_3217_, v___x_3215_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
lean_dec(v_targetLit_x3f_3210_);
lean_dec(v_slashTk_x3f_3209_);
lean_dec(v___y_3208_);
lean_dec(v_keyTk_3206_);
v___x_3219_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
lean_ctor_set(v___x_3220_, 1, v___y_3212_);
return v___x_3220_;
}
else
{
lean_object* v_val_3221_; lean_object* v___x_3222_; 
v_val_3221_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_val_3221_);
lean_dec_ref_known(v___x_3218_, 1);
v___x_3222_ = l_Lean_Fmt_fmt(v_keyTk_3206_, v___y_3211_, v___y_3212_);
if (lean_obj_tag(v___x_3222_) == 0)
{
if (lean_obj_tag(v___y_3208_) == 0)
{
lean_object* v_a_3223_; lean_object* v_a_3224_; lean_object* v___x_3225_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_a_3223_);
v_a_3224_ = lean_ctor_get(v___x_3222_, 1);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3222_, 2);
v___x_3225_ = lean_box(0);
v___y_3177_ = v_slashTk_x3f_3209_;
v___y_3178_ = v_targetLit_x3f_3210_;
v___y_3179_ = v_a_3223_;
v___y_3180_ = v_a_3224_;
v___y_3181_ = v___y_3211_;
v___y_3182_ = v_val_3221_;
v___y_3183_ = v___x_3225_;
goto v___jp_3176_;
}
else
{
lean_object* v_a_3226_; lean_object* v_a_3227_; lean_object* v_val_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
v_a_3226_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_a_3226_);
v_a_3227_ = lean_ctor_get(v___x_3222_, 1);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3222_, 2);
v_val_3228_ = lean_ctor_get(v___y_3208_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___y_3208_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___y_3208_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_val_3228_);
lean_dec(v___y_3208_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_val_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
v___y_3177_ = v_slashTk_x3f_3209_;
v___y_3178_ = v_targetLit_x3f_3210_;
v___y_3179_ = v_a_3226_;
v___y_3180_ = v_a_3227_;
v___y_3181_ = v___y_3211_;
v___y_3182_ = v_val_3221_;
v___y_3183_ = v___x_3233_;
goto v___jp_3176_;
}
}
}
}
else
{
lean_dec(v_val_3221_);
lean_dec(v_targetLit_x3f_3210_);
lean_dec(v_slashTk_x3f_3209_);
lean_dec(v___y_3208_);
return v___x_3222_;
}
}
}
v___jp_3237_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3241_ = lean_unsigned_to_nat(2u);
v___x_3242_ = l_Lean_Syntax_getArg(v_x_3135_, v___x_3241_);
v___x_3243_ = l_Lean_Syntax_isNone(v___x_3242_);
if (v___x_3243_ == 0)
{
uint8_t v___x_3244_; 
lean_inc(v___x_3242_);
v___x_3244_ = l_Lean_Syntax_matchesNull(v___x_3242_, v___x_3241_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
lean_dec(v___x_3242_);
lean_dec(v_pkg_x3f_3238_);
lean_dec(v_keyTk_3206_);
lean_dec(v_x_3135_);
v___x_3245_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
lean_ctor_set(v___x_3246_, 1, v___y_3240_);
return v___x_3246_;
}
else
{
lean_object* v_targetLit_x3f_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v_targetLit_x3f_3247_ = l_Lean_Syntax_getArg(v___x_3242_, v___x_3236_);
v___x_3248_ = ((lean_object*)(l_Lake_Formatters_fmtPackageTargetLit___closed__1));
lean_inc(v_targetLit_x3f_3247_);
v___x_3249_ = l_Lean_Syntax_isOfKind(v_targetLit_x3f_3247_, v___x_3248_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_dec(v_targetLit_x3f_3247_);
lean_dec(v___x_3242_);
lean_dec(v_pkg_x3f_3238_);
lean_dec(v_keyTk_3206_);
lean_dec(v_x_3135_);
v___x_3250_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
lean_ctor_set(v___x_3251_, 1, v___y_3240_);
return v___x_3251_;
}
else
{
lean_object* v_slashTk_x3f_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_slashTk_x3f_3252_ = l_Lean_Syntax_getArg(v___x_3242_, v___x_3205_);
lean_dec(v___x_3242_);
v___x_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3253_, 0, v_slashTk_x3f_3252_);
v___x_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3254_, 0, v_targetLit_x3f_3247_);
v___y_3208_ = v_pkg_x3f_3238_;
v_slashTk_x3f_3209_ = v___x_3253_;
v_targetLit_x3f_3210_ = v___x_3254_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___y_3240_;
goto v___jp_3207_;
}
}
}
else
{
lean_object* v___x_3255_; 
lean_dec(v___x_3242_);
v___x_3255_ = lean_box(0);
v___y_3208_ = v_pkg_x3f_3238_;
v_slashTk_x3f_3209_ = v___x_3255_;
v_targetLit_x3f_3210_ = v___x_3255_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___y_3240_;
goto v___jp_3207_;
}
}
}
v___jp_3138_:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_Fmt_fmt_x3f(v___y_3145_, v___y_3143_, v___y_3142_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v_a_3148_; lean_object* v___x_3149_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
v_a_3148_ = lean_ctor_get(v___x_3146_, 1);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3146_, 2);
v___x_3149_ = l_Lean_Fmt_fmtArray___redArg(v___y_3144_, v___y_3143_, v_a_3148_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3166_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
v_a_3151_ = lean_ctor_get(v___x_3149_, 1);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3153_ = v___x_3149_;
v_isShared_3154_ = v_isSharedCheck_3166_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_inc(v_a_3150_);
lean_dec(v___x_3149_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3166_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3155_ = lean_unsigned_to_nat(4u);
v___x_3156_ = lean_mk_empty_array_with_capacity(v___x_3155_);
v___x_3157_ = lean_array_push(v___x_3156_, v___y_3140_);
v___x_3158_ = lean_array_push(v___x_3157_, v___y_3139_);
v___x_3159_ = lean_array_push(v___x_3158_, v___y_3141_);
v___x_3160_ = lean_array_push(v___x_3159_, v_a_3147_);
v___x_3161_ = l_Array_append___redArg(v___x_3160_, v_a_3150_);
lean_dec(v_a_3150_);
v___x_3162_ = l_Lean_Fmt_Layouts_atomic(v___x_3161_);
lean_dec_ref(v___x_3161_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 0, v___x_3162_);
v___x_3164_ = v___x_3153_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_a_3151_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v_a_3147_);
lean_dec_ref(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v___y_3139_);
v_a_3167_ = lean_ctor_get(v___x_3149_, 0);
v_a_3168_ = lean_ctor_get(v___x_3149_, 1);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3149_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_inc(v_a_3167_);
lean_dec(v___x_3149_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3167_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_dec_ref(v___y_3144_);
lean_dec_ref(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v___y_3139_);
return v___x_3146_;
}
}
v___jp_3176_:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_Fmt_fmt_x3f(v___y_3183_, v___y_3181_, v___y_3180_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v_a_3186_; lean_object* v___x_3187_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
v_a_3186_ = lean_ctor_get(v___x_3184_, 1);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3184_, 2);
v___x_3187_ = l_Lean_Fmt_fmt_x3f(v___y_3177_, v___y_3181_, v_a_3186_);
if (lean_obj_tag(v___x_3187_) == 0)
{
if (lean_obj_tag(v___y_3178_) == 0)
{
lean_object* v_a_3188_; lean_object* v_a_3189_; lean_object* v___x_3190_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
v_a_3189_ = lean_ctor_get(v___x_3187_, 1);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3187_, 2);
v___x_3190_ = lean_box(0);
v___y_3139_ = v_a_3185_;
v___y_3140_ = v___y_3179_;
v___y_3141_ = v_a_3188_;
v___y_3142_ = v_a_3189_;
v___y_3143_ = v___y_3181_;
v___y_3144_ = v___y_3182_;
v___y_3145_ = v___x_3190_;
goto v___jp_3138_;
}
else
{
lean_object* v_a_3191_; lean_object* v_a_3192_; lean_object* v_val_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
v_a_3191_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3191_);
v_a_3192_ = lean_ctor_get(v___x_3187_, 1);
lean_inc(v_a_3192_);
lean_dec_ref_known(v___x_3187_, 2);
v_val_3193_ = lean_ctor_get(v___y_3178_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___y_3178_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___y_3178_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_val_3193_);
lean_dec(v___y_3178_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_val_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
v___y_3139_ = v_a_3185_;
v___y_3140_ = v___y_3179_;
v___y_3141_ = v_a_3191_;
v___y_3142_ = v_a_3192_;
v___y_3143_ = v___y_3181_;
v___y_3144_ = v___y_3182_;
v___y_3145_ = v___x_3198_;
goto v___jp_3138_;
}
}
}
}
else
{
lean_dec(v_a_3185_);
lean_dec_ref(v___y_3182_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
return v___x_3187_;
}
}
else
{
lean_dec_ref(v___y_3182_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec(v___y_3177_);
return v___x_3184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtPackageTargetKeyLit___boxed(lean_object* v_x_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lake_Formatters_fmtPackageTargetKeyLit(v_x_3268_, v_a_3269_, v_a_3270_);
lean_dec_ref(v_a_3269_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1(){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3278_ = l_Lean_Fmt_fmtAttribute;
v___x_3279_ = ((lean_object*)(l_Lake_Formatters_fmtPackageTargetKeyLit___closed__1));
v___x_3280_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___closed__1));
v___x_3281_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtPackageTargetKeyLit___boxed), 3, 0);
v___x_3282_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3278_, v___x_3279_, v___x_3280_, v___x_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1___boxed(lean_object* v_a_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1();
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f(lean_object* v_stx_3295_){
_start:
{
lean_object* v___x_3296_; uint8_t v___x_3297_; 
v___x_3296_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__1));
lean_inc(v_stx_3295_);
v___x_3297_ = l_Lean_Syntax_isOfKind(v_stx_3295_, v___x_3296_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; 
lean_dec(v_stx_3295_);
v___x_3298_ = lean_box(0);
return v___x_3298_;
}
else
{
lean_object* v___x_3299_; lean_object* v_thenBranch_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
v___x_3299_ = lean_unsigned_to_nat(4u);
v_thenBranch_3300_ = l_Lean_Syntax_getArg(v_stx_3295_, v___x_3299_);
v___x_3301_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__3));
lean_inc(v_thenBranch_3300_);
v___x_3302_ = l_Lean_Syntax_isOfKind(v_thenBranch_3300_, v___x_3301_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; 
lean_dec(v_thenBranch_3300_);
lean_dec(v_stx_3295_);
v___x_3303_ = lean_box(0);
return v___x_3303_;
}
else
{
lean_object* v___x_3304_; lean_object* v_metaTk_3305_; lean_object* v___x_3306_; lean_object* v_ifTk_3307_; lean_object* v___x_3308_; lean_object* v_cond_3309_; lean_object* v___x_3310_; lean_object* v_thenTk_3311_; lean_object* v_elseTk_x3f_3313_; lean_object* v_elseBranch_x3f_3314_; lean_object* v___x_3317_; lean_object* v___x_3318_; uint8_t v___x_3319_; 
v___x_3304_ = lean_unsigned_to_nat(0u);
v_metaTk_3305_ = l_Lean_Syntax_getArg(v_stx_3295_, v___x_3304_);
v___x_3306_ = lean_unsigned_to_nat(1u);
v_ifTk_3307_ = l_Lean_Syntax_getArg(v_stx_3295_, v___x_3306_);
v___x_3308_ = lean_unsigned_to_nat(2u);
v_cond_3309_ = l_Lean_Syntax_getArg(v_stx_3295_, v___x_3308_);
v___x_3310_ = lean_unsigned_to_nat(3u);
v_thenTk_3311_ = l_Lean_Syntax_getArg(v_stx_3295_, v___x_3310_);
v___x_3317_ = lean_unsigned_to_nat(5u);
v___x_3318_ = l_Lean_Syntax_getArg(v_stx_3295_, v___x_3317_);
lean_dec(v_stx_3295_);
v___x_3319_ = l_Lean_Syntax_isNone(v___x_3318_);
if (v___x_3319_ == 0)
{
uint8_t v___x_3320_; 
lean_inc(v___x_3318_);
v___x_3320_ = l_Lean_Syntax_matchesNull(v___x_3318_, v___x_3308_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; 
lean_dec(v___x_3318_);
lean_dec(v_thenTk_3311_);
lean_dec(v_cond_3309_);
lean_dec(v_ifTk_3307_);
lean_dec(v_metaTk_3305_);
lean_dec(v_thenBranch_3300_);
v___x_3321_ = lean_box(0);
return v___x_3321_;
}
else
{
lean_object* v_elseBranch_x3f_3322_; uint8_t v___x_3323_; 
v_elseBranch_x3f_3322_ = l_Lean_Syntax_getArg(v___x_3318_, v___x_3306_);
lean_inc(v_elseBranch_x3f_3322_);
v___x_3323_ = l_Lean_Syntax_isOfKind(v_elseBranch_x3f_3322_, v___x_3301_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; 
lean_dec(v_elseBranch_x3f_3322_);
lean_dec(v___x_3318_);
lean_dec(v_thenTk_3311_);
lean_dec(v_cond_3309_);
lean_dec(v_ifTk_3307_);
lean_dec(v_metaTk_3305_);
lean_dec(v_thenBranch_3300_);
v___x_3324_ = lean_box(0);
return v___x_3324_;
}
else
{
lean_object* v_elseTk_x3f_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_elseTk_x3f_3325_ = l_Lean_Syntax_getArg(v___x_3318_, v___x_3304_);
lean_dec(v___x_3318_);
v___x_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3326_, 0, v_elseTk_x3f_3325_);
v___x_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3327_, 0, v_elseBranch_x3f_3322_);
v_elseTk_x3f_3313_ = v___x_3326_;
v_elseBranch_x3f_3314_ = v___x_3327_;
goto v___jp_3312_;
}
}
}
else
{
lean_object* v___x_3328_; 
lean_dec(v___x_3318_);
v___x_3328_ = lean_box(0);
v_elseTk_x3f_3313_ = v___x_3328_;
v_elseBranch_x3f_3314_ = v___x_3328_;
goto v___jp_3312_;
}
v___jp_3312_:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3315_, 0, v_metaTk_3305_);
lean_ctor_set(v___x_3315_, 1, v_ifTk_3307_);
lean_ctor_set(v___x_3315_, 2, v_cond_3309_);
lean_ctor_set(v___x_3315_, 3, v_thenTk_3311_);
lean_ctor_set(v___x_3315_, 4, v_thenBranch_3300_);
lean_ctor_set(v___x_3315_, 5, v_elseTk_x3f_3313_);
lean_ctor_set(v___x_3315_, 6, v_elseBranch_x3f_3314_);
v___x_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
return v___x_3316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch_spec__0(size_t v_sz_3329_, size_t v_i_3330_, lean_object* v_bs_3331_){
_start:
{
uint8_t v___x_3332_; 
v___x_3332_ = lean_usize_dec_lt(v_i_3330_, v_sz_3329_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; 
v___x_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3333_, 0, v_bs_3331_);
return v___x_3333_;
}
else
{
lean_object* v_v_3334_; lean_object* v___x_3335_; lean_object* v_bs_x27_3336_; size_t v___x_3337_; size_t v___x_3338_; lean_object* v___x_3339_; 
v_v_3334_ = lean_array_uget(v_bs_3331_, v_i_3330_);
v___x_3335_ = lean_unsigned_to_nat(0u);
v_bs_x27_3336_ = lean_array_uset(v_bs_3331_, v_i_3330_, v___x_3335_);
v___x_3337_ = ((size_t)1ULL);
v___x_3338_ = lean_usize_add(v_i_3330_, v___x_3337_);
v___x_3339_ = lean_array_uset(v_bs_x27_3336_, v_i_3330_, v_v_3334_);
v_i_3330_ = v___x_3338_;
v_bs_3331_ = v___x_3339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch_spec__0___boxed(lean_object* v_sz_3341_, lean_object* v_i_3342_, lean_object* v_bs_3343_){
_start:
{
size_t v_sz_boxed_3344_; size_t v_i_boxed_3345_; lean_object* v_res_3346_; 
v_sz_boxed_3344_ = lean_unbox_usize(v_sz_3341_);
lean_dec(v_sz_3341_);
v_i_boxed_3345_ = lean_unbox_usize(v_i_3342_);
lean_dec(v_i_3342_);
v_res_3346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch_spec__0(v_sz_boxed_3344_, v_i_boxed_3345_, v_bs_3343_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch(lean_object* v_head_3350_, lean_object* v_kwTk_3351_, lean_object* v_branch_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v___x_3355_; uint8_t v___x_3356_; 
v___x_3355_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__3));
lean_inc(v_branch_3352_);
v___x_3356_ = l_Lean_Syntax_isOfKind(v_branch_3352_, v___x_3355_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec(v_branch_3352_);
lean_dec(v_kwTk_3351_);
lean_dec_ref(v_head_3350_);
v___x_3357_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
lean_ctor_set(v___x_3358_, 1, v_a_3354_);
return v___x_3358_;
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3359_ = lean_unsigned_to_nat(0u);
v___x_3360_ = l_Lean_Syntax_getArg(v_branch_3352_, v___x_3359_);
lean_dec(v_branch_3352_);
v___x_3361_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch___closed__1));
lean_inc(v___x_3360_);
v___x_3362_ = l_Lean_Syntax_isOfKind(v___x_3360_, v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; 
lean_inc(v_kwTk_3351_);
v___x_3363_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v_kwTk_3351_, v___x_3356_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v_a_3365_; lean_object* v___x_3366_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
v_a_3365_ = lean_ctor_get(v___x_3363_, 1);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3363_, 2);
v___x_3366_ = l_Lean_Fmt_fmt(v_kwTk_3351_, v_a_3353_, v_a_3365_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v_a_3368_; lean_object* v___x_3369_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
v_a_3368_ = lean_ctor_get(v___x_3366_, 1);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3366_, 2);
v___x_3369_ = l_Lean_Fmt_fmt(v___x_3360_, v_a_3353_, v_a_3368_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3390_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
v_a_3371_ = lean_ctor_get(v___x_3369_, 1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3373_ = v___x_3369_;
v_isShared_3374_ = v_isSharedCheck_3390_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_inc(v_a_3370_);
lean_dec(v___x_3369_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3390_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3375_ = lean_unsigned_to_nat(2u);
v___x_3376_ = lean_mk_empty_array_with_capacity(v___x_3375_);
v___x_3377_ = lean_array_push(v___x_3376_, v_head_3350_);
v___x_3378_ = lean_array_push(v___x_3377_, v_a_3367_);
v___x_3379_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3378_);
lean_dec_ref(v___x_3378_);
v___x_3380_ = lean_unsigned_to_nat(3u);
v___x_3381_ = lean_mk_empty_array_with_capacity(v___x_3380_);
v___x_3382_ = lean_array_push(v___x_3381_, v___x_3379_);
v___x_3383_ = lean_array_push(v___x_3382_, v_a_3364_);
v___x_3384_ = lean_array_push(v___x_3383_, v_a_3370_);
v___x_3385_ = l_Lean_Fmt_Layouts_retainedWhitespace(v___x_3384_);
lean_dec_ref(v___x_3384_);
v___x_3386_ = l_Lean_Fmt_TaggedDoc_nested(v___x_3385_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3386_);
v___x_3388_ = v___x_3373_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3371_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
else
{
lean_dec(v_a_3367_);
lean_dec(v_a_3364_);
lean_dec_ref(v_head_3350_);
return v___x_3369_;
}
}
else
{
lean_dec(v_a_3364_);
lean_dec(v___x_3360_);
lean_dec_ref(v_head_3350_);
return v___x_3366_;
}
}
else
{
lean_dec(v___x_3360_);
lean_dec(v_kwTk_3351_);
lean_dec_ref(v_head_3350_);
return v___x_3363_;
}
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; size_t v_sz_3394_; size_t v___x_3395_; lean_object* v___x_3396_; 
v___x_3391_ = lean_unsigned_to_nat(1u);
v___x_3392_ = l_Lean_Syntax_getArg(v___x_3360_, v___x_3391_);
v___x_3393_ = l_Lean_Syntax_getArgs(v___x_3392_);
lean_dec(v___x_3392_);
v_sz_3394_ = lean_array_size(v___x_3393_);
v___x_3395_ = ((size_t)0ULL);
v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch_spec__0(v_sz_3394_, v___x_3395_, v___x_3393_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v___x_3397_; 
lean_inc(v_kwTk_3351_);
v___x_3397_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v_kwTk_3351_, v___x_3356_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v_a_3399_; lean_object* v___x_3400_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
v_a_3399_ = lean_ctor_get(v___x_3397_, 1);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3397_, 2);
v___x_3400_ = l_Lean_Fmt_fmt(v_kwTk_3351_, v_a_3353_, v_a_3399_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v_a_3402_; lean_object* v___x_3403_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
v_a_3402_ = lean_ctor_get(v___x_3400_, 1);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3400_, 2);
v___x_3403_ = l_Lean_Fmt_fmt(v___x_3360_, v_a_3353_, v_a_3402_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3424_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_a_3405_ = lean_ctor_get(v___x_3403_, 1);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3407_ = v___x_3403_;
v_isShared_3408_ = v_isSharedCheck_3424_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3424_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3409_ = lean_unsigned_to_nat(2u);
v___x_3410_ = lean_mk_empty_array_with_capacity(v___x_3409_);
v___x_3411_ = lean_array_push(v___x_3410_, v_head_3350_);
v___x_3412_ = lean_array_push(v___x_3411_, v_a_3401_);
v___x_3413_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3412_);
lean_dec_ref(v___x_3412_);
v___x_3414_ = lean_unsigned_to_nat(3u);
v___x_3415_ = lean_mk_empty_array_with_capacity(v___x_3414_);
v___x_3416_ = lean_array_push(v___x_3415_, v___x_3413_);
v___x_3417_ = lean_array_push(v___x_3416_, v_a_3398_);
v___x_3418_ = lean_array_push(v___x_3417_, v_a_3404_);
v___x_3419_ = l_Lean_Fmt_Layouts_retainedWhitespace(v___x_3418_);
lean_dec_ref(v___x_3418_);
v___x_3420_ = l_Lean_Fmt_TaggedDoc_nested(v___x_3419_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3420_);
v___x_3422_ = v___x_3407_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_a_3405_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
else
{
lean_dec(v_a_3401_);
lean_dec(v_a_3398_);
lean_dec_ref(v_head_3350_);
return v___x_3403_;
}
}
else
{
lean_dec(v_a_3398_);
lean_dec(v___x_3360_);
lean_dec_ref(v_head_3350_);
return v___x_3400_;
}
}
else
{
lean_dec(v___x_3360_);
lean_dec(v_kwTk_3351_);
lean_dec_ref(v_head_3350_);
return v___x_3397_;
}
}
else
{
lean_object* v_val_3425_; lean_object* v_doTk_3426_; lean_object* v___x_3427_; 
v_val_3425_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_val_3425_);
lean_dec_ref_known(v___x_3396_, 1);
v_doTk_3426_ = l_Lean_Syntax_getArg(v___x_3360_, v___x_3359_);
lean_dec(v___x_3360_);
lean_inc(v_doTk_3426_);
v___x_3427_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v_doTk_3426_, v___x_3356_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v_a_3429_; lean_object* v___x_3430_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
v_a_3429_ = lean_ctor_get(v___x_3427_, 1);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3427_, 2);
v___x_3430_ = l_Lean_Fmt_fmt(v_kwTk_3351_, v_a_3353_, v_a_3429_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v_a_3432_; lean_object* v___x_3433_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
v_a_3432_ = lean_ctor_get(v___x_3430_, 1);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3430_, 2);
v___x_3433_ = l_Lean_Fmt_fmt(v_doTk_3426_, v_a_3353_, v_a_3432_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v_a_3435_; lean_object* v___x_3436_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
v_a_3435_ = lean_ctor_get(v___x_3433_, 1);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3433_, 2);
v___x_3436_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(v_val_3425_, v_a_3353_, v_a_3435_);
lean_dec(v_val_3425_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3456_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
v_a_3438_ = lean_ctor_get(v___x_3436_, 1);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3440_ = v___x_3436_;
v_isShared_3441_ = v_isSharedCheck_3456_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_inc(v_a_3437_);
lean_dec(v___x_3436_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3456_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3442_ = lean_unsigned_to_nat(3u);
v___x_3443_ = lean_mk_empty_array_with_capacity(v___x_3442_);
lean_inc_ref(v___x_3443_);
v___x_3444_ = lean_array_push(v___x_3443_, v_head_3350_);
v___x_3445_ = lean_array_push(v___x_3444_, v_a_3431_);
v___x_3446_ = lean_array_push(v___x_3445_, v_a_3434_);
v___x_3447_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3446_);
lean_dec_ref(v___x_3446_);
v___x_3448_ = lean_array_push(v___x_3443_, v___x_3447_);
v___x_3449_ = lean_array_push(v___x_3448_, v_a_3428_);
v___x_3450_ = lean_array_push(v___x_3449_, v_a_3437_);
v___x_3451_ = l_Lean_Fmt_Layouts_retainedWhitespace(v___x_3450_);
lean_dec_ref(v___x_3450_);
v___x_3452_ = l_Lean_Fmt_TaggedDoc_nested(v___x_3451_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v___x_3452_);
v___x_3454_ = v___x_3440_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_a_3438_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
else
{
lean_dec(v_a_3434_);
lean_dec(v_a_3431_);
lean_dec(v_a_3428_);
lean_dec_ref(v_head_3350_);
return v___x_3436_;
}
}
else
{
lean_dec(v_a_3431_);
lean_dec(v_a_3428_);
lean_dec(v_val_3425_);
lean_dec_ref(v_head_3350_);
return v___x_3433_;
}
}
else
{
lean_dec(v_a_3428_);
lean_dec(v_doTk_3426_);
lean_dec(v_val_3425_);
lean_dec_ref(v_head_3350_);
return v___x_3430_;
}
}
else
{
lean_dec(v_doTk_3426_);
lean_dec(v_val_3425_);
lean_dec(v_kwTk_3351_);
lean_dec_ref(v_head_3350_);
return v___x_3427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch___boxed(lean_object* v_head_3457_, lean_object* v_kwTk_3458_, lean_object* v_branch_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch(v_head_3457_, v_kwTk_3458_, v_branch_3459_, v_a_3460_, v_a_3461_);
lean_dec_ref(v_a_3460_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfChain(lean_object* v_head_3463_, lean_object* v_c_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_metaTk_3467_; lean_object* v_ifTk_3468_; lean_object* v_cond_3469_; lean_object* v_thenTk_3470_; lean_object* v_thenBranch_3471_; lean_object* v_elseTk_x3f_3472_; lean_object* v_elseBranch_x3f_3473_; lean_object* v___x_3474_; 
v_metaTk_3467_ = lean_ctor_get(v_c_3464_, 0);
lean_inc(v_metaTk_3467_);
v_ifTk_3468_ = lean_ctor_get(v_c_3464_, 1);
lean_inc(v_ifTk_3468_);
v_cond_3469_ = lean_ctor_get(v_c_3464_, 2);
lean_inc(v_cond_3469_);
v_thenTk_3470_ = lean_ctor_get(v_c_3464_, 3);
lean_inc(v_thenTk_3470_);
v_thenBranch_3471_ = lean_ctor_get(v_c_3464_, 4);
lean_inc(v_thenBranch_3471_);
v_elseTk_x3f_3472_ = lean_ctor_get(v_c_3464_, 5);
lean_inc(v_elseTk_x3f_3472_);
v_elseBranch_x3f_3473_ = lean_ctor_get(v_c_3464_, 6);
lean_inc(v_elseBranch_x3f_3473_);
lean_dec_ref(v_c_3464_);
v___x_3474_ = l_Lean_Fmt_fmt(v_metaTk_3467_, v_a_3465_, v_a_3466_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v_a_3476_; lean_object* v___x_3477_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
v_a_3476_ = lean_ctor_get(v___x_3474_, 1);
lean_inc(v_a_3476_);
lean_dec_ref_known(v___x_3474_, 2);
v___x_3477_ = l_Lean_Fmt_fmt(v_ifTk_3468_, v_a_3465_, v_a_3476_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v_a_3479_; lean_object* v___x_3480_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
v_a_3479_ = lean_ctor_get(v___x_3477_, 1);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3477_, 2);
v___x_3480_ = l_Lean_Fmt_fmt(v_cond_3469_, v_a_3465_, v_a_3479_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v_a_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
v_a_3482_ = lean_ctor_get(v___x_3480_, 1);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3480_, 2);
v___x_3483_ = lean_unsigned_to_nat(3u);
v___x_3484_ = lean_mk_empty_array_with_capacity(v___x_3483_);
lean_inc_ref(v___x_3484_);
v___x_3485_ = lean_array_push(v___x_3484_, v_head_3463_);
v___x_3486_ = lean_array_push(v___x_3485_, v_a_3475_);
v___x_3487_ = lean_array_push(v___x_3486_, v_a_3478_);
v___x_3488_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3487_);
lean_dec_ref(v___x_3487_);
v___x_3489_ = lean_unsigned_to_nat(2u);
v___x_3490_ = lean_mk_empty_array_with_capacity(v___x_3489_);
lean_inc_ref(v___x_3490_);
v___x_3491_ = lean_array_push(v___x_3490_, v___x_3488_);
v___x_3492_ = lean_array_push(v___x_3491_, v_a_3481_);
v___x_3493_ = 1;
v___x_3494_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtConfigCommand___closed__0));
v___x_3495_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3492_, v___x_3494_);
lean_inc(v_thenBranch_3471_);
v___x_3496_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch(v___x_3495_, v_thenTk_3470_, v_thenBranch_3471_, v_a_3465_, v_a_3482_);
if (lean_obj_tag(v___x_3496_) == 0)
{
if (lean_obj_tag(v_elseTk_x3f_3472_) == 1)
{
if (lean_obj_tag(v_elseBranch_x3f_3473_) == 1)
{
lean_object* v_a_3497_; lean_object* v_a_3498_; lean_object* v_val_3499_; lean_object* v_val_3500_; lean_object* v___x_3501_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
v_a_3498_ = lean_ctor_get(v___x_3496_, 1);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3496_, 2);
v_val_3499_ = lean_ctor_get(v_elseTk_x3f_3472_, 0);
lean_inc(v_val_3499_);
lean_dec_ref_known(v_elseTk_x3f_3472_, 1);
v_val_3500_ = lean_ctor_get(v_elseBranch_x3f_3473_, 0);
lean_inc(v_val_3500_);
lean_dec_ref_known(v_elseBranch_x3f_3473_, 1);
v___x_3501_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v_thenBranch_3471_, v___x_3493_, v_a_3465_, v_a_3498_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v_a_3503_; lean_object* v___y_3505_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
v_a_3503_ = lean_ctor_get(v___x_3501_, 1);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3501_, 2);
v___x_3529_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__3));
lean_inc(v_val_3500_);
v___x_3530_ = l_Lean_Syntax_isOfKind(v_val_3500_, v___x_3529_);
if (v___x_3530_ == 0)
{
lean_dec_ref(v___x_3490_);
v___y_3505_ = v_a_3465_;
goto v___jp_3504_;
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3531_ = lean_unsigned_to_nat(0u);
v___x_3532_ = l_Lean_Syntax_getArg(v_val_3500_, v___x_3531_);
v___x_3533_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f(v___x_3532_);
if (lean_obj_tag(v___x_3533_) == 1)
{
lean_object* v_val_3534_; lean_object* v___x_3535_; 
lean_dec(v_val_3500_);
lean_dec_ref(v___x_3484_);
v_val_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_val_3534_);
lean_dec_ref_known(v___x_3533_, 1);
v___x_3535_ = l_Lean_Fmt_fmt(v_val_3499_, v_a_3465_, v_a_3503_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v_a_3537_; lean_object* v___x_3538_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
v_a_3537_ = lean_ctor_get(v___x_3535_, 1);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3535_, 2);
v___x_3538_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfChain(v_a_3536_, v_val_3534_, v_a_3465_, v_a_3537_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3550_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_a_3540_ = lean_ctor_get(v___x_3538_, 1);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3542_ = v___x_3538_;
v_isShared_3543_ = v_isSharedCheck_3550_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3550_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3544_ = lean_array_push(v___x_3490_, v_a_3497_);
v___x_3545_ = lean_array_push(v___x_3544_, v_a_3502_);
v___x_3546_ = l_Array_append___redArg(v___x_3545_, v_a_3539_);
lean_dec(v_a_3539_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3546_);
v___x_3548_ = v___x_3542_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v_a_3540_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
else
{
lean_dec(v_a_3502_);
lean_dec(v_a_3497_);
lean_dec_ref(v___x_3490_);
return v___x_3538_;
}
}
else
{
lean_object* v_a_3551_; lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
lean_dec(v_val_3534_);
lean_dec(v_a_3502_);
lean_dec(v_a_3497_);
lean_dec_ref(v___x_3490_);
v_a_3551_ = lean_ctor_get(v___x_3535_, 0);
v_a_3552_ = lean_ctor_get(v___x_3535_, 1);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3535_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_inc(v_a_3551_);
lean_dec(v___x_3535_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3551_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
else
{
lean_dec(v___x_3533_);
lean_dec_ref(v___x_3490_);
v___y_3505_ = v_a_3465_;
goto v___jp_3504_;
}
}
v___jp_3504_:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_3507_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfBranch(v___x_3506_, v_val_3499_, v_val_3500_, v___y_3505_, v_a_3503_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3519_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_a_3509_ = lean_ctor_get(v___x_3507_, 1);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3511_ = v___x_3507_;
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3519_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3513_ = lean_array_push(v___x_3484_, v_a_3497_);
v___x_3514_ = lean_array_push(v___x_3513_, v_a_3502_);
v___x_3515_ = lean_array_push(v___x_3514_, v_a_3508_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3515_);
v___x_3517_ = v___x_3511_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_a_3509_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec(v_a_3502_);
lean_dec(v_a_3497_);
lean_dec_ref(v___x_3484_);
v_a_3520_ = lean_ctor_get(v___x_3507_, 0);
v_a_3521_ = lean_ctor_get(v___x_3507_, 1);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3507_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_inc(v_a_3520_);
lean_dec(v___x_3507_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3520_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
else
{
lean_object* v_a_3560_; lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v_val_3500_);
lean_dec(v_val_3499_);
lean_dec(v_a_3497_);
lean_dec_ref(v___x_3490_);
lean_dec_ref(v___x_3484_);
v_a_3560_ = lean_ctor_get(v___x_3501_, 0);
v_a_3561_ = lean_ctor_get(v___x_3501_, 1);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3501_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_inc(v_a_3560_);
lean_dec(v___x_3501_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3560_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3580_; 
lean_dec_ref_known(v_elseTk_x3f_3472_, 1);
lean_dec_ref(v___x_3490_);
lean_dec_ref(v___x_3484_);
lean_dec(v_elseBranch_x3f_3473_);
lean_dec(v_thenBranch_3471_);
v_a_3569_ = lean_ctor_get(v___x_3496_, 0);
v_a_3570_ = lean_ctor_get(v___x_3496_, 1);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3572_ = v___x_3496_;
v_isShared_3573_ = v_isSharedCheck_3580_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_inc(v_a_3569_);
lean_dec(v___x_3496_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3580_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3578_; 
v___x_3574_ = lean_unsigned_to_nat(1u);
v___x_3575_ = lean_mk_empty_array_with_capacity(v___x_3574_);
v___x_3576_ = lean_array_push(v___x_3575_, v_a_3569_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v___x_3576_);
v___x_3578_ = v___x_3572_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_a_3570_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3592_; 
lean_dec_ref(v___x_3490_);
lean_dec_ref(v___x_3484_);
lean_dec(v_elseBranch_x3f_3473_);
lean_dec(v_elseTk_x3f_3472_);
lean_dec(v_thenBranch_3471_);
v_a_3581_ = lean_ctor_get(v___x_3496_, 0);
v_a_3582_ = lean_ctor_get(v___x_3496_, 1);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3584_ = v___x_3496_;
v_isShared_3585_ = v_isSharedCheck_3592_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_inc(v_a_3581_);
lean_dec(v___x_3496_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3592_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3590_; 
v___x_3586_ = lean_unsigned_to_nat(1u);
v___x_3587_ = lean_mk_empty_array_with_capacity(v___x_3586_);
v___x_3588_ = lean_array_push(v___x_3587_, v_a_3581_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3588_);
v___x_3590_ = v___x_3584_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v_a_3582_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec_ref(v___x_3490_);
lean_dec_ref(v___x_3484_);
lean_dec(v_elseBranch_x3f_3473_);
lean_dec(v_elseTk_x3f_3472_);
lean_dec(v_thenBranch_3471_);
v_a_3593_ = lean_ctor_get(v___x_3496_, 0);
v_a_3594_ = lean_ctor_get(v___x_3496_, 1);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3496_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_inc(v_a_3593_);
lean_dec(v___x_3496_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3593_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec(v_a_3478_);
lean_dec(v_a_3475_);
lean_dec(v_elseBranch_x3f_3473_);
lean_dec(v_elseTk_x3f_3472_);
lean_dec(v_thenBranch_3471_);
lean_dec(v_thenTk_3470_);
lean_dec_ref(v_head_3463_);
v_a_3602_ = lean_ctor_get(v___x_3480_, 0);
v_a_3603_ = lean_ctor_get(v___x_3480_, 1);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3480_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_inc(v_a_3602_);
lean_dec(v___x_3480_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3602_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v_a_3475_);
lean_dec(v_elseBranch_x3f_3473_);
lean_dec(v_elseTk_x3f_3472_);
lean_dec(v_thenBranch_3471_);
lean_dec(v_thenTk_3470_);
lean_dec(v_cond_3469_);
lean_dec_ref(v_head_3463_);
v_a_3611_ = lean_ctor_get(v___x_3477_, 0);
v_a_3612_ = lean_ctor_get(v___x_3477_, 1);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3477_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_inc(v_a_3611_);
lean_dec(v___x_3477_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3611_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v_elseBranch_x3f_3473_);
lean_dec(v_elseTk_x3f_3472_);
lean_dec(v_thenBranch_3471_);
lean_dec(v_thenTk_3470_);
lean_dec(v_cond_3469_);
lean_dec(v_ifTk_3468_);
lean_dec_ref(v_head_3463_);
v_a_3620_ = lean_ctor_get(v___x_3474_, 0);
v_a_3621_ = lean_ctor_get(v___x_3474_, 1);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3474_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_inc(v_a_3620_);
lean_dec(v___x_3474_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3620_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfChain___boxed(lean_object* v_head_3629_, lean_object* v_c_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfChain(v_head_3629_, v_c_3630_, v_a_3631_, v_a_3632_);
lean_dec_ref(v_a_3631_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtMetaIf(lean_object* v_stx_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f(v_stx_3634_);
if (lean_obj_tag(v___x_3637_) == 1)
{
lean_object* v_val_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v_val_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_val_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v___x_3639_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_3640_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIfChain(v___x_3639_, v_val_3638_, v_a_3635_, v_a_3636_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3650_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
v_a_3642_ = lean_ctor_get(v___x_3640_, 1);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3644_ = v___x_3640_;
v_isShared_3645_ = v_isSharedCheck_3650_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_inc(v_a_3641_);
lean_dec(v___x_3640_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3650_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3646_ = l_Lean_Fmt_Layouts_retainedWhitespace(v_a_3641_);
lean_dec(v_a_3641_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3646_);
v___x_3648_ = v___x_3644_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_a_3642_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
v_a_3651_ = lean_ctor_get(v___x_3640_, 0);
v_a_3652_ = lean_ctor_get(v___x_3640_, 1);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3640_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_inc(v_a_3651_);
lean_dec(v___x_3640_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3651_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
else
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
lean_dec(v___x_3637_);
v___x_3660_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v_a_3636_);
return v___x_3661_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtMetaIf___boxed(lean_object* v_stx_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lake_Formatters_fmtMetaIf(v_stx_3662_, v_a_3663_, v_a_3664_);
lean_dec_ref(v_a_3663_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1(){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3672_ = l_Lean_Fmt_fmtAttribute;
v___x_3673_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_deconstructMetaIf_x3f___closed__1));
v___x_3674_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___closed__1));
v___x_3675_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtMetaIf___boxed), 3, 0);
v___x_3676_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3672_, v___x_3673_, v___x_3674_, v___x_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1___boxed(lean_object* v_a_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1();
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtRunIO(lean_object* v_x_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v___x_3687_; uint8_t v___x_3688_; 
v___x_3687_ = ((lean_object*)(l_Lake_Formatters_fmtRunIO___closed__1));
lean_inc(v_x_3684_);
v___x_3688_ = l_Lean_Syntax_isOfKind(v_x_3684_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_dec(v_x_3684_);
v___x_3689_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
lean_ctor_set(v___x_3690_, 1, v_a_3686_);
return v___x_3690_;
}
else
{
lean_object* v___x_3691_; lean_object* v_runIOTk_3692_; lean_object* v___x_3693_; 
v___x_3691_ = lean_unsigned_to_nat(0u);
v_runIOTk_3692_ = l_Lean_Syntax_getArg(v_x_3684_, v___x_3691_);
v___x_3693_ = l_Lean_Fmt_fmt(v_runIOTk_3692_, v_a_3685_, v_a_3686_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v_a_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
v_a_3695_ = lean_ctor_get(v___x_3693_, 1);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3693_, 2);
v___x_3696_ = lean_unsigned_to_nat(1u);
v___x_3697_ = l_Lean_Syntax_getArg(v_x_3684_, v___x_3696_);
lean_dec(v_x_3684_);
v___x_3698_ = l_Lean_Fmt_fmt(v___x_3697_, v_a_3685_, v_a_3695_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3709_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_a_3700_ = lean_ctor_get(v___x_3698_, 1);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3702_ = v___x_3698_;
v_isShared_3703_ = v_isSharedCheck_3709_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3709_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
uint8_t v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3707_; 
v___x_3704_ = 1;
v___x_3705_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_3694_, v_a_3699_, v___x_3704_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v___x_3705_);
v___x_3707_ = v___x_3702_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_a_3700_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_dec(v_a_3694_);
return v___x_3698_;
}
}
else
{
lean_dec(v_x_3684_);
return v___x_3693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtRunIO___boxed(lean_object* v_x_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lake_Formatters_fmtRunIO(v_x_3710_, v_a_3711_, v_a_3712_);
lean_dec_ref(v_a_3711_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1(){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3720_ = l_Lean_Fmt_fmtAttribute;
v___x_3721_ = ((lean_object*)(l_Lake_Formatters_fmtRunIO___closed__1));
v___x_3722_ = ((lean_object*)(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___closed__1));
v___x_3723_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtRunIO___boxed), 3, 0);
v___x_3724_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3720_, v___x_3721_, v___x_3722_, v___x_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1___boxed(lean_object* v_a_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1();
return v_res_3726_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lake_Formatters_DSL_DeclUtil(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Formatters_DSL_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Formatters_DSL_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtGetConfig___regBuiltin_Lake_Formatters_fmtGetConfig__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageCommand___regBuiltin_Lake_Formatters_fmtPackageCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanLibCommand___regBuiltin_Lake_Formatters_fmtLeanLibCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLeanExeCommand___regBuiltin_Lake_Formatters_fmtLeanExeCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputFileCommand___regBuiltin_Lake_Formatters_fmtInputFileCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtInputDirCommand___regBuiltin_Lake_Formatters_fmtInputDirCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix = _init_l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix();
lean_mark_persistent(l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_emptyTerminationSuffix);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPostUpdateDecl___regBuiltin_Lake_Formatters_fmtPostUpdateDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromPath___regBuiltin_Lake_Formatters_fmtFromPath__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromGit___regBuiltin_Lake_Formatters_fmtFromGit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromSource___regBuiltin_Lake_Formatters_fmtFromSource__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFromClause___regBuiltin_Lake_Formatters_fmtFromClause__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtWithClause___regBuiltin_Lake_Formatters_fmtWithClause__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtDepName___regBuiltin_Lake_Formatters_fmtDepName__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerSpec___regBuiltin_Lake_Formatters_fmtVerSpec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRequireDecl___regBuiltin_Lake_Formatters_fmtRequireDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleFacetDecl___regBuiltin_Lake_Formatters_fmtModuleFacetDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageFacetDecl___regBuiltin_Lake_Formatters_fmtPackageFacetDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtLibraryFacetDecl___regBuiltin_Lake_Formatters_fmtLibraryFacetDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtTargetCommand___regBuiltin_Lake_Formatters_fmtTargetCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtExternLibCommand___regBuiltin_Lake_Formatters_fmtExternLibCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtCacheServiceCommand___regBuiltin_Lake_Formatters_fmtCacheServiceCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtScriptDecl___regBuiltin_Lake_Formatters_fmtScriptDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtEvalVer___regBuiltin_Lake_Formatters_fmtEvalVer__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtVerLit___regBuiltin_Lake_Formatters_fmtVerLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtFacetSuffix___regBuiltin_Lake_Formatters_fmtFacetSuffix__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetLit___regBuiltin_Lake_Formatters_fmtPackageTargetLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtModuleTargetKeyLit___regBuiltin_Lake_Formatters_fmtModuleTargetKeyLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtPackageTargetKeyLit___regBuiltin_Lake_Formatters_fmtPackageTargetKeyLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtMetaIf___regBuiltin_Lake_Formatters_fmtMetaIf__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_DSL_Syntax_0__Lake_Formatters_fmtRunIO___regBuiltin_Lake_Formatters_fmtRunIO__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Formatters_DSL_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lake_Formatters_DSL_DeclUtil(uint8_t builtin);
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Formatters_DSL_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Formatters_DSL_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Formatters_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Formatters_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Formatters_DSL_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
