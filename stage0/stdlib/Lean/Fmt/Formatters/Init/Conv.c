// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Conv
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Init.Tactics meta import Init.Conv import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSimpLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSeq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_hardNl;
lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtExtractLetsLike___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_fill(lean_object*);
lean_object* l_Lean_Fmt_fmtRwLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtCaseDeclaration___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_collection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
lean_object* l_Lean_Fmt_fmtNextLike___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Fmt_fmtAltsTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtLiftLetsLike(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_infixFmtAttribute;
static const lean_string_object l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtConvSeq1Indented___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtConvSeq1Indented___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtConvSeq1Indented___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l_Lean_Fmt_fmtConvSeq1Indented___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtConvSeq1Indented___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "convSeq1Indented"};
static const lean_object* l_Lean_Fmt_fmtConvSeq1Indented___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvSeq1Indented___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeq1Indented___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeq1Indented___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeq1Indented___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeq1Indented___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__5_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__4_value),LEAN_SCALAR_PTR_LITERAL(249, 35, 202, 76, 198, 168, 114, 30)}};
static const lean_object* l_Lean_Fmt_fmtConvSeq1Indented___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtConvSeq1Indented___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Fmt_fmtConvSeq1Indented___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeq1Indented(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeq1Indented___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtConvSeq1Indented"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 127, 99, 68, 13, 120, 107)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvSeqBracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "convSeqBracketed"};
static const lean_object* l_Lean_Fmt_fmtConvSeqBracketed___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvSeqBracketed___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvSeqBracketed___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeqBracketed___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeqBracketed___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeqBracketed___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeqBracketed___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeqBracketed___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeqBracketed___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeqBracketed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeqBracketed___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvSeqBracketed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 46, 60, 206, 104, 220, 125, 67)}};
static const lean_object* l_Lean_Fmt_fmtConvSeqBracketed___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvSeqBracketed___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeqBracketed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeqBracketed___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtConvSeqBracketed"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 26, 93, 113, 72, 79, 140, 86)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "convSeq"};
static const lean_object* l_Lean_Fmt_fmtConvSeq___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvSeq___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvSeq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeq___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeq___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeq___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeq___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeq___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvSeq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 81, 30, 13, 252, 23, 29, 64)}};
static const lean_object* l_Lean_Fmt_fmtConvSeq___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvSeq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeq___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtConvSeq"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 49, 157, 188, 28, 32, 31, 188)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvOccsIndexed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "occsIndexed"};
static const lean_object* l_Lean_Fmt_fmtConvOccsIndexed___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvOccsIndexed___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvOccsIndexed___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvOccsIndexed___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvOccsIndexed___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvOccsIndexed___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvOccsIndexed___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvOccsIndexed___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvOccsIndexed___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvOccsIndexed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvOccsIndexed___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvOccsIndexed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 79, 250, 218, 138, 32, 121, 144)}};
static const lean_object* l_Lean_Fmt_fmtConvOccsIndexed___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvOccsIndexed___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvOccsIndexed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvOccsIndexed___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtConvOccsIndexed"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 217, 161, 146, 151, 132, 204, 220)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvOccs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "occs"};
static const lean_object* l_Lean_Fmt_fmtConvOccs___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvOccs___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvOccs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvOccs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvOccs___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvOccs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvOccs___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvOccs___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvOccs___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvOccs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvOccs___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvOccs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 84, 10, 70, 31, 153, 125, 43)}};
static const lean_object* l_Lean_Fmt_fmtConvOccs___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvOccs___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvOccs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvOccs___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtConvOccs"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 76, 80, 30, 121, 17, 251, 9)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvArgArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtConvArgArg___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvArgArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvArgArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvArgArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtConvArgArg___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvArgArg___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConvArgArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "argArg"};
static const lean_object* l_Lean_Fmt_fmtConvArgArg___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConvArgArg___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvArgArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvArgArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvArgArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvArgArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvArgArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvArgArg___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvArgArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvArgArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvArgArg___closed__3_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvArgArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(59, 211, 157, 2, 56, 142, 56, 136)}};
static const lean_object* l_Lean_Fmt_fmtConvArgArg___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConvArgArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvArgArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvArgArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtConvArgArg"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 219, 67, 222, 110, 147, 30, 183)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtConvWithAnnotateState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtConvWithAnnotateState___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvWithAnnotateState___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvWithAnnotateState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvWithAnnotateState___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "withAnnotateState"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 133, 126, 96, 213, 194, 239, 44)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtConvWithAnnotateState"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(123, 231, 198, 49, 4, 92, 117, 161)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvArgTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l_Lean_Fmt_fmtConvArgTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvArgTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvArgTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvArgTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvArgTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvArgTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvArgTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvArgTactic___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvArgTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvArgTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvArgTactic___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvArgTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 63, 45, 128, 216, 102, 81, 96)}};
static const lean_object* l_Lean_Fmt_fmtConvArgTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvArgTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvArgTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvArgTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtConvArgTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 7, 40, 94, 141, 246, 2, 63)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Fmt_fmtConvExt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvExt___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvExt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvExt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvExt___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvExt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvExt___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvExt___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvExt___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvExt___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvExt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 59, 213, 100, 231, 162, 190, 80)}};
static const lean_object* l_Lean_Fmt_fmtConvExt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvExt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvExt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtConvExt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 129, 226, 100, 26, 128, 195, 81)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvChange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "change"};
static const lean_object* l_Lean_Fmt_fmtConvChange___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvChange___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvChange___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvChange___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvChange___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvChange___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvChange___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvChange___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvChange___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvChange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvChange___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvChange___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 48, 251, 99, 118, 217, 178, 16)}};
static const lean_object* l_Lean_Fmt_fmtConvChange___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvChange___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvChange(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvChange___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtConvChange"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 117, 93, 177, 31, 116, 216, 134)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvDelta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "delta"};
static const lean_object* l_Lean_Fmt_fmtConvDelta___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvDelta___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvDelta___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDelta___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDelta___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDelta___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDelta___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDelta___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDelta___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDelta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDelta___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvDelta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 217, 17, 26, 4, 182, 95, 121)}};
static const lean_object* l_Lean_Fmt_fmtConvDelta___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvDelta___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDelta(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDelta___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtConvDelta"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 240, 141, 107, 4, 114, 171, 158)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unfold"};
static const lean_object* l_Lean_Fmt_fmtConvUnfold___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvUnfold___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvUnfold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvUnfold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvUnfold___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvUnfold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvUnfold___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvUnfold___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvUnfold___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvUnfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvUnfold___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 13, 86, 191, 228, 222, 83, 199)}};
static const lean_object* l_Lean_Fmt_fmtConvUnfold___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvUnfold___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvUnfold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvUnfold___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtConvUnfold"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 211, 27, 39, 2, 198, 100, 171)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvClear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clear"};
static const lean_object* l_Lean_Fmt_fmtConvClear___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvClear___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvClear___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvClear___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvClear___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvClear___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvClear___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvClear___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvClear___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvClear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvClear___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 78, 175, 7, 2, 107, 214, 173)}};
static const lean_object* l_Lean_Fmt_fmtConvClear___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvClear___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvClear(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvClear___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtConvClear"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 214, 197, 154, 79, 188, 110, 246)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "convIntro___"};
static const lean_object* l_Lean_Fmt_fmtConvIntro___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvIntro___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvIntro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvIntro___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvIntro___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvIntro___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvIntro___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 68, 154, 126, 169, 192, 138, 68)}};
static const lean_object* l_Lean_Fmt_fmtConvIntro___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvIntro___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvIntro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvIntro___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtConvIntro"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 214, 65, 251, 217, 14, 178, 1)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvApply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "convApply_"};
static const lean_object* l_Lean_Fmt_fmtConvApply___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvApply___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvApply___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvApply___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvApply___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvApply___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvApply___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvApply___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvApply___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvApply___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvApply___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvApply___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 7, 29, 82, 157, 206, 45, 91)}};
static const lean_object* l_Lean_Fmt_fmtConvApply___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvApply___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvApply(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvApply___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtConvApply"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 165, 70, 204, 127, 165, 133, 222)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvNestedTacticCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "nestedTacticCore"};
static const lean_object* l_Lean_Fmt_fmtConvNestedTacticCore___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTacticCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTacticCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTacticCore___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTacticCore___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTacticCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 23, 62, 30, 134, 160, 158, 203)}};
static const lean_object* l_Lean_Fmt_fmtConvNestedTacticCore___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConvNestedTacticCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Fmt_fmtConvNestedTacticCore___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTacticCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTacticCore___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTacticCore___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTacticCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Fmt_fmtConvNestedTacticCore___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConvNestedTacticCore___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedTacticCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedTacticCore___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtConvNestedTacticCore"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 148, 184, 191, 29, 110, 112, 207)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvNestedTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedTactic"};
static const lean_object* l_Lean_Fmt_fmtConvNestedTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvNestedTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTactic___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedTactic___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvNestedTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 28, 213, 2, 207, 8, 223, 137)}};
static const lean_object* l_Lean_Fmt_fmtConvNestedTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvNestedTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtConvNestedTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 243, 59, 137, 83, 219, 181, 65)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvTacticInTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "convTactic"};
static const lean_object* l_Lean_Fmt_fmtConvTacticInTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvTacticInTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvTacticInTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTacticInTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTacticInTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTacticInTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTacticInTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTacticInTactic___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTacticInTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTacticInTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTacticInTactic___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvTacticInTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 239, 251, 250, 179, 30, 250, 48)}};
static const lean_object* l_Lean_Fmt_fmtConvTacticInTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvTacticInTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTacticInTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTacticInTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtConvTacticInTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 58, 90, 40, 36, 165, 156, 7)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvConvSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "convConvSeq"};
static const lean_object* l_Lean_Fmt_fmtConvConvSeq___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvConvSeq___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvConvSeq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvConvSeq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvConvSeq___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvConvSeq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvConvSeq___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvConvSeq___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvConvSeq___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvConvSeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvConvSeq___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvConvSeq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 85, 97, 250, 95, 212, 248, 253)}};
static const lean_object* l_Lean_Fmt_fmtConvConvSeq___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvConvSeq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvConvSeq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvConvSeq___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtConvConvSeq"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 207, 79, 26, 94, 69, 200, 182)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvNestedConv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "nestedConv"};
static const lean_object* l_Lean_Fmt_fmtConvNestedConv___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvNestedConv___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedConv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedConv___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedConv___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedConv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedConv___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedConv___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedConv___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNestedConv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNestedConv___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvNestedConv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 174, 232, 149, 164, 188, 109, 191)}};
static const lean_object* l_Lean_Fmt_fmtConvNestedConv___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvNestedConv___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedConv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedConv___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtConvNestedConv"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 44, 246, 253, 45, 113, 88, 16)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Fmt_fmtConvParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvParen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvParen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvParen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvParen___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvParen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvParen___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvParen___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvParen___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvParen___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 172, 52, 155, 88, 222, 189, 57)}};
static const lean_object* l_Lean_Fmt_fmtConvParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvParen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtConvParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 6, 254, 118, 22, 47, 118, 26)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvAllGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l_Lean_Fmt_fmtConvAllGoals___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvAllGoals___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvAllGoals___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvAllGoals___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvAllGoals___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvAllGoals___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvAllGoals___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvAllGoals___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvAllGoals___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvAllGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvAllGoals___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvAllGoals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 55, 182, 70, 128, 26, 115, 15)}};
static const lean_object* l_Lean_Fmt_fmtConvAllGoals___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvAllGoals___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvAllGoals(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvAllGoals___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtConvAllGoals"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 195, 9, 113, 245, 16, 32, 33)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvAnyGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "anyGoals"};
static const lean_object* l_Lean_Fmt_fmtConvAnyGoals___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvAnyGoals___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvAnyGoals___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvAnyGoals___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvAnyGoals___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvAnyGoals___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvAnyGoals___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvAnyGoals___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvAnyGoals___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvAnyGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvAnyGoals___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvAnyGoals___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 41, 143, 75, 238, 57, 26, 246)}};
static const lean_object* l_Lean_Fmt_fmtConvAnyGoals___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvAnyGoals___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvAnyGoals(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvAnyGoals___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtConvAnyGoals"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 241, 7, 158, 2, 89, 79, 212)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvFocus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "focus"};
static const lean_object* l_Lean_Fmt_fmtConvFocus___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvFocus___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvFocus___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFocus___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFocus___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFocus___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFocus___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFocus___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFocus___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFocus___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFocus___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvFocus___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 104, 36, 236, 86, 45, 58, 207)}};
static const lean_object* l_Lean_Fmt_fmtConvFocus___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvFocus___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFocus(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFocus___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtConvFocus"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 45, 182, 213, 244, 173, 107, 180)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvFailIfSuccess___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "failIfSuccess"};
static const lean_object* l_Lean_Fmt_fmtConvFailIfSuccess___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvFailIfSuccess___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvFailIfSuccess___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFailIfSuccess___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFailIfSuccess___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFailIfSuccess___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFailIfSuccess___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFailIfSuccess___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFailIfSuccess___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFailIfSuccess___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFailIfSuccess___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvFailIfSuccess___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 74, 242, 37, 111, 42, 66, 94)}};
static const lean_object* l_Lean_Fmt_fmtConvFailIfSuccess___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvFailIfSuccess___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFailIfSuccess(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFailIfSuccess___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtConvFailIfSuccess"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 22, 242, 52, 246, 45, 130, 179)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvTry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "convTry_"};
static const lean_object* l_Lean_Fmt_fmtConvTry___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvTry___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvTry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTry___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTry___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTry___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTry___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTry___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvTry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 99, 115, 76, 123, 72, 244, 211)}};
static const lean_object* l_Lean_Fmt_fmtConvTry___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvTry___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTry___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtConvTry"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 137, 132, 125, 192, 33, 161, 238)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvRepeat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "convRepeat_"};
static const lean_object* l_Lean_Fmt_fmtConvRepeat___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvRepeat___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvRepeat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRepeat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRepeat___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRepeat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRepeat___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRepeat___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRepeat___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRepeat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRepeat___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 38, 239, 209, 98, 101, 29, 196)}};
static const lean_object* l_Lean_Fmt_fmtConvRepeat___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvRepeat___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRepeat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRepeat___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtConvRepeat"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 221, 186, 152, 53, 84, 80, 18)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvCase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "case"};
static const lean_object* l_Lean_Fmt_fmtConvCase___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvCase___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvCase___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvCase___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvCase___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvCase___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvCase___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvCase___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvCase___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvCase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvCase___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvCase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 23, 91, 126, 214, 77, 25, 163)}};
static const lean_object* l_Lean_Fmt_fmtConvCase___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvCase___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCase(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCase___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtConvCase"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 189, 51, 121, 235, 99, 229, 218)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvCase_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case'"};
static const lean_object* l_Lean_Fmt_fmtConvCase_x27___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvCase_x27___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvCase_x27___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvCase_x27___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvCase_x27___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvCase_x27___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvCase_x27___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvCase_x27___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvCase_x27___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvCase_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvCase_x27___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvCase_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 157, 98, 160, 189, 128, 94, 31)}};
static const lean_object* l_Lean_Fmt_fmtConvCase_x27___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvCase_x27___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCase_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCase_x27___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtConvCase'"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 236, 87, 106, 159, 182, 178, 20)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvNext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "convNext__=>_"};
static const lean_object* l_Lean_Fmt_fmtConvNext___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvNext___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvNext___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNext___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNext___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNext___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNext___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNext___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNext___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvNext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvNext___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvNext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 255, 234, 0, 142, 69, 158, 51)}};
static const lean_object* l_Lean_Fmt_fmtConvNext___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvNext___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNext___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtConvNext"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 245, 20, 217, 186, 31, 159, 39)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvDot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 6, .m_data = "conv·_"};
static const lean_object* l_Lean_Fmt_fmtConvDot___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvDot___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvDot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDot___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDot___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDot___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDot___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvDot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 17, 134, 179, 95, 143, 156, 206)}};
static const lean_object* l_Lean_Fmt_fmtConvDot___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvDot___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDot___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtConvDot"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 179, 175, 34, 152, 219, 0, 14)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtConvSeqFocus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtConvSeqFocus___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvSeqFocus___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvSeqFocus___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSeqFocus___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtConvSeqFocus___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvSeqFocus___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtConvSeqFocus___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtConvSeqFocus___closed__2;
static lean_once_cell_t l_Lean_Fmt_fmtConvSeqFocus___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtConvSeqFocus___closed__3;
static lean_once_cell_t l_Lean_Fmt_fmtConvSeqFocus___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtConvSeqFocus___closed__4;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeqFocus;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "conv_<;>_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 57, 152, 10, 187, 180, 111, 39)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtConvSeqFocus"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 47, 203, 168, 236, 215, 84, 112)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvRw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "convRw__"};
static const lean_object* l_Lean_Fmt_fmtConvRw___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvRw___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 150, 200, 64, 217, 142, 60, 16)}};
static const lean_object* l_Lean_Fmt_fmtConvRw___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvRw___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConvRw___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Fmt_fmtConvRw___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConvRw___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Fmt_fmtConvRw___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConvRw___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtConvRw___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rwRuleSeq"};
static const lean_object* l_Lean_Fmt_fmtConvRw___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtConvRw___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRw___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvRw___closed__4_value),LEAN_SCALAR_PTR_LITERAL(170, 212, 96, 120, 212, 17, 101, 100)}};
static const lean_object* l_Lean_Fmt_fmtConvRw___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtConvRw___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRw(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRw___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtConvRw"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 185, 145, 40, 254, 164, 24, 164)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvErw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "convErw__"};
static const lean_object* l_Lean_Fmt_fmtConvErw___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvErw___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvErw___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvErw___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvErw___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvErw___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvErw___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvErw___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvErw___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvErw___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvErw___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvErw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 240, 248, 235, 235, 171, 22, 12)}};
static const lean_object* l_Lean_Fmt_fmtConvErw___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvErw___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvErw(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvErw___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtConvErw"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 101, 186, 13, 112, 1, 87, 42)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvRewrite___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l_Lean_Fmt_fmtConvRewrite___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvRewrite___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvRewrite___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRewrite___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRewrite___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRewrite___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRewrite___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRewrite___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRewrite___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvRewrite___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvRewrite___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvRewrite___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 123, 122, 14, 133, 216, 210, 10)}};
static const lean_object* l_Lean_Fmt_fmtConvRewrite___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvRewrite___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRewrite(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRewrite___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtConvRewrite"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 229, 24, 127, 139, 230, 47, 14)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Fmt_fmtConvSimp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimp___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 165, 42, 136, 187, 206, 234, 202)}};
static const lean_object* l_Lean_Fmt_fmtConvSimp___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConvSimp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "discharger"};
static const lean_object* l_Lean_Fmt_fmtConvSimp___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvSimp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimp___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(233, 186, 255, 143, 150, 72, 152, 71)}};
static const lean_object* l_Lean_Fmt_fmtConvSimp___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConvSimp___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSimp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSimp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtConvSimp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 252, 2, 233, 12, 44, 163, 131)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvDSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l_Lean_Fmt_fmtConvDSimp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvDSimp___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDSimp___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimp___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDSimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDSimp___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvDSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 35, 2, 104, 74, 78, 120, 9)}};
static const lean_object* l_Lean_Fmt_fmtConvDSimp___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvDSimp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDSimp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDSimp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtConvDSimp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 66, 86, 107, 169, 200, 73, 45)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvSimpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpTrace"};
static const lean_object* l_Lean_Fmt_fmtConvSimpTrace___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvSimpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimpTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 24, 207, 89, 155, 142, 251, 55)}};
static const lean_object* l_Lean_Fmt_fmtConvSimpTrace___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConvSimpTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpArgs"};
static const lean_object* l_Lean_Fmt_fmtConvSimpTrace___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvSimpTrace___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimpTrace___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimpTrace___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvSimpTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 198, 190, 154, 66, 126, 242, 208)}};
static const lean_object* l_Lean_Fmt_fmtConvSimpTrace___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConvSimpTrace___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSimpTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSimpTrace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtConvSimpTrace"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 22, 130, 248, 42, 143, 23, 93)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvDSimpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dsimpTrace"};
static const lean_object* l_Lean_Fmt_fmtConvDSimpTrace___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimpTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 139, 45, 80, 126, 130, 141, 19)}};
static const lean_object* l_Lean_Fmt_fmtConvDSimpTrace___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConvDSimpTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dsimpArgs"};
static const lean_object* l_Lean_Fmt_fmtConvDSimpTrace___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimpTrace___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimpTrace___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimpTrace___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvDSimpTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__3_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 87, 141, 148, 80, 213, 108, 207)}};
static const lean_object* l_Lean_Fmt_fmtConvDSimpTrace___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConvDSimpTrace___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDSimpTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDSimpTrace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtConvDSimpTrace"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 232, 230, 37, 208, 63, 190, 60)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pattern"};
static const lean_object* l_Lean_Fmt_fmtConvPattern___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvPattern___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvPattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvPattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvPattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvPattern___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvPattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvPattern___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvPattern___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvPattern___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 139, 144, 223, 221, 17, 152, 53)}};
static const lean_object* l_Lean_Fmt_fmtConvPattern___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvPattern___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvPattern___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtConvPattern"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 57, 60, 234, 206, 82, 253, 203)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvExtractLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLets"};
static const lean_object* l_Lean_Fmt_fmtConvExtractLets___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvExtractLets___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvExtractLets___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvExtractLets___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvExtractLets___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvExtractLets___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvExtractLets___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvExtractLets___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvExtractLets___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvExtractLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvExtractLets___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 111, 123, 142, 92, 98, 88, 43)}};
static const lean_object* l_Lean_Fmt_fmtConvExtractLets___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvExtractLets___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvExtractLets(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvExtractLets___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtConvExtractLets"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 39, 137, 211, 109, 184, 16, 45)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvLiftLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "liftLets"};
static const lean_object* l_Lean_Fmt_fmtConvLiftLets___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvLiftLets___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvLiftLets___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvLiftLets___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvLiftLets___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvLiftLets___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvLiftLets___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvLiftLets___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvLiftLets___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvLiftLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvLiftLets___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvLiftLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 68, 102, 93, 72, 158, 25, 211)}};
static const lean_object* l_Lean_Fmt_fmtConvLiftLets___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvLiftLets___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvLiftLets(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvLiftLets___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtConvLiftLets"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 52, 98, 79, 152, 142, 128, 116)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvEnterPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "enterPattern"};
static const lean_object* l_Lean_Fmt_fmtConvEnterPattern___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvEnterPattern___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterPattern___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterPattern___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnterPattern___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterPattern___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnterPattern___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterPattern___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnterPattern___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnterPattern___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvEnterPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 190, 181, 104, 228, 19, 208, 104)}};
static const lean_object* l_Lean_Fmt_fmtConvEnterPattern___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvEnterPattern___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnterPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnterPattern___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtConvEnterPattern"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 216, 150, 29, 30, 229, 86, 218)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvEnterArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "enterArg"};
static const lean_object* l_Lean_Fmt_fmtConvEnterArg___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvEnterArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnterArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnterArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnterArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnterArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvEnterArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 39, 81, 184, 62, 123, 191, 109)}};
static const lean_object* l_Lean_Fmt_fmtConvEnterArg___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvEnterArg___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConvEnterArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean_Fmt_fmtConvEnterArg___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConvEnterArg___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnterArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnterArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvEnterArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Lean_Fmt_fmtConvEnterArg___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConvEnterArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnterArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnterArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtConvEnterArg"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 240, 14, 70, 202, 74, 26, 44)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvEnter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "enter"};
static const lean_object* l_Lean_Fmt_fmtConvEnter___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvEnter___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvEnter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnter___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnter___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnter___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnter___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvEnter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvEnter___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvEnter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 212, 211, 21, 88, 173, 115, 108)}};
static const lean_object* l_Lean_Fmt_fmtConvEnter___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvEnter___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConvEnter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtConvEnter___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConvEnter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnter___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtConvEnter"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 3, 147, 49, 3, 164, 162, 16)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvFirst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Lean_Fmt_fmtConvFirst___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvFirst___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvFirst___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFirst___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFirst___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFirst___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFirst___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFirst___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFirst___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvFirst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvFirst___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvFirst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 113, 181, 219, 229, 158, 34, 244)}};
static const lean_object* l_Lean_Fmt_fmtConvFirst___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvFirst___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFirst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFirst___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtConvFirst"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 226, 87, 71, 169, 109, 134, 118)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtConvTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Fmt_fmtConvTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtConvTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTactic___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Fmt_fmtConvTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtConvTactic___closed__1_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtConvTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 39, 103, 162, 58, 5, 181, 114)}};
static const lean_object* l_Lean_Fmt_fmtConvTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtConvTactic___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtConvTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtConvTactic___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtConvTactic___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtConvTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtConvTactic___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtConvTactic___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtConvTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtConvSeq1Indented___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 125, 174, 118, 181, 47, 21, 220)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeq1Indented(lean_object* v_x_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq1Indented___closed__5));
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
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v_convs_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = l_Lean_Syntax_getArg(v_x_13_, v___x_20_);
lean_dec(v_x_13_);
v___x_22_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq1Indented___closed__6));
v_convs_23_ = l_Lean_Syntax_getArgs(v___x_21_);
lean_dec(v___x_21_);
v___x_24_ = lean_box(0);
v___x_25_ = l_Lean_Fmt_fmtSeq___redArg(v___x_22_, v_convs_23_, v___x_24_, v_a_14_, v_a_15_);
lean_dec_ref(v_convs_23_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeq1Indented___boxed(lean_object* v_x_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Fmt_fmtConvSeq1Indented(v_x_26_, v_a_27_, v_a_28_);
lean_dec_ref(v_a_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1(){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_37_ = l_Lean_Fmt_fmtAttribute;
v___x_38_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq1Indented___closed__5));
v___x_39_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___closed__2));
v___x_40_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvSeq1Indented___boxed), 3, 0);
v___x_41_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_37_, v___x_38_, v___x_39_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1___boxed(lean_object* v_a_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1();
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeqBracketed(lean_object* v_x_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeqBracketed___closed__1));
lean_inc(v_x_51_);
v___x_55_ = l_Lean_Syntax_isOfKind(v_x_51_, v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec(v_x_51_);
v___x_56_ = l_Lean_Fmt_Error_partialFormatter;
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v_a_53_);
return v___x_57_;
}
else
{
lean_object* v___x_58_; lean_object* v_lbTk_59_; lean_object* v___x_60_; 
v___x_58_ = lean_unsigned_to_nat(0u);
v_lbTk_59_ = l_Lean_Syntax_getArg(v_x_51_, v___x_58_);
v___x_60_ = l_Lean_Fmt_fmt(v_lbTk_59_, v_a_52_, v_a_53_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v_a_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_convs_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
v_a_62_ = lean_ctor_get(v___x_60_, 1);
lean_inc(v_a_62_);
lean_dec_ref_known(v___x_60_, 2);
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = l_Lean_Syntax_getArg(v_x_51_, v___x_63_);
v___x_65_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq1Indented___closed__6));
v_convs_66_ = l_Lean_Syntax_getArgs(v___x_64_);
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v___x_68_ = l_Lean_Fmt_fmtSeq___redArg(v___x_65_, v_convs_66_, v___x_67_, v_a_52_, v_a_62_);
lean_dec_ref(v_convs_66_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v_a_70_; lean_object* v___x_71_; lean_object* v_rbTk_72_; lean_object* v___x_73_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_a_69_);
v_a_70_ = lean_ctor_get(v___x_68_, 1);
lean_inc(v_a_70_);
lean_dec_ref_known(v___x_68_, 2);
v___x_71_ = lean_unsigned_to_nat(2u);
v_rbTk_72_ = l_Lean_Syntax_getArg(v_x_51_, v___x_71_);
lean_dec(v_x_51_);
v___x_73_ = l_Lean_Fmt_fmt(v_rbTk_72_, v_a_52_, v_a_70_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_86_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_a_75_ = lean_ctor_get(v___x_73_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_86_ == 0)
{
v___x_77_ = v___x_73_;
v_isShared_78_ = v_isSharedCheck_86_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_86_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_79_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_80_ = 1;
v___x_81_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1, v___x_55_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1 + 1, v___x_80_);
v___x_82_ = l_Lean_Fmt_Layouts_bracketed(v_a_61_, v_a_69_, v_a_74_, v___x_81_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_82_);
v___x_84_ = v___x_77_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_a_75_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
else
{
lean_dec(v_a_69_);
lean_dec(v_a_61_);
return v___x_73_;
}
}
else
{
lean_dec(v_a_61_);
lean_dec(v_x_51_);
return v___x_68_;
}
}
else
{
lean_dec(v_x_51_);
return v___x_60_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeqBracketed___boxed(lean_object* v_x_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Fmt_fmtConvSeqBracketed(v_x_87_, v_a_88_, v_a_89_);
lean_dec_ref(v_a_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1(){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_97_ = l_Lean_Fmt_fmtAttribute;
v___x_98_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeqBracketed___closed__1));
v___x_99_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___closed__1));
v___x_100_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvSeqBracketed___boxed), 3, 0);
v___x_101_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_97_, v___x_98_, v___x_99_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1___boxed(lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1();
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeq(lean_object* v_x_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v_x_111_);
v___x_115_ = l_Lean_Syntax_isOfKind(v_x_111_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v_x_111_);
v___x_116_ = l_Lean_Fmt_Error_partialFormatter;
v___x_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_a_113_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = l_Lean_Syntax_getArg(v_x_111_, v___x_118_);
lean_dec(v_x_111_);
v___x_120_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeqBracketed___closed__1));
lean_inc(v___x_119_);
v___x_121_ = l_Lean_Syntax_isOfKind(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq1Indented___closed__5));
lean_inc(v___x_119_);
v___x_123_ = l_Lean_Syntax_isOfKind(v___x_119_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v___x_119_);
v___x_124_ = l_Lean_Fmt_Error_partialFormatter;
v___x_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_a_113_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Fmt_fmt(v___x_119_, v_a_112_, v_a_113_);
return v___x_126_;
}
}
else
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Fmt_fmt(v___x_119_, v_a_112_, v_a_113_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSeq___boxed(lean_object* v_x_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Fmt_fmtConvSeq(v_x_128_, v_a_129_, v_a_130_);
lean_dec_ref(v_a_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1(){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_138_ = l_Lean_Fmt_fmtAttribute;
v___x_139_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
v___x_140_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___closed__1));
v___x_141_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvSeq___boxed), 3, 0);
v___x_142_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_138_, v___x_139_, v___x_140_, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1___boxed(lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1();
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvOccsIndexed(lean_object* v_x_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Fmt_fmtConvOccsIndexed___closed__1));
lean_inc(v_x_152_);
v___x_156_ = l_Lean_Syntax_isOfKind(v_x_152_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_x_152_);
v___x_157_ = l_Lean_Fmt_Error_partialFormatter;
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v_a_154_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_nums_161_; lean_object* v___x_162_; 
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = l_Lean_Syntax_getArg(v_x_152_, v___x_159_);
lean_dec(v_x_152_);
v_nums_161_ = l_Lean_Syntax_getArgs(v___x_160_);
lean_dec(v___x_160_);
v___x_162_ = l_Lean_Fmt_fmtArray___redArg(v_nums_161_, v_a_153_, v_a_154_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_172_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_a_164_ = lean_ctor_get(v___x_162_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_172_ == 0)
{
v___x_166_ = v___x_162_;
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_168_ = l_Lean_Fmt_Layouts_fill(v_a_163_);
lean_dec(v_a_163_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_a_164_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
else
{
lean_object* v_a_173_; lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
v_a_173_ = lean_ctor_get(v___x_162_, 0);
v_a_174_ = lean_ctor_get(v___x_162_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_162_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_inc(v_a_173_);
lean_dec(v___x_162_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_173_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvOccsIndexed___boxed(lean_object* v_x_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Fmt_fmtConvOccsIndexed(v_x_182_, v_a_183_, v_a_184_);
lean_dec_ref(v_a_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1(){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_192_ = l_Lean_Fmt_fmtAttribute;
v___x_193_ = ((lean_object*)(l_Lean_Fmt_fmtConvOccsIndexed___closed__1));
v___x_194_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___closed__1));
v___x_195_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvOccsIndexed___boxed), 3, 0);
v___x_196_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_192_, v___x_193_, v___x_194_, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1___boxed(lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1();
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvOccs(lean_object* v_x_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Fmt_fmtConvOccs___closed__1));
lean_inc(v_x_206_);
v___x_210_ = l_Lean_Syntax_isOfKind(v_x_206_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_x_206_);
v___x_211_ = l_Lean_Fmt_Error_partialFormatter;
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v_a_208_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v_lbTk_214_; lean_object* v___x_215_; lean_object* v_occsTk_216_; lean_object* v___x_217_; lean_object* v_colonEqTk_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_rbTk_222_; lean_object* v___x_223_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v_lbTk_214_ = l_Lean_Syntax_getArg(v_x_206_, v___x_213_);
v___x_215_ = lean_unsigned_to_nat(1u);
v_occsTk_216_ = l_Lean_Syntax_getArg(v_x_206_, v___x_215_);
v___x_217_ = lean_unsigned_to_nat(2u);
v_colonEqTk_218_ = l_Lean_Syntax_getArg(v_x_206_, v___x_217_);
v___x_219_ = lean_unsigned_to_nat(3u);
v___x_220_ = l_Lean_Syntax_getArg(v_x_206_, v___x_219_);
v___x_221_ = lean_unsigned_to_nat(4u);
v_rbTk_222_ = l_Lean_Syntax_getArg(v_x_206_, v___x_221_);
lean_dec(v_x_206_);
v___x_223_ = l_Lean_Fmt_fmtNamedArgumentTerm(v_lbTk_214_, v_occsTk_216_, v_colonEqTk_218_, v___x_220_, v_rbTk_222_, v_a_207_, v_a_208_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvOccs___boxed(lean_object* v_x_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Fmt_fmtConvOccs(v_x_224_, v_a_225_, v_a_226_);
lean_dec_ref(v_a_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1(){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_234_ = l_Lean_Fmt_fmtAttribute;
v___x_235_ = ((lean_object*)(l_Lean_Fmt_fmtConvOccs___closed__1));
v___x_236_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___closed__1));
v___x_237_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvOccs___boxed), 3, 0);
v___x_238_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_234_, v___x_235_, v___x_236_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1___boxed(lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1();
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvArgArg(lean_object* v_x_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___y_255_; lean_object* v_negTk_x3f_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = ((lean_object*)(l_Lean_Fmt_fmtConvArgArg___closed__3));
lean_inc(v_x_251_);
v___x_288_ = l_Lean_Syntax_isOfKind(v_x_251_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_x_251_);
v___x_289_ = l_Lean_Fmt_Error_partialFormatter;
v___x_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_a_253_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; lean_object* v_atTk_x3f_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_305_ = l_Lean_Syntax_getArg(v_x_251_, v___x_291_);
v___x_306_ = l_Lean_Syntax_isNone(v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_305_);
v___x_308_ = l_Lean_Syntax_matchesNull(v___x_305_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v___x_305_);
lean_dec(v_x_251_);
v___x_309_ = l_Lean_Fmt_Error_partialFormatter;
v___x_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v_a_253_);
return v___x_310_;
}
else
{
lean_object* v_atTk_x3f_311_; lean_object* v___x_312_; 
v_atTk_x3f_311_ = l_Lean_Syntax_getArg(v___x_305_, v___x_291_);
lean_dec(v___x_305_);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v_atTk_x3f_311_);
v_atTk_x3f_293_ = v___x_312_;
v___y_294_ = v_a_252_;
v___y_295_ = v_a_253_;
goto v___jp_292_;
}
}
else
{
lean_object* v___x_313_; 
lean_dec(v___x_305_);
v___x_313_ = lean_box(0);
v_atTk_x3f_293_ = v___x_313_;
v___y_294_ = v_a_252_;
v___y_295_ = v_a_253_;
goto v___jp_292_;
}
v___jp_292_:
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = l_Lean_Syntax_getArg(v_x_251_, v___x_296_);
v___x_298_ = l_Lean_Syntax_isNone(v___x_297_);
if (v___x_298_ == 0)
{
uint8_t v___x_299_; 
lean_inc(v___x_297_);
v___x_299_ = l_Lean_Syntax_matchesNull(v___x_297_, v___x_296_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v___x_297_);
lean_dec(v_atTk_x3f_293_);
lean_dec(v_x_251_);
v___x_300_ = l_Lean_Fmt_Error_partialFormatter;
v___x_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___y_295_);
return v___x_301_;
}
else
{
lean_object* v_negTk_x3f_302_; lean_object* v___x_303_; 
v_negTk_x3f_302_ = l_Lean_Syntax_getArg(v___x_297_, v___x_291_);
lean_dec(v___x_297_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v_negTk_x3f_302_);
v___y_255_ = v_atTk_x3f_293_;
v_negTk_x3f_256_ = v___x_303_;
v___y_257_ = v___y_294_;
v___y_258_ = v___y_295_;
goto v___jp_254_;
}
}
else
{
lean_object* v___x_304_; 
lean_dec(v___x_297_);
v___x_304_ = lean_box(0);
v___y_255_ = v_atTk_x3f_293_;
v_negTk_x3f_256_ = v___x_304_;
v___y_257_ = v___y_294_;
v___y_258_ = v___y_295_;
goto v___jp_254_;
}
}
}
v___jp_254_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_259_ = lean_unsigned_to_nat(2u);
v___x_260_ = l_Lean_Syntax_getArg(v_x_251_, v___x_259_);
lean_dec(v_x_251_);
v___x_261_ = ((lean_object*)(l_Lean_Fmt_fmtConvArgArg___closed__1));
lean_inc(v___x_260_);
v___x_262_ = l_Lean_Syntax_isOfKind(v___x_260_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec(v___x_260_);
lean_dec(v_negTk_x3f_256_);
lean_dec(v___y_255_);
v___x_263_ = l_Lean_Fmt_Error_partialFormatter;
v___x_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___y_258_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Fmt_fmt_x3f(v___y_255_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v___x_268_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
v_a_267_ = lean_ctor_get(v___x_265_, 1);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_265_, 2);
v___x_268_ = l_Lean_Fmt_fmt_x3f(v_negTk_x3f_256_, v___y_257_, v_a_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v_a_270_; lean_object* v___x_271_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
v_a_270_ = lean_ctor_get(v___x_268_, 1);
lean_inc(v_a_270_);
lean_dec_ref_known(v___x_268_, 2);
v___x_271_ = l_Lean_Fmt_fmt(v___x_260_, v___y_257_, v_a_270_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_286_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_a_273_ = lean_ctor_get(v___x_271_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_286_ == 0)
{
v___x_275_ = v___x_271_;
v_isShared_276_ = v_isSharedCheck_286_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_286_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_277_ = lean_unsigned_to_nat(3u);
v___x_278_ = lean_mk_empty_array_with_capacity(v___x_277_);
v___x_279_ = lean_array_push(v___x_278_, v_a_266_);
v___x_280_ = lean_array_push(v___x_279_, v_a_269_);
v___x_281_ = lean_array_push(v___x_280_, v_a_272_);
v___x_282_ = l_Lean_Fmt_Layouts_atomic(v___x_281_);
lean_dec_ref(v___x_281_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_282_);
v___x_284_ = v___x_275_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_a_273_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_dec(v_a_269_);
lean_dec(v_a_266_);
return v___x_271_;
}
}
else
{
lean_dec(v_a_266_);
lean_dec(v___x_260_);
return v___x_268_;
}
}
else
{
lean_dec(v___x_260_);
lean_dec(v_negTk_x3f_256_);
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvArgArg___boxed(lean_object* v_x_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Fmt_fmtConvArgArg(v_x_314_, v_a_315_, v_a_316_);
lean_dec_ref(v_a_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1(){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_324_ = l_Lean_Fmt_fmtAttribute;
v___x_325_ = ((lean_object*)(l_Lean_Fmt_fmtConvArgArg___closed__3));
v___x_326_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___closed__1));
v___x_327_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvArgArg___boxed), 3, 0);
v___x_328_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_324_, v___x_325_, v___x_326_, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1___boxed(lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1();
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvWithAnnotateState(lean_object* v_stx_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_334_, v___x_337_, v_a_336_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
v_a_340_ = lean_ctor_get(v___x_338_, 1);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_338_, 2);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_334_, v___x_341_, v_a_340_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v_a_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
v_a_344_ = lean_ctor_get(v___x_342_, 1);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_342_, 2);
v___x_345_ = lean_unsigned_to_nat(2u);
v___x_346_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_334_, v___x_345_, v_a_344_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v_a_348_; lean_object* v___x_349_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
v_a_348_ = lean_ctor_get(v___x_346_, 1);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_346_, 2);
v___x_349_ = l_Lean_Fmt_fmt(v_a_339_, v_a_335_, v_a_348_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v_a_351_; lean_object* v___x_352_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
v_a_351_ = lean_ctor_get(v___x_349_, 1);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_349_, 2);
v___x_352_ = l_Lean_Fmt_fmt(v_a_343_, v_a_335_, v_a_351_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v_a_354_; lean_object* v___x_355_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
v_a_354_ = lean_ctor_get(v___x_352_, 1);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_352_, 2);
v___x_355_ = l_Lean_Fmt_fmt(v_a_347_, v_a_335_, v_a_354_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_371_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_a_357_ = lean_ctor_get(v___x_355_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_371_ == 0)
{
v___x_359_ = v___x_355_;
v_isShared_360_ = v_isSharedCheck_371_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_371_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_361_ = lean_unsigned_to_nat(3u);
v___x_362_ = lean_mk_empty_array_with_capacity(v___x_361_);
v___x_363_ = lean_array_push(v___x_362_, v_a_350_);
v___x_364_ = lean_array_push(v___x_363_, v_a_353_);
v___x_365_ = lean_array_push(v___x_364_, v_a_356_);
v___x_366_ = ((lean_object*)(l_Lean_Fmt_fmtConvWithAnnotateState___closed__0));
v___x_367_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_365_, v___x_366_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_367_);
v___x_369_ = v___x_359_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_a_357_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_dec(v_a_353_);
lean_dec(v_a_350_);
return v___x_355_;
}
}
else
{
lean_dec(v_a_350_);
lean_dec(v_a_347_);
return v___x_352_;
}
}
else
{
lean_dec(v_a_347_);
lean_dec(v_a_343_);
return v___x_349_;
}
}
else
{
lean_object* v_a_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec(v_a_343_);
lean_dec(v_a_339_);
v_a_372_ = lean_ctor_get(v___x_346_, 0);
v_a_373_ = lean_ctor_get(v___x_346_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_346_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_inc(v_a_372_);
lean_dec(v___x_346_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_372_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_a_339_);
v_a_381_ = lean_ctor_get(v___x_342_, 0);
v_a_382_ = lean_ctor_get(v___x_342_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_342_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_inc(v_a_381_);
lean_dec(v___x_342_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_381_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_390_ = lean_ctor_get(v___x_338_, 0);
v_a_391_ = lean_ctor_get(v___x_338_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_338_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_inc(v_a_390_);
lean_dec(v___x_338_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_390_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvWithAnnotateState___boxed(lean_object* v_stx_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Fmt_fmtConvWithAnnotateState(v_stx_399_, v_a_400_, v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_stx_399_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1(){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_416_ = l_Lean_Fmt_fmtAttribute;
v___x_417_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__1));
v___x_418_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___closed__3));
v___x_419_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvWithAnnotateState___boxed), 3, 0);
v___x_420_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_416_, v___x_417_, v___x_418_, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1___boxed(lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1();
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvArgTactic(lean_object* v_x_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lean_Fmt_fmtConvArgTactic___closed__1));
lean_inc(v_x_430_);
v___x_434_ = l_Lean_Syntax_isOfKind(v_x_430_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_x_430_);
v___x_435_ = l_Lean_Fmt_Error_partialFormatter;
v___x_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v_a_432_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = l_Lean_Syntax_getArg(v_x_430_, v___x_437_);
v___x_439_ = ((lean_object*)(l_Lean_Fmt_fmtConvArgArg___closed__3));
lean_inc(v___x_438_);
v___x_440_ = l_Lean_Syntax_isOfKind(v___x_438_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v___x_438_);
lean_dec(v_x_430_);
v___x_441_ = l_Lean_Fmt_Error_partialFormatter;
v___x_442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v_a_432_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v_argTk_444_; lean_object* v___x_445_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v_argTk_444_ = l_Lean_Syntax_getArg(v_x_430_, v___x_443_);
lean_dec(v_x_430_);
v___x_445_ = l_Lean_Fmt_fmt(v_argTk_444_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v_a_447_; lean_object* v___x_448_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
v_a_447_ = lean_ctor_get(v___x_445_, 1);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_445_, 2);
v___x_448_ = l_Lean_Fmt_fmt(v___x_438_, v_a_431_, v_a_447_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_464_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_a_450_ = lean_ctor_get(v___x_448_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_464_ == 0)
{
v___x_452_ = v___x_448_;
v_isShared_453_ = v_isSharedCheck_464_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_464_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_454_ = lean_unsigned_to_nat(2u);
v___x_455_ = lean_mk_empty_array_with_capacity(v___x_454_);
v___x_456_ = lean_array_push(v___x_455_, v_a_446_);
v___x_457_ = lean_array_push(v___x_456_, v_a_449_);
v___x_458_ = 0;
v___x_459_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_459_, 0, v___x_440_);
lean_ctor_set_uint8(v___x_459_, 1, v___x_458_);
lean_ctor_set_uint8(v___x_459_, 2, v___x_458_);
lean_ctor_set_uint8(v___x_459_, 3, v___x_458_);
v___x_460_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_457_, v___x_459_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_460_);
v___x_462_ = v___x_452_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_a_450_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_dec(v_a_446_);
return v___x_448_;
}
}
else
{
lean_dec(v___x_438_);
return v___x_445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvArgTactic___boxed(lean_object* v_x_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Fmt_fmtConvArgTactic(v_x_465_, v_a_466_, v_a_467_);
lean_dec_ref(v_a_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1(){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_475_ = l_Lean_Fmt_fmtAttribute;
v___x_476_ = ((lean_object*)(l_Lean_Fmt_fmtConvArgTactic___closed__1));
v___x_477_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___closed__1));
v___x_478_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvArgTactic___boxed), 3, 0);
v___x_479_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_475_, v___x_476_, v___x_477_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1___boxed(lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1();
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvExt(lean_object* v_x_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Fmt_fmtConvExt___closed__1));
lean_inc(v_x_489_);
v___x_493_ = l_Lean_Syntax_isOfKind(v_x_489_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v_x_489_);
v___x_494_ = l_Lean_Fmt_Error_partialFormatter;
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_a_491_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; lean_object* v_extTk_497_; lean_object* v___x_498_; 
v___x_496_ = lean_unsigned_to_nat(0u);
v_extTk_497_ = l_Lean_Syntax_getArg(v_x_489_, v___x_496_);
v___x_498_ = l_Lean_Fmt_fmt(v_extTk_497_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v_a_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_args_503_; lean_object* v___x_504_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
v_a_500_ = lean_ctor_get(v___x_498_, 1);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_498_, 2);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = l_Lean_Syntax_getArg(v_x_489_, v___x_501_);
lean_dec(v_x_489_);
v_args_503_ = l_Lean_Syntax_getArgs(v___x_502_);
lean_dec(v___x_502_);
v___x_504_ = l_Lean_Fmt_fmtArray___redArg(v_args_503_, v_a_490_, v_a_500_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_519_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_a_506_ = lean_ctor_get(v___x_504_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_519_ == 0)
{
v___x_508_ = v___x_504_;
v_isShared_509_ = v_isSharedCheck_519_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_519_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_510_ = lean_mk_empty_array_with_capacity(v___x_501_);
v___x_511_ = lean_array_push(v___x_510_, v_a_499_);
v___x_512_ = l_Array_append___redArg(v___x_511_, v_a_505_);
lean_dec(v_a_505_);
v___x_513_ = 0;
v___x_514_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_514_, 0, v___x_493_);
lean_ctor_set_uint8(v___x_514_, 1, v___x_513_);
lean_ctor_set_uint8(v___x_514_, 2, v___x_513_);
lean_ctor_set_uint8(v___x_514_, 3, v___x_513_);
v___x_515_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_512_, v___x_514_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_515_);
v___x_517_ = v___x_508_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_a_506_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
else
{
lean_object* v_a_520_; lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec(v_a_499_);
v_a_520_ = lean_ctor_get(v___x_504_, 0);
v_a_521_ = lean_ctor_get(v___x_504_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_504_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_inc(v_a_520_);
lean_dec(v___x_504_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_520_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_a_521_);
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
lean_dec(v_x_489_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvExt___boxed(lean_object* v_x_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Fmt_fmtConvExt(v_x_529_, v_a_530_, v_a_531_);
lean_dec_ref(v_a_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1(){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_539_ = l_Lean_Fmt_fmtAttribute;
v___x_540_ = ((lean_object*)(l_Lean_Fmt_fmtConvExt___closed__1));
v___x_541_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___closed__1));
v___x_542_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvExt___boxed), 3, 0);
v___x_543_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_539_, v___x_540_, v___x_541_, v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1___boxed(lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1();
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvChange(lean_object* v_x_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = ((lean_object*)(l_Lean_Fmt_fmtConvChange___closed__1));
lean_inc(v_x_553_);
v___x_557_ = l_Lean_Syntax_isOfKind(v_x_553_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec(v_x_553_);
v___x_558_ = l_Lean_Fmt_Error_partialFormatter;
v___x_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v_a_555_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v_changeTk_561_; lean_object* v___x_562_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v_changeTk_561_ = l_Lean_Syntax_getArg(v_x_553_, v___x_560_);
v___x_562_ = l_Lean_Fmt_fmt(v_changeTk_561_, v_a_554_, v_a_555_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v_a_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
v_a_564_ = lean_ctor_get(v___x_562_, 1);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_562_, 2);
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = l_Lean_Syntax_getArg(v_x_553_, v___x_565_);
lean_dec(v_x_553_);
v___x_567_ = l_Lean_Fmt_fmt(v___x_566_, v_a_554_, v_a_564_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_583_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_a_569_ = lean_ctor_get(v___x_567_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_583_ == 0)
{
v___x_571_ = v___x_567_;
v_isShared_572_ = v_isSharedCheck_583_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_583_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_573_ = lean_unsigned_to_nat(2u);
v___x_574_ = lean_mk_empty_array_with_capacity(v___x_573_);
v___x_575_ = lean_array_push(v___x_574_, v_a_563_);
v___x_576_ = lean_array_push(v___x_575_, v_a_568_);
v___x_577_ = 0;
v___x_578_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_578_, 0, v___x_557_);
lean_ctor_set_uint8(v___x_578_, 1, v___x_577_);
lean_ctor_set_uint8(v___x_578_, 2, v___x_577_);
lean_ctor_set_uint8(v___x_578_, 3, v___x_577_);
v___x_579_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_576_, v___x_578_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_579_);
v___x_581_ = v___x_571_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_a_569_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
lean_dec(v_a_563_);
return v___x_567_;
}
}
else
{
lean_dec(v_x_553_);
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvChange___boxed(lean_object* v_x_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Fmt_fmtConvChange(v_x_584_, v_a_585_, v_a_586_);
lean_dec_ref(v_a_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1(){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_594_ = l_Lean_Fmt_fmtAttribute;
v___x_595_ = ((lean_object*)(l_Lean_Fmt_fmtConvChange___closed__1));
v___x_596_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___closed__1));
v___x_597_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvChange___boxed), 3, 0);
v___x_598_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_594_, v___x_595_, v___x_596_, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1___boxed(lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1();
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDelta(lean_object* v_x_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean_Fmt_fmtConvDelta___closed__1));
lean_inc(v_x_608_);
v___x_612_ = l_Lean_Syntax_isOfKind(v_x_608_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_x_608_);
v___x_613_ = l_Lean_Fmt_Error_partialFormatter;
v___x_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v_a_610_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; lean_object* v_deltaTk_616_; lean_object* v___x_617_; 
v___x_615_ = lean_unsigned_to_nat(0u);
v_deltaTk_616_ = l_Lean_Syntax_getArg(v_x_608_, v___x_615_);
v___x_617_ = l_Lean_Fmt_fmt(v_deltaTk_616_, v_a_609_, v_a_610_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_ids_622_; lean_object* v___x_623_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
v_a_619_ = lean_ctor_get(v___x_617_, 1);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_617_, 2);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = l_Lean_Syntax_getArg(v_x_608_, v___x_620_);
lean_dec(v_x_608_);
v_ids_622_ = l_Lean_Syntax_getArgs(v___x_621_);
lean_dec(v___x_621_);
v___x_623_ = l_Lean_Fmt_fmtArray___redArg(v_ids_622_, v_a_609_, v_a_619_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_638_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_a_625_ = lean_ctor_get(v___x_623_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_638_ == 0)
{
v___x_627_ = v___x_623_;
v_isShared_628_ = v_isSharedCheck_638_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_638_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_629_ = lean_mk_empty_array_with_capacity(v___x_620_);
v___x_630_ = lean_array_push(v___x_629_, v_a_618_);
v___x_631_ = l_Array_append___redArg(v___x_630_, v_a_624_);
lean_dec(v_a_624_);
v___x_632_ = 0;
v___x_633_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_633_, 0, v___x_612_);
lean_ctor_set_uint8(v___x_633_, 1, v___x_632_);
lean_ctor_set_uint8(v___x_633_, 2, v___x_632_);
lean_ctor_set_uint8(v___x_633_, 3, v___x_632_);
v___x_634_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_631_, v___x_633_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_634_);
v___x_636_ = v___x_627_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_a_625_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
else
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_a_618_);
v_a_639_ = lean_ctor_get(v___x_623_, 0);
v_a_640_ = lean_ctor_get(v___x_623_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_623_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_inc(v_a_639_);
lean_dec(v___x_623_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_639_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_dec(v_x_608_);
return v___x_617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDelta___boxed(lean_object* v_x_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Fmt_fmtConvDelta(v_x_648_, v_a_649_, v_a_650_);
lean_dec_ref(v_a_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1(){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_658_ = l_Lean_Fmt_fmtAttribute;
v___x_659_ = ((lean_object*)(l_Lean_Fmt_fmtConvDelta___closed__1));
v___x_660_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___closed__1));
v___x_661_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvDelta___boxed), 3, 0);
v___x_662_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_658_, v___x_659_, v___x_660_, v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1___boxed(lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1();
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvUnfold(lean_object* v_x_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = ((lean_object*)(l_Lean_Fmt_fmtConvUnfold___closed__1));
lean_inc(v_x_672_);
v___x_676_ = l_Lean_Syntax_isOfKind(v_x_672_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v_x_672_);
v___x_677_ = l_Lean_Fmt_Error_partialFormatter;
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v_a_674_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; lean_object* v_unfoldTk_680_; lean_object* v___x_681_; 
v___x_679_ = lean_unsigned_to_nat(0u);
v_unfoldTk_680_ = l_Lean_Syntax_getArg(v_x_672_, v___x_679_);
v___x_681_ = l_Lean_Fmt_fmt(v_unfoldTk_680_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v_a_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v_ids_686_; lean_object* v___x_687_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
v_a_683_ = lean_ctor_get(v___x_681_, 1);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_681_, 2);
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = l_Lean_Syntax_getArg(v_x_672_, v___x_684_);
lean_dec(v_x_672_);
v_ids_686_ = l_Lean_Syntax_getArgs(v___x_685_);
lean_dec(v___x_685_);
v___x_687_ = l_Lean_Fmt_fmtArray___redArg(v_ids_686_, v_a_673_, v_a_683_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_702_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_a_689_ = lean_ctor_get(v___x_687_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_702_ == 0)
{
v___x_691_ = v___x_687_;
v_isShared_692_ = v_isSharedCheck_702_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_702_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_693_ = lean_mk_empty_array_with_capacity(v___x_684_);
v___x_694_ = lean_array_push(v___x_693_, v_a_682_);
v___x_695_ = l_Array_append___redArg(v___x_694_, v_a_688_);
lean_dec(v_a_688_);
v___x_696_ = 0;
v___x_697_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_697_, 0, v___x_676_);
lean_ctor_set_uint8(v___x_697_, 1, v___x_696_);
lean_ctor_set_uint8(v___x_697_, 2, v___x_696_);
lean_ctor_set_uint8(v___x_697_, 3, v___x_696_);
v___x_698_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_695_, v___x_697_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_698_);
v___x_700_ = v___x_691_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_a_689_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
else
{
lean_object* v_a_703_; lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v_a_682_);
v_a_703_ = lean_ctor_get(v___x_687_, 0);
v_a_704_ = lean_ctor_get(v___x_687_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_687_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_inc(v_a_703_);
lean_dec(v___x_687_);
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
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_703_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_dec(v_x_672_);
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvUnfold___boxed(lean_object* v_x_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Fmt_fmtConvUnfold(v_x_712_, v_a_713_, v_a_714_);
lean_dec_ref(v_a_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1(){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_722_ = l_Lean_Fmt_fmtAttribute;
v___x_723_ = ((lean_object*)(l_Lean_Fmt_fmtConvUnfold___closed__1));
v___x_724_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___closed__1));
v___x_725_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvUnfold___boxed), 3, 0);
v___x_726_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_722_, v___x_723_, v___x_724_, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1___boxed(lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1();
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvClear(lean_object* v_stx_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = ((lean_object*)(l_Lean_Fmt_fmtConvClear___closed__1));
lean_inc(v_stx_736_);
v___x_740_ = l_Lean_Syntax_isOfKind(v_stx_736_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec(v_stx_736_);
v___x_741_ = l_Lean_Fmt_Error_partialFormatter;
v___x_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v_a_738_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_736_, v___x_743_, v_a_738_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v_a_746_; lean_object* v___x_747_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
v_a_746_ = lean_ctor_get(v___x_744_, 1);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_744_, 2);
v___x_747_ = l_Lean_Fmt_fmt(v_a_745_, v_a_737_, v_a_746_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_args_752_; lean_object* v___x_753_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
v_a_749_ = lean_ctor_get(v___x_747_, 1);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_747_, 2);
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = l_Lean_Syntax_getArg(v_stx_736_, v___x_750_);
lean_dec(v_stx_736_);
v_args_752_ = l_Lean_Syntax_getArgs(v___x_751_);
lean_dec(v___x_751_);
v___x_753_ = l_Lean_Fmt_fmtArray___redArg(v_args_752_, v_a_737_, v_a_749_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_768_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_a_755_ = lean_ctor_get(v___x_753_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_768_ == 0)
{
v___x_757_ = v___x_753_;
v_isShared_758_ = v_isSharedCheck_768_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_768_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_759_ = lean_mk_empty_array_with_capacity(v___x_750_);
v___x_760_ = lean_array_push(v___x_759_, v_a_748_);
v___x_761_ = l_Array_append___redArg(v___x_760_, v_a_754_);
lean_dec(v_a_754_);
v___x_762_ = 0;
v___x_763_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_763_, 0, v___x_740_);
lean_ctor_set_uint8(v___x_763_, 1, v___x_762_);
lean_ctor_set_uint8(v___x_763_, 2, v___x_740_);
lean_ctor_set_uint8(v___x_763_, 3, v___x_762_);
v___x_764_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_761_, v___x_763_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_764_);
v___x_766_ = v___x_757_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_a_755_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
else
{
lean_object* v_a_769_; lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_a_748_);
v_a_769_ = lean_ctor_get(v___x_753_, 0);
v_a_770_ = lean_ctor_get(v___x_753_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_753_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_inc(v_a_769_);
lean_dec(v___x_753_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_769_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_dec(v_stx_736_);
return v___x_747_;
}
}
else
{
lean_object* v_a_778_; lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_stx_736_);
v_a_778_ = lean_ctor_get(v___x_744_, 0);
v_a_779_ = lean_ctor_get(v___x_744_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_744_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_inc(v_a_778_);
lean_dec(v___x_744_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_778_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvClear___boxed(lean_object* v_stx_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Fmt_fmtConvClear(v_stx_787_, v_a_788_, v_a_789_);
lean_dec_ref(v_a_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1(){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_797_ = l_Lean_Fmt_fmtAttribute;
v___x_798_ = ((lean_object*)(l_Lean_Fmt_fmtConvClear___closed__1));
v___x_799_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___closed__1));
v___x_800_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvClear___boxed), 3, 0);
v___x_801_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_797_, v___x_798_, v___x_799_, v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1___boxed(lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1();
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvIntro(lean_object* v_x_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_Fmt_fmtConvIntro___closed__1));
lean_inc(v_x_811_);
v___x_815_ = l_Lean_Syntax_isOfKind(v_x_811_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec(v_x_811_);
v___x_816_ = l_Lean_Fmt_Error_partialFormatter;
v___x_817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_a_813_);
return v___x_817_;
}
else
{
lean_object* v___x_818_; lean_object* v_introTk_819_; lean_object* v___x_820_; 
v___x_818_ = lean_unsigned_to_nat(0u);
v_introTk_819_ = l_Lean_Syntax_getArg(v_x_811_, v___x_818_);
v___x_820_ = l_Lean_Fmt_fmt(v_introTk_819_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v_a_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_args_825_; lean_object* v___x_826_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
v_a_822_ = lean_ctor_get(v___x_820_, 1);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_820_, 2);
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = l_Lean_Syntax_getArg(v_x_811_, v___x_823_);
lean_dec(v_x_811_);
v_args_825_ = l_Lean_Syntax_getArgs(v___x_824_);
lean_dec(v___x_824_);
v___x_826_ = l_Lean_Fmt_fmtArray___redArg(v_args_825_, v_a_812_, v_a_822_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_841_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_a_828_ = lean_ctor_get(v___x_826_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_841_ == 0)
{
v___x_830_ = v___x_826_;
v_isShared_831_ = v_isSharedCheck_841_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_841_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_832_ = lean_mk_empty_array_with_capacity(v___x_823_);
v___x_833_ = lean_array_push(v___x_832_, v_a_821_);
v___x_834_ = l_Array_append___redArg(v___x_833_, v_a_827_);
lean_dec(v_a_827_);
v___x_835_ = 0;
v___x_836_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_836_, 0, v___x_815_);
lean_ctor_set_uint8(v___x_836_, 1, v___x_835_);
lean_ctor_set_uint8(v___x_836_, 2, v___x_835_);
lean_ctor_set_uint8(v___x_836_, 3, v___x_835_);
v___x_837_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_834_, v___x_836_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_837_);
v___x_839_ = v___x_830_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_a_828_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v_a_842_; lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_a_821_);
v_a_842_ = lean_ctor_get(v___x_826_, 0);
v_a_843_ = lean_ctor_get(v___x_826_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_826_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_inc(v_a_842_);
lean_dec(v___x_826_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_842_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_dec(v_x_811_);
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvIntro___boxed(lean_object* v_x_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Fmt_fmtConvIntro(v_x_851_, v_a_852_, v_a_853_);
lean_dec_ref(v_a_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1(){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_861_ = l_Lean_Fmt_fmtAttribute;
v___x_862_ = ((lean_object*)(l_Lean_Fmt_fmtConvIntro___closed__1));
v___x_863_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___closed__1));
v___x_864_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvIntro___boxed), 3, 0);
v___x_865_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_861_, v___x_862_, v___x_863_, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1___boxed(lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1();
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvApply(lean_object* v_x_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_Fmt_fmtConvApply___closed__1));
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
lean_object* v___x_882_; lean_object* v_applyTk_883_; lean_object* v___x_884_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v_applyTk_883_ = l_Lean_Syntax_getArg(v_x_875_, v___x_882_);
v___x_884_ = l_Lean_Fmt_fmt(v_applyTk_883_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v_a_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
v_a_886_ = lean_ctor_get(v___x_884_, 1);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_884_, 2);
v___x_887_ = lean_unsigned_to_nat(1u);
v___x_888_ = l_Lean_Syntax_getArg(v_x_875_, v___x_887_);
lean_dec(v_x_875_);
v___x_889_ = l_Lean_Fmt_fmt(v___x_888_, v_a_876_, v_a_886_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_905_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_a_891_ = lean_ctor_get(v___x_889_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_905_ == 0)
{
v___x_893_ = v___x_889_;
v_isShared_894_ = v_isSharedCheck_905_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_905_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_895_ = lean_unsigned_to_nat(2u);
v___x_896_ = lean_mk_empty_array_with_capacity(v___x_895_);
v___x_897_ = lean_array_push(v___x_896_, v_a_885_);
v___x_898_ = lean_array_push(v___x_897_, v_a_890_);
v___x_899_ = 0;
v___x_900_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_900_, 0, v___x_879_);
lean_ctor_set_uint8(v___x_900_, 1, v___x_899_);
lean_ctor_set_uint8(v___x_900_, 2, v___x_899_);
lean_ctor_set_uint8(v___x_900_, 3, v___x_899_);
v___x_901_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_898_, v___x_900_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_901_);
v___x_903_ = v___x_893_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_a_891_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_dec(v_a_885_);
return v___x_889_;
}
}
else
{
lean_dec(v_x_875_);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvApply___boxed(lean_object* v_x_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Fmt_fmtConvApply(v_x_906_, v_a_907_, v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1(){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_916_ = l_Lean_Fmt_fmtAttribute;
v___x_917_ = ((lean_object*)(l_Lean_Fmt_fmtConvApply___closed__1));
v___x_918_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___closed__1));
v___x_919_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvApply___boxed), 3, 0);
v___x_920_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_916_, v___x_917_, v___x_918_, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1___boxed(lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1();
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedTacticCore(lean_object* v_x_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = ((lean_object*)(l_Lean_Fmt_fmtConvNestedTacticCore___closed__1));
lean_inc(v_x_936_);
v___x_940_ = l_Lean_Syntax_isOfKind(v_x_936_, v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v_x_936_);
v___x_941_ = l_Lean_Fmt_Error_partialFormatter;
v___x_942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v_a_938_);
return v___x_942_;
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_943_ = lean_unsigned_to_nat(2u);
v___x_944_ = l_Lean_Syntax_getArg(v_x_936_, v___x_943_);
v___x_945_ = ((lean_object*)(l_Lean_Fmt_fmtConvNestedTacticCore___closed__3));
lean_inc(v___x_944_);
v___x_946_ = l_Lean_Syntax_isOfKind(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec(v___x_944_);
lean_dec(v_x_936_);
v___x_947_ = l_Lean_Fmt_Error_partialFormatter;
v___x_948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v_a_938_);
return v___x_948_;
}
else
{
lean_object* v___x_949_; lean_object* v_tk_950_; lean_object* v___x_951_; 
v___x_949_ = lean_unsigned_to_nat(0u);
v_tk_950_ = l_Lean_Syntax_getArg(v_x_936_, v___x_949_);
v___x_951_ = l_Lean_Fmt_fmt(v_tk_950_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v___x_954_; lean_object* v_arrowTk_955_; lean_object* v___x_956_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
v_a_953_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_951_, 2);
v___x_954_ = lean_unsigned_to_nat(1u);
v_arrowTk_955_ = l_Lean_Syntax_getArg(v_x_936_, v___x_954_);
lean_dec(v_x_936_);
v___x_956_ = l_Lean_Fmt_fmt(v_arrowTk_955_, v_a_937_, v_a_953_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v_a_958_; lean_object* v___x_959_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
v_a_958_ = lean_ctor_get(v___x_956_, 1);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_956_, 2);
v___x_959_ = l_Lean_Fmt_fmt(v___x_944_, v_a_937_, v_a_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_970_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_a_961_ = lean_ctor_get(v___x_959_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_970_ == 0)
{
v___x_963_ = v___x_959_;
v_isShared_964_ = v_isSharedCheck_970_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_970_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_965_ = 0;
v___x_966_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_952_, v_a_957_, v_a_960_, v___x_965_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_966_);
v___x_968_ = v___x_963_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_a_961_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
else
{
lean_dec(v_a_957_);
lean_dec(v_a_952_);
return v___x_959_;
}
}
else
{
lean_dec(v_a_952_);
lean_dec(v___x_944_);
return v___x_956_;
}
}
else
{
lean_dec(v___x_944_);
lean_dec(v_x_936_);
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedTacticCore___boxed(lean_object* v_x_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Fmt_fmtConvNestedTacticCore(v_x_971_, v_a_972_, v_a_973_);
lean_dec_ref(v_a_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1(){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_981_ = l_Lean_Fmt_fmtAttribute;
v___x_982_ = ((lean_object*)(l_Lean_Fmt_fmtConvNestedTacticCore___closed__1));
v___x_983_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___closed__1));
v___x_984_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvNestedTacticCore___boxed), 3, 0);
v___x_985_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_981_, v___x_982_, v___x_983_, v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1___boxed(lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1();
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedTactic(lean_object* v_x_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_Fmt_fmtConvNestedTactic___closed__1));
lean_inc(v_x_995_);
v___x_999_ = l_Lean_Syntax_isOfKind(v_x_995_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec(v_x_995_);
v___x_1000_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_a_997_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1002_ = lean_unsigned_to_nat(2u);
v___x_1003_ = l_Lean_Syntax_getArg(v_x_995_, v___x_1002_);
v___x_1004_ = ((lean_object*)(l_Lean_Fmt_fmtConvNestedTacticCore___closed__3));
lean_inc(v___x_1003_);
v___x_1005_ = l_Lean_Syntax_isOfKind(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec(v___x_1003_);
lean_dec(v_x_995_);
v___x_1006_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v_a_997_);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; lean_object* v_tk_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_unsigned_to_nat(0u);
v_tk_1009_ = l_Lean_Syntax_getArg(v_x_995_, v___x_1008_);
v___x_1010_ = l_Lean_Fmt_fmt(v_tk_1009_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v_arrowTk_1014_; lean_object* v___x_1015_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
v_a_1012_ = lean_ctor_get(v___x_1010_, 1);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1010_, 2);
v___x_1013_ = lean_unsigned_to_nat(1u);
v_arrowTk_1014_ = l_Lean_Syntax_getArg(v_x_995_, v___x_1013_);
lean_dec(v_x_995_);
v___x_1015_ = l_Lean_Fmt_fmt(v_arrowTk_1014_, v_a_996_, v_a_1012_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
v_a_1017_ = lean_ctor_get(v___x_1015_, 1);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1015_, 2);
v___x_1018_ = l_Lean_Fmt_fmt(v___x_1003_, v_a_996_, v_a_1017_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1029_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_a_1020_ = lean_ctor_get(v___x_1018_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1022_ = v___x_1018_;
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1024_ = 0;
v___x_1025_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1011_, v_a_1016_, v_a_1019_, v___x_1024_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1025_);
v___x_1027_ = v___x_1022_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_a_1020_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
else
{
lean_dec(v_a_1016_);
lean_dec(v_a_1011_);
return v___x_1018_;
}
}
else
{
lean_dec(v_a_1011_);
lean_dec(v___x_1003_);
return v___x_1015_;
}
}
else
{
lean_dec(v___x_1003_);
lean_dec(v_x_995_);
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedTactic___boxed(lean_object* v_x_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Fmt_fmtConvNestedTactic(v_x_1030_, v_a_1031_, v_a_1032_);
lean_dec_ref(v_a_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1(){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1040_ = l_Lean_Fmt_fmtAttribute;
v___x_1041_ = ((lean_object*)(l_Lean_Fmt_fmtConvNestedTactic___closed__1));
v___x_1042_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___closed__1));
v___x_1043_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvNestedTactic___boxed), 3, 0);
v___x_1044_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1040_, v___x_1041_, v___x_1042_, v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1___boxed(lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1();
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTacticInTactic(lean_object* v_x_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_Fmt_fmtConvTacticInTactic___closed__1));
lean_inc(v_x_1054_);
v___x_1058_ = l_Lean_Syntax_isOfKind(v_x_1054_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v_x_1054_);
v___x_1059_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v_a_1056_);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1061_ = lean_unsigned_to_nat(2u);
v___x_1062_ = l_Lean_Syntax_getArg(v_x_1054_, v___x_1061_);
v___x_1063_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1062_);
v___x_1064_ = l_Lean_Syntax_isOfKind(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec(v___x_1062_);
lean_dec(v_x_1054_);
v___x_1065_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_a_1056_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; lean_object* v_tk_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_unsigned_to_nat(0u);
v_tk_1068_ = l_Lean_Syntax_getArg(v_x_1054_, v___x_1067_);
v___x_1069_ = l_Lean_Fmt_fmt(v_tk_1068_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v_arrowTk_1073_; lean_object* v___x_1074_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
v_a_1071_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1069_, 2);
v___x_1072_ = lean_unsigned_to_nat(1u);
v_arrowTk_1073_ = l_Lean_Syntax_getArg(v_x_1054_, v___x_1072_);
lean_dec(v_x_1054_);
v___x_1074_ = l_Lean_Fmt_fmt(v_arrowTk_1073_, v_a_1055_, v_a_1071_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v_a_1076_; lean_object* v___x_1077_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
v_a_1076_ = lean_ctor_get(v___x_1074_, 1);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1074_, 2);
v___x_1077_ = l_Lean_Fmt_fmt(v___x_1062_, v_a_1055_, v_a_1076_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1088_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_a_1079_ = lean_ctor_get(v___x_1077_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1081_ = v___x_1077_;
v_isShared_1082_ = v_isSharedCheck_1088_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1088_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1083_ = 0;
v___x_1084_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1070_, v_a_1075_, v_a_1078_, v___x_1083_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1084_);
v___x_1086_ = v___x_1081_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_a_1079_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
else
{
lean_dec(v_a_1075_);
lean_dec(v_a_1070_);
return v___x_1077_;
}
}
else
{
lean_dec(v_a_1070_);
lean_dec(v___x_1062_);
return v___x_1074_;
}
}
else
{
lean_dec(v___x_1062_);
lean_dec(v_x_1054_);
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTacticInTactic___boxed(lean_object* v_x_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Fmt_fmtConvTacticInTactic(v_x_1089_, v_a_1090_, v_a_1091_);
lean_dec_ref(v_a_1090_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1(){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1099_ = l_Lean_Fmt_fmtAttribute;
v___x_1100_ = ((lean_object*)(l_Lean_Fmt_fmtConvTacticInTactic___closed__1));
v___x_1101_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___closed__1));
v___x_1102_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvTacticInTactic___boxed), 3, 0);
v___x_1103_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1099_, v___x_1100_, v___x_1101_, v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1___boxed(lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1();
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvConvSeq(lean_object* v_x_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_Fmt_fmtConvConvSeq___closed__1));
lean_inc(v_x_1113_);
v___x_1117_ = l_Lean_Syntax_isOfKind(v_x_1113_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec(v_x_1113_);
v___x_1118_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v_a_1115_);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1120_ = lean_unsigned_to_nat(2u);
v___x_1121_ = l_Lean_Syntax_getArg(v_x_1113_, v___x_1120_);
v___x_1122_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1121_);
v___x_1123_ = l_Lean_Syntax_isOfKind(v___x_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_dec(v___x_1121_);
lean_dec(v_x_1113_);
v___x_1124_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v_a_1115_);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; lean_object* v_tk_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_unsigned_to_nat(0u);
v_tk_1127_ = l_Lean_Syntax_getArg(v_x_1113_, v___x_1126_);
v___x_1128_ = l_Lean_Fmt_fmt(v_tk_1127_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v_arrowTk_1132_; lean_object* v___x_1133_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
v_a_1130_ = lean_ctor_get(v___x_1128_, 1);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1128_, 2);
v___x_1131_ = lean_unsigned_to_nat(1u);
v_arrowTk_1132_ = l_Lean_Syntax_getArg(v_x_1113_, v___x_1131_);
lean_dec(v_x_1113_);
v___x_1133_ = l_Lean_Fmt_fmt(v_arrowTk_1132_, v_a_1114_, v_a_1130_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v_a_1135_; lean_object* v___x_1136_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
v_a_1135_ = lean_ctor_get(v___x_1133_, 1);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1133_, 2);
v___x_1136_ = l_Lean_Fmt_fmt(v___x_1121_, v_a_1114_, v_a_1135_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1147_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_a_1138_ = lean_ctor_get(v___x_1136_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1140_ = v___x_1136_;
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
uint8_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1142_ = 0;
v___x_1143_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1129_, v_a_1134_, v_a_1137_, v___x_1142_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_a_1138_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_dec(v_a_1134_);
lean_dec(v_a_1129_);
return v___x_1136_;
}
}
else
{
lean_dec(v_a_1129_);
lean_dec(v___x_1121_);
return v___x_1133_;
}
}
else
{
lean_dec(v___x_1121_);
lean_dec(v_x_1113_);
return v___x_1128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvConvSeq___boxed(lean_object* v_x_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_Fmt_fmtConvConvSeq(v_x_1148_, v_a_1149_, v_a_1150_);
lean_dec_ref(v_a_1149_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1(){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1158_ = l_Lean_Fmt_fmtAttribute;
v___x_1159_ = ((lean_object*)(l_Lean_Fmt_fmtConvConvSeq___closed__1));
v___x_1160_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___closed__1));
v___x_1161_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvConvSeq___boxed), 3, 0);
v___x_1162_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1158_, v___x_1159_, v___x_1160_, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1___boxed(lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1();
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedConv(lean_object* v_x_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_Fmt_fmtConvNestedConv___closed__1));
lean_inc(v_x_1172_);
v___x_1176_ = l_Lean_Syntax_isOfKind(v_x_1172_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v_x_1172_);
v___x_1177_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v_a_1174_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = l_Lean_Syntax_getArg(v_x_1172_, v___x_1179_);
lean_dec(v_x_1172_);
v___x_1181_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeqBracketed___closed__1));
lean_inc(v___x_1180_);
v___x_1182_ = l_Lean_Syntax_isOfKind(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec(v___x_1180_);
v___x_1183_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v_a_1174_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_Fmt_fmt(v___x_1180_, v_a_1173_, v_a_1174_);
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNestedConv___boxed(lean_object* v_x_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Fmt_fmtConvNestedConv(v_x_1186_, v_a_1187_, v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1(){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1196_ = l_Lean_Fmt_fmtAttribute;
v___x_1197_ = ((lean_object*)(l_Lean_Fmt_fmtConvNestedConv___closed__1));
v___x_1198_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___closed__1));
v___x_1199_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvNestedConv___boxed), 3, 0);
v___x_1200_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1196_, v___x_1197_, v___x_1198_, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1___boxed(lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1();
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvParen(lean_object* v_x_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = ((lean_object*)(l_Lean_Fmt_fmtConvParen___closed__1));
lean_inc(v_x_1210_);
v___x_1214_ = l_Lean_Syntax_isOfKind(v_x_1210_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec(v_x_1210_);
v___x_1215_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v_a_1212_);
return v___x_1216_;
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1217_ = lean_unsigned_to_nat(1u);
v___x_1218_ = l_Lean_Syntax_getArg(v_x_1210_, v___x_1217_);
v___x_1219_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1218_);
v___x_1220_ = l_Lean_Syntax_isOfKind(v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec(v___x_1218_);
lean_dec(v_x_1210_);
v___x_1221_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v_a_1212_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v_lbTk_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_unsigned_to_nat(0u);
v_lbTk_1224_ = l_Lean_Syntax_getArg(v_x_1210_, v___x_1223_);
v___x_1225_ = l_Lean_Fmt_fmt(v_lbTk_1224_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v_a_1227_; lean_object* v___x_1228_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
v_a_1227_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1225_, 2);
v___x_1228_ = l_Lean_Fmt_fmt(v___x_1218_, v_a_1211_, v_a_1227_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v_a_1230_; lean_object* v___x_1231_; lean_object* v_rbTk_1232_; lean_object* v___x_1233_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
v_a_1230_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1228_, 2);
v___x_1231_ = lean_unsigned_to_nat(2u);
v_rbTk_1232_ = l_Lean_Syntax_getArg(v_x_1210_, v___x_1231_);
lean_dec(v_x_1210_);
v___x_1233_ = l_Lean_Fmt_fmt(v_rbTk_1232_, v_a_1211_, v_a_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1243_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_a_1235_ = lean_ctor_get(v___x_1233_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1237_ = v___x_1233_;
v_isShared_1238_ = v_isSharedCheck_1243_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1243_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = l_Lean_Fmt_Layouts_parenthesizedSeq(v_a_1226_, v_a_1229_, v_a_1234_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_a_1235_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
else
{
lean_dec(v_a_1229_);
lean_dec(v_a_1226_);
return v___x_1233_;
}
}
else
{
lean_dec(v_a_1226_);
lean_dec(v_x_1210_);
return v___x_1228_;
}
}
else
{
lean_dec(v___x_1218_);
lean_dec(v_x_1210_);
return v___x_1225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvParen___boxed(lean_object* v_x_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Fmt_fmtConvParen(v_x_1244_, v_a_1245_, v_a_1246_);
lean_dec_ref(v_a_1245_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1(){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1254_ = l_Lean_Fmt_fmtAttribute;
v___x_1255_ = ((lean_object*)(l_Lean_Fmt_fmtConvParen___closed__1));
v___x_1256_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___closed__1));
v___x_1257_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvParen___boxed), 3, 0);
v___x_1258_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1254_, v___x_1255_, v___x_1256_, v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1___boxed(lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1();
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvAllGoals(lean_object* v_x_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Lean_Fmt_fmtConvAllGoals___closed__1));
lean_inc(v_x_1268_);
v___x_1272_ = l_Lean_Syntax_isOfKind(v_x_1268_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec(v_x_1268_);
v___x_1273_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v_a_1270_);
return v___x_1274_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = l_Lean_Syntax_getArg(v_x_1268_, v___x_1275_);
v___x_1277_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1276_);
v___x_1278_ = l_Lean_Syntax_isOfKind(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec(v___x_1276_);
lean_dec(v_x_1268_);
v___x_1279_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v_a_1270_);
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; lean_object* v_tk_1282_; lean_object* v___x_1283_; 
v___x_1281_ = lean_unsigned_to_nat(0u);
v_tk_1282_ = l_Lean_Syntax_getArg(v_x_1268_, v___x_1281_);
lean_dec(v_x_1268_);
v___x_1283_ = l_Lean_Fmt_fmt(v_tk_1282_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_a_1285_; lean_object* v___x_1286_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
v_a_1285_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1283_, 2);
v___x_1286_ = l_Lean_Fmt_fmt(v___x_1276_, v_a_1269_, v_a_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1297_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_a_1288_ = lean_ctor_get(v___x_1286_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1290_ = v___x_1286_;
v_isShared_1291_ = v_isSharedCheck_1297_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1297_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1292_ = 1;
v___x_1293_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_1284_, v_a_1287_, v___x_1292_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1293_);
v___x_1295_ = v___x_1290_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_a_1288_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
else
{
lean_dec(v_a_1284_);
return v___x_1286_;
}
}
else
{
lean_dec(v___x_1276_);
return v___x_1283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvAllGoals___boxed(lean_object* v_x_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_Fmt_fmtConvAllGoals(v_x_1298_, v_a_1299_, v_a_1300_);
lean_dec_ref(v_a_1299_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1(){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1308_ = l_Lean_Fmt_fmtAttribute;
v___x_1309_ = ((lean_object*)(l_Lean_Fmt_fmtConvAllGoals___closed__1));
v___x_1310_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___closed__1));
v___x_1311_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvAllGoals___boxed), 3, 0);
v___x_1312_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1308_, v___x_1309_, v___x_1310_, v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1___boxed(lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1();
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvAnyGoals(lean_object* v_x_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = ((lean_object*)(l_Lean_Fmt_fmtConvAnyGoals___closed__1));
lean_inc(v_x_1322_);
v___x_1326_ = l_Lean_Syntax_isOfKind(v_x_1322_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec(v_x_1322_);
v___x_1327_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v_a_1324_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = l_Lean_Syntax_getArg(v_x_1322_, v___x_1329_);
v___x_1331_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1330_);
v___x_1332_ = l_Lean_Syntax_isOfKind(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec(v___x_1330_);
lean_dec(v_x_1322_);
v___x_1333_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v_a_1324_);
return v___x_1334_;
}
else
{
lean_object* v___x_1335_; lean_object* v_tk_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_unsigned_to_nat(0u);
v_tk_1336_ = l_Lean_Syntax_getArg(v_x_1322_, v___x_1335_);
lean_dec(v_x_1322_);
v___x_1337_ = l_Lean_Fmt_fmt(v_tk_1336_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v_a_1339_; lean_object* v___x_1340_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
v_a_1339_ = lean_ctor_get(v___x_1337_, 1);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1337_, 2);
v___x_1340_ = l_Lean_Fmt_fmt(v___x_1330_, v_a_1323_, v_a_1339_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1351_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_a_1342_ = lean_ctor_get(v___x_1340_, 1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1344_ = v___x_1340_;
v_isShared_1345_ = v_isSharedCheck_1351_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1351_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1346_ = 1;
v___x_1347_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_1338_, v_a_1341_, v___x_1346_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1347_);
v___x_1349_ = v___x_1344_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_a_1342_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
else
{
lean_dec(v_a_1338_);
return v___x_1340_;
}
}
else
{
lean_dec(v___x_1330_);
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvAnyGoals___boxed(lean_object* v_x_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Fmt_fmtConvAnyGoals(v_x_1352_, v_a_1353_, v_a_1354_);
lean_dec_ref(v_a_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1(){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1362_ = l_Lean_Fmt_fmtAttribute;
v___x_1363_ = ((lean_object*)(l_Lean_Fmt_fmtConvAnyGoals___closed__1));
v___x_1364_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___closed__1));
v___x_1365_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvAnyGoals___boxed), 3, 0);
v___x_1366_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1362_, v___x_1363_, v___x_1364_, v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1___boxed(lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1();
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFocus(lean_object* v_x_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = ((lean_object*)(l_Lean_Fmt_fmtConvFocus___closed__1));
lean_inc(v_x_1376_);
v___x_1380_ = l_Lean_Syntax_isOfKind(v_x_1376_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_dec(v_x_1376_);
v___x_1381_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v_a_1378_);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1383_ = lean_unsigned_to_nat(1u);
v___x_1384_ = l_Lean_Syntax_getArg(v_x_1376_, v___x_1383_);
v___x_1385_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1384_);
v___x_1386_ = l_Lean_Syntax_isOfKind(v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec(v___x_1384_);
lean_dec(v_x_1376_);
v___x_1387_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
lean_ctor_set(v___x_1388_, 1, v_a_1378_);
return v___x_1388_;
}
else
{
lean_object* v___x_1389_; lean_object* v_tk_1390_; lean_object* v___x_1391_; 
v___x_1389_ = lean_unsigned_to_nat(0u);
v_tk_1390_ = l_Lean_Syntax_getArg(v_x_1376_, v___x_1389_);
lean_dec(v_x_1376_);
v___x_1391_ = l_Lean_Fmt_fmt(v_tk_1390_, v_a_1377_, v_a_1378_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v_a_1393_; lean_object* v___x_1394_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
v_a_1393_ = lean_ctor_get(v___x_1391_, 1);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1391_, 2);
v___x_1394_ = l_Lean_Fmt_fmt(v___x_1384_, v_a_1377_, v_a_1393_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1405_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_a_1396_ = lean_ctor_get(v___x_1394_, 1);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1398_ = v___x_1394_;
v_isShared_1399_ = v_isSharedCheck_1405_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1405_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1400_ = 1;
v___x_1401_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_1392_, v_a_1395_, v___x_1400_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1401_);
v___x_1403_ = v___x_1398_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_a_1396_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
else
{
lean_dec(v_a_1392_);
return v___x_1394_;
}
}
else
{
lean_dec(v___x_1384_);
return v___x_1391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFocus___boxed(lean_object* v_x_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Fmt_fmtConvFocus(v_x_1406_, v_a_1407_, v_a_1408_);
lean_dec_ref(v_a_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1(){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1416_ = l_Lean_Fmt_fmtAttribute;
v___x_1417_ = ((lean_object*)(l_Lean_Fmt_fmtConvFocus___closed__1));
v___x_1418_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___closed__1));
v___x_1419_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvFocus___boxed), 3, 0);
v___x_1420_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1416_, v___x_1417_, v___x_1418_, v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1___boxed(lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1();
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFailIfSuccess(lean_object* v_x_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lean_Fmt_fmtConvFailIfSuccess___closed__1));
lean_inc(v_x_1430_);
v___x_1434_ = l_Lean_Syntax_isOfKind(v_x_1430_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec(v_x_1430_);
v___x_1435_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v_a_1432_);
return v___x_1436_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v___x_1437_ = lean_unsigned_to_nat(1u);
v___x_1438_ = l_Lean_Syntax_getArg(v_x_1430_, v___x_1437_);
v___x_1439_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1438_);
v___x_1440_ = l_Lean_Syntax_isOfKind(v___x_1438_, v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec(v___x_1438_);
lean_dec(v_x_1430_);
v___x_1441_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v_a_1432_);
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; lean_object* v_tk_1444_; lean_object* v___x_1445_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v_tk_1444_ = l_Lean_Syntax_getArg(v_x_1430_, v___x_1443_);
lean_dec(v_x_1430_);
v___x_1445_ = l_Lean_Fmt_fmt(v_tk_1444_, v_a_1431_, v_a_1432_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
v_a_1447_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1445_, 2);
v___x_1448_ = l_Lean_Fmt_fmt(v___x_1438_, v_a_1431_, v_a_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1459_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_a_1450_ = lean_ctor_get(v___x_1448_, 1);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1452_ = v___x_1448_;
v_isShared_1453_ = v_isSharedCheck_1459_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1459_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1454_ = 1;
v___x_1455_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_1446_, v_a_1449_, v___x_1454_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1455_);
v___x_1457_ = v___x_1452_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_a_1450_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
else
{
lean_dec(v_a_1446_);
return v___x_1448_;
}
}
else
{
lean_dec(v___x_1438_);
return v___x_1445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFailIfSuccess___boxed(lean_object* v_x_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_Fmt_fmtConvFailIfSuccess(v_x_1460_, v_a_1461_, v_a_1462_);
lean_dec_ref(v_a_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1(){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1470_ = l_Lean_Fmt_fmtAttribute;
v___x_1471_ = ((lean_object*)(l_Lean_Fmt_fmtConvFailIfSuccess___closed__1));
v___x_1472_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___closed__1));
v___x_1473_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvFailIfSuccess___boxed), 3, 0);
v___x_1474_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1470_, v___x_1471_, v___x_1472_, v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1___boxed(lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1();
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTry(lean_object* v_x_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Lean_Fmt_fmtConvTry___closed__1));
lean_inc(v_x_1484_);
v___x_1488_ = l_Lean_Syntax_isOfKind(v_x_1484_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec(v_x_1484_);
v___x_1489_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
lean_ctor_set(v___x_1490_, 1, v_a_1486_);
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1491_ = lean_unsigned_to_nat(1u);
v___x_1492_ = l_Lean_Syntax_getArg(v_x_1484_, v___x_1491_);
v___x_1493_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1492_);
v___x_1494_ = l_Lean_Syntax_isOfKind(v___x_1492_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec(v___x_1492_);
lean_dec(v_x_1484_);
v___x_1495_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v_a_1486_);
return v___x_1496_;
}
else
{
lean_object* v___x_1497_; lean_object* v_tk_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_unsigned_to_nat(0u);
v_tk_1498_ = l_Lean_Syntax_getArg(v_x_1484_, v___x_1497_);
lean_dec(v_x_1484_);
v___x_1499_ = l_Lean_Fmt_fmt(v_tk_1498_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v_a_1501_; lean_object* v___x_1502_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
v_a_1501_ = lean_ctor_get(v___x_1499_, 1);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1499_, 2);
v___x_1502_ = l_Lean_Fmt_fmt(v___x_1492_, v_a_1485_, v_a_1501_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1513_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_a_1504_ = lean_ctor_get(v___x_1502_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1506_ = v___x_1502_;
v_isShared_1507_ = v_isSharedCheck_1513_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1513_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
uint8_t v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1508_ = 1;
v___x_1509_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_1500_, v_a_1503_, v___x_1508_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1509_);
v___x_1511_ = v___x_1506_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_a_1504_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
else
{
lean_dec(v_a_1500_);
return v___x_1502_;
}
}
else
{
lean_dec(v___x_1492_);
return v___x_1499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTry___boxed(lean_object* v_x_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_Fmt_fmtConvTry(v_x_1514_, v_a_1515_, v_a_1516_);
lean_dec_ref(v_a_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1(){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1524_ = l_Lean_Fmt_fmtAttribute;
v___x_1525_ = ((lean_object*)(l_Lean_Fmt_fmtConvTry___closed__1));
v___x_1526_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___closed__1));
v___x_1527_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvTry___boxed), 3, 0);
v___x_1528_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1524_, v___x_1525_, v___x_1526_, v___x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1___boxed(lean_object* v_a_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1();
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRepeat(lean_object* v_x_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_Fmt_fmtConvRepeat___closed__1));
lean_inc(v_x_1538_);
v___x_1542_ = l_Lean_Syntax_isOfKind(v_x_1538_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec(v_x_1538_);
v___x_1543_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v_a_1540_);
return v___x_1544_;
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = l_Lean_Syntax_getArg(v_x_1538_, v___x_1545_);
v___x_1547_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1546_);
v___x_1548_ = l_Lean_Syntax_isOfKind(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec(v___x_1546_);
lean_dec(v_x_1538_);
v___x_1549_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v_a_1540_);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; lean_object* v_tk_1552_; lean_object* v___x_1553_; 
v___x_1551_ = lean_unsigned_to_nat(0u);
v_tk_1552_ = l_Lean_Syntax_getArg(v_x_1538_, v___x_1551_);
lean_dec(v_x_1538_);
v___x_1553_ = l_Lean_Fmt_fmt(v_tk_1552_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v_a_1555_; lean_object* v___x_1556_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
v_a_1555_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1553_, 2);
v___x_1556_ = l_Lean_Fmt_fmt(v___x_1546_, v_a_1539_, v_a_1555_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1567_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_a_1558_ = lean_ctor_get(v___x_1556_, 1);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1560_ = v___x_1556_;
v_isShared_1561_ = v_isSharedCheck_1567_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1567_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1562_ = 1;
v___x_1563_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_1554_, v_a_1557_, v___x_1562_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1563_);
v___x_1565_ = v___x_1560_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_a_1558_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
lean_dec(v_a_1554_);
return v___x_1556_;
}
}
else
{
lean_dec(v___x_1546_);
return v___x_1553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRepeat___boxed(lean_object* v_x_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Fmt_fmtConvRepeat(v_x_1568_, v_a_1569_, v_a_1570_);
lean_dec_ref(v_a_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1(){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1578_ = l_Lean_Fmt_fmtAttribute;
v___x_1579_ = ((lean_object*)(l_Lean_Fmt_fmtConvRepeat___closed__1));
v___x_1580_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___closed__1));
v___x_1581_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvRepeat___boxed), 3, 0);
v___x_1582_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1578_, v___x_1579_, v___x_1580_, v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1___boxed(lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1();
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCase(lean_object* v_x_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = ((lean_object*)(l_Lean_Fmt_fmtConvCase___closed__1));
lean_inc(v_x_1592_);
v___x_1596_ = l_Lean_Syntax_isOfKind(v_x_1592_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v_x_1592_);
v___x_1597_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v_a_1594_);
return v___x_1598_;
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1599_ = lean_unsigned_to_nat(3u);
v___x_1600_ = l_Lean_Syntax_getArg(v_x_1592_, v___x_1599_);
v___x_1601_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1600_);
v___x_1602_ = l_Lean_Syntax_isOfKind(v___x_1600_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v___x_1600_);
lean_dec(v_x_1592_);
v___x_1603_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1594_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v_caseTk_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v_arrowTk_1610_; lean_object* v_args_1611_; lean_object* v___x_1612_; 
v___x_1605_ = lean_unsigned_to_nat(0u);
v_caseTk_1606_ = l_Lean_Syntax_getArg(v_x_1592_, v___x_1605_);
v___x_1607_ = lean_unsigned_to_nat(1u);
v___x_1608_ = l_Lean_Syntax_getArg(v_x_1592_, v___x_1607_);
v___x_1609_ = lean_unsigned_to_nat(2u);
v_arrowTk_1610_ = l_Lean_Syntax_getArg(v_x_1592_, v___x_1609_);
lean_dec(v_x_1592_);
v_args_1611_ = l_Lean_Syntax_getArgs(v___x_1608_);
lean_dec(v___x_1608_);
v___x_1612_ = l_Lean_Fmt_fmtCaseDeclaration___redArg(v_caseTk_1606_, v_args_1611_, v_arrowTk_1610_, v___x_1600_, v_a_1593_, v_a_1594_);
return v___x_1612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCase___boxed(lean_object* v_x_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_Fmt_fmtConvCase(v_x_1613_, v_a_1614_, v_a_1615_);
lean_dec_ref(v_a_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1(){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1623_ = l_Lean_Fmt_fmtAttribute;
v___x_1624_ = ((lean_object*)(l_Lean_Fmt_fmtConvCase___closed__1));
v___x_1625_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___closed__1));
v___x_1626_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvCase___boxed), 3, 0);
v___x_1627_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1623_, v___x_1624_, v___x_1625_, v___x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1___boxed(lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1();
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCase_x27(lean_object* v_x_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_Fmt_fmtConvCase_x27___closed__1));
lean_inc(v_x_1637_);
v___x_1641_ = l_Lean_Syntax_isOfKind(v_x_1637_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec(v_x_1637_);
v___x_1642_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v_a_1639_);
return v___x_1643_;
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1644_ = lean_unsigned_to_nat(3u);
v___x_1645_ = l_Lean_Syntax_getArg(v_x_1637_, v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1645_);
v___x_1647_ = l_Lean_Syntax_isOfKind(v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec(v___x_1645_);
lean_dec(v_x_1637_);
v___x_1648_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v_a_1639_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; lean_object* v_caseTk_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v_arrowTk_1655_; lean_object* v_args_1656_; lean_object* v___x_1657_; 
v___x_1650_ = lean_unsigned_to_nat(0u);
v_caseTk_1651_ = l_Lean_Syntax_getArg(v_x_1637_, v___x_1650_);
v___x_1652_ = lean_unsigned_to_nat(1u);
v___x_1653_ = l_Lean_Syntax_getArg(v_x_1637_, v___x_1652_);
v___x_1654_ = lean_unsigned_to_nat(2u);
v_arrowTk_1655_ = l_Lean_Syntax_getArg(v_x_1637_, v___x_1654_);
lean_dec(v_x_1637_);
v_args_1656_ = l_Lean_Syntax_getArgs(v___x_1653_);
lean_dec(v___x_1653_);
v___x_1657_ = l_Lean_Fmt_fmtCaseDeclaration___redArg(v_caseTk_1651_, v_args_1656_, v_arrowTk_1655_, v___x_1645_, v_a_1638_, v_a_1639_);
return v___x_1657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvCase_x27___boxed(lean_object* v_x_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_Fmt_fmtConvCase_x27(v_x_1658_, v_a_1659_, v_a_1660_);
lean_dec_ref(v_a_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1(){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1668_ = l_Lean_Fmt_fmtAttribute;
v___x_1669_ = ((lean_object*)(l_Lean_Fmt_fmtConvCase_x27___closed__1));
v___x_1670_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___closed__1));
v___x_1671_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvCase_x27___boxed), 3, 0);
v___x_1672_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1668_, v___x_1669_, v___x_1670_, v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1___boxed(lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1();
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNext(lean_object* v_x_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Fmt_fmtConvNext___closed__1));
lean_inc(v_x_1682_);
v___x_1686_ = l_Lean_Syntax_isOfKind(v_x_1682_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v_x_1682_);
v___x_1687_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v_a_1684_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1689_ = lean_unsigned_to_nat(3u);
v___x_1690_ = l_Lean_Syntax_getArg(v_x_1682_, v___x_1689_);
v___x_1691_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1690_);
v___x_1692_ = l_Lean_Syntax_isOfKind(v___x_1690_, v___x_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_dec(v___x_1690_);
lean_dec(v_x_1682_);
v___x_1693_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v_a_1684_);
return v___x_1694_;
}
else
{
lean_object* v___x_1695_; lean_object* v_nextTk_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_arrowTk_1700_; lean_object* v_args_1701_; lean_object* v___x_1702_; 
v___x_1695_ = lean_unsigned_to_nat(0u);
v_nextTk_1696_ = l_Lean_Syntax_getArg(v_x_1682_, v___x_1695_);
v___x_1697_ = lean_unsigned_to_nat(1u);
v___x_1698_ = l_Lean_Syntax_getArg(v_x_1682_, v___x_1697_);
v___x_1699_ = lean_unsigned_to_nat(2u);
v_arrowTk_1700_ = l_Lean_Syntax_getArg(v_x_1682_, v___x_1699_);
lean_dec(v_x_1682_);
v_args_1701_ = l_Lean_Syntax_getArgs(v___x_1698_);
lean_dec(v___x_1698_);
v___x_1702_ = l_Lean_Fmt_fmtNextLike___redArg(v_nextTk_1696_, v_args_1701_, v_arrowTk_1700_, v___x_1690_, v_a_1683_, v_a_1684_);
return v___x_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvNext___boxed(lean_object* v_x_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Fmt_fmtConvNext(v_x_1703_, v_a_1704_, v_a_1705_);
lean_dec_ref(v_a_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1(){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1713_ = l_Lean_Fmt_fmtAttribute;
v___x_1714_ = ((lean_object*)(l_Lean_Fmt_fmtConvNext___closed__1));
v___x_1715_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___closed__1));
v___x_1716_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvNext___boxed), 3, 0);
v___x_1717_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1713_, v___x_1714_, v___x_1715_, v___x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1___boxed(lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1();
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDot(lean_object* v_x_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = ((lean_object*)(l_Lean_Fmt_fmtConvDot___closed__1));
lean_inc(v_x_1727_);
v___x_1731_ = l_Lean_Syntax_isOfKind(v_x_1727_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v_x_1727_);
v___x_1732_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v_a_1729_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = l_Lean_Syntax_getArg(v_x_1727_, v___x_1734_);
v___x_1736_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_1735_);
v___x_1737_ = l_Lean_Syntax_isOfKind(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v___x_1735_);
lean_dec(v_x_1727_);
v___x_1738_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v_a_1729_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; lean_object* v_dotTk_1741_; lean_object* v___x_1742_; 
v___x_1740_ = lean_unsigned_to_nat(0u);
v_dotTk_1741_ = l_Lean_Syntax_getArg(v_x_1727_, v___x_1740_);
lean_dec(v_x_1727_);
v___x_1742_ = l_Lean_Fmt_fmt(v_dotTk_1741_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v_a_1744_; lean_object* v___x_1745_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
v_a_1744_ = lean_ctor_get(v___x_1742_, 1);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1742_, 2);
v___x_1745_ = l_Lean_Fmt_fmt(v___x_1735_, v_a_1728_, v_a_1744_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1760_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_a_1747_ = lean_ctor_get(v___x_1745_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1749_ = v___x_1745_;
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1751_ = lean_unsigned_to_nat(2u);
v___x_1752_ = lean_mk_empty_array_with_capacity(v___x_1751_);
v___x_1753_ = lean_array_push(v___x_1752_, v_a_1743_);
v___x_1754_ = lean_array_push(v___x_1753_, v_a_1746_);
v___x_1755_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v___x_1754_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1755_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1756_);
v___x_1758_ = v___x_1749_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_a_1747_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
else
{
lean_dec(v_a_1743_);
return v___x_1745_;
}
}
else
{
lean_dec(v___x_1735_);
return v___x_1742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDot___boxed(lean_object* v_x_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Fmt_fmtConvDot(v_x_1761_, v_a_1762_, v_a_1763_);
lean_dec_ref(v_a_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1(){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1771_ = l_Lean_Fmt_fmtAttribute;
v___x_1772_ = ((lean_object*)(l_Lean_Fmt_fmtConvDot___closed__1));
v___x_1773_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___closed__1));
v___x_1774_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvDot___boxed), 3, 0);
v___x_1775_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1771_, v___x_1772_, v___x_1773_, v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1___boxed(lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1();
return v_res_1777_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtConvSeqFocus___closed__2(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_box(0);
v___x_1784_ = lean_unsigned_to_nat(16u);
v___x_1785_ = lean_mk_array(v___x_1784_, v___x_1783_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtConvSeqFocus___closed__3(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_obj_once(&l_Lean_Fmt_fmtConvSeqFocus___closed__2, &l_Lean_Fmt_fmtConvSeqFocus___closed__2_once, _init_l_Lean_Fmt_fmtConvSeqFocus___closed__2);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
lean_ctor_set(v___x_1788_, 1, v___x_1786_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtConvSeqFocus___closed__4(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; lean_object* v___x_1792_; 
v___x_1789_ = lean_obj_once(&l_Lean_Fmt_fmtConvSeqFocus___closed__3, &l_Lean_Fmt_fmtConvSeqFocus___closed__3_once, _init_l_Lean_Fmt_fmtConvSeqFocus___closed__3);
v___x_1790_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeqFocus___closed__1));
v___x_1791_ = 0;
v___x_1792_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1789_);
lean_ctor_set_uint8(v___x_1792_, sizeof(void*)*2, v___x_1791_);
lean_ctor_set_uint8(v___x_1792_, sizeof(void*)*2 + 1, v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtConvSeqFocus(void){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_obj_once(&l_Lean_Fmt_fmtConvSeqFocus___closed__4, &l_Lean_Fmt_fmtConvSeqFocus___closed__4_once, _init_l_Lean_Fmt_fmtConvSeqFocus___closed__4);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1(){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1807_ = l_Lean_Fmt_infixFmtAttribute;
v___x_1808_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__1));
v___x_1809_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___closed__3));
v___x_1810_ = l_Lean_Fmt_fmtConvSeqFocus;
v___x_1811_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1807_, v___x_1808_, v___x_1809_, v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1___boxed(lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1();
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRw(lean_object* v_x_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__1));
lean_inc(v_x_1833_);
v___x_1837_ = l_Lean_Syntax_isOfKind(v_x_1833_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec(v_x_1833_);
v___x_1838_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v_a_1835_);
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; lean_object* v_cfg_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1840_ = lean_unsigned_to_nat(1u);
v_cfg_1841_ = l_Lean_Syntax_getArg(v_x_1833_, v___x_1840_);
v___x_1842_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__3));
lean_inc(v_cfg_1841_);
v___x_1843_ = l_Lean_Syntax_isOfKind(v_cfg_1841_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec(v_cfg_1841_);
lean_dec(v_x_1833_);
v___x_1844_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v_a_1835_);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1846_ = lean_unsigned_to_nat(2u);
v___x_1847_ = l_Lean_Syntax_getArg(v_x_1833_, v___x_1846_);
v___x_1848_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__5));
lean_inc(v___x_1847_);
v___x_1849_ = l_Lean_Syntax_isOfKind(v___x_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec(v___x_1847_);
lean_dec(v_cfg_1841_);
lean_dec(v_x_1833_);
v___x_1850_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v_a_1835_);
return v___x_1851_;
}
else
{
lean_object* v___x_1852_; lean_object* v_rwTk_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1852_ = lean_unsigned_to_nat(0u);
v_rwTk_1853_ = l_Lean_Syntax_getArg(v_x_1833_, v___x_1852_);
lean_dec(v_x_1833_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_cfg_1841_);
v___x_1855_ = lean_box(0);
v___x_1856_ = l_Lean_Fmt_fmtRwLike(v_rwTk_1853_, v___x_1854_, v___x_1847_, v___x_1855_, v_a_1834_, v_a_1835_);
return v___x_1856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRw___boxed(lean_object* v_x_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_Fmt_fmtConvRw(v_x_1857_, v_a_1858_, v_a_1859_);
lean_dec_ref(v_a_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1(){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1867_ = l_Lean_Fmt_fmtAttribute;
v___x_1868_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__1));
v___x_1869_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___closed__1));
v___x_1870_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvRw___boxed), 3, 0);
v___x_1871_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1867_, v___x_1868_, v___x_1869_, v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1___boxed(lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1();
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvErw(lean_object* v_x_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v___x_1884_; uint8_t v___x_1885_; 
v___x_1884_ = ((lean_object*)(l_Lean_Fmt_fmtConvErw___closed__1));
lean_inc(v_x_1881_);
v___x_1885_ = l_Lean_Syntax_isOfKind(v_x_1881_, v___x_1884_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec(v_x_1881_);
v___x_1886_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
lean_ctor_set(v___x_1887_, 1, v_a_1883_);
return v___x_1887_;
}
else
{
lean_object* v___x_1888_; lean_object* v_cfg_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1888_ = lean_unsigned_to_nat(1u);
v_cfg_1889_ = l_Lean_Syntax_getArg(v_x_1881_, v___x_1888_);
v___x_1890_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__3));
lean_inc(v_cfg_1889_);
v___x_1891_ = l_Lean_Syntax_isOfKind(v_cfg_1889_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_dec(v_cfg_1889_);
lean_dec(v_x_1881_);
v___x_1892_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v_a_1883_);
return v___x_1893_;
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1894_ = lean_unsigned_to_nat(2u);
v___x_1895_ = l_Lean_Syntax_getArg(v_x_1881_, v___x_1894_);
v___x_1896_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__5));
lean_inc(v___x_1895_);
v___x_1897_ = l_Lean_Syntax_isOfKind(v___x_1895_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_dec(v___x_1895_);
lean_dec(v_cfg_1889_);
lean_dec(v_x_1881_);
v___x_1898_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v_a_1883_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; lean_object* v_erwTk_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1900_ = lean_unsigned_to_nat(0u);
v_erwTk_1901_ = l_Lean_Syntax_getArg(v_x_1881_, v___x_1900_);
lean_dec(v_x_1881_);
v___x_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1902_, 0, v_cfg_1889_);
v___x_1903_ = lean_box(0);
v___x_1904_ = l_Lean_Fmt_fmtRwLike(v_erwTk_1901_, v___x_1902_, v___x_1895_, v___x_1903_, v_a_1882_, v_a_1883_);
return v___x_1904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvErw___boxed(lean_object* v_x_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Fmt_fmtConvErw(v_x_1905_, v_a_1906_, v_a_1907_);
lean_dec_ref(v_a_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1(){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1915_ = l_Lean_Fmt_fmtAttribute;
v___x_1916_ = ((lean_object*)(l_Lean_Fmt_fmtConvErw___closed__1));
v___x_1917_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___closed__1));
v___x_1918_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvErw___boxed), 3, 0);
v___x_1919_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1915_, v___x_1916_, v___x_1917_, v___x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1___boxed(lean_object* v_a_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1();
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRewrite(lean_object* v_x_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = ((lean_object*)(l_Lean_Fmt_fmtConvRewrite___closed__1));
lean_inc(v_x_1929_);
v___x_1933_ = l_Lean_Syntax_isOfKind(v_x_1929_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
lean_dec(v_x_1929_);
v___x_1934_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v_a_1931_);
return v___x_1935_;
}
else
{
lean_object* v___x_1936_; lean_object* v_cfg_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1936_ = lean_unsigned_to_nat(1u);
v_cfg_1937_ = l_Lean_Syntax_getArg(v_x_1929_, v___x_1936_);
v___x_1938_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__3));
lean_inc(v_cfg_1937_);
v___x_1939_ = l_Lean_Syntax_isOfKind(v_cfg_1937_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec(v_cfg_1937_);
lean_dec(v_x_1929_);
v___x_1940_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v_a_1931_);
return v___x_1941_;
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1942_ = lean_unsigned_to_nat(2u);
v___x_1943_ = l_Lean_Syntax_getArg(v_x_1929_, v___x_1942_);
v___x_1944_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__5));
lean_inc(v___x_1943_);
v___x_1945_ = l_Lean_Syntax_isOfKind(v___x_1943_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec(v___x_1943_);
lean_dec(v_cfg_1937_);
lean_dec(v_x_1929_);
v___x_1946_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v_a_1931_);
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; lean_object* v_rewriteTk_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1948_ = lean_unsigned_to_nat(0u);
v_rewriteTk_1949_ = l_Lean_Syntax_getArg(v_x_1929_, v___x_1948_);
lean_dec(v_x_1929_);
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v_cfg_1937_);
v___x_1951_ = lean_box(0);
v___x_1952_ = l_Lean_Fmt_fmtRwLike(v_rewriteTk_1949_, v___x_1950_, v___x_1943_, v___x_1951_, v_a_1930_, v_a_1931_);
return v___x_1952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvRewrite___boxed(lean_object* v_x_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Fmt_fmtConvRewrite(v_x_1953_, v_a_1954_, v_a_1955_);
lean_dec_ref(v_a_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1(){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1963_ = l_Lean_Fmt_fmtAttribute;
v___x_1964_ = ((lean_object*)(l_Lean_Fmt_fmtConvRewrite___closed__1));
v___x_1965_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___closed__1));
v___x_1966_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvRewrite___boxed), 3, 0);
v___x_1967_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1963_, v___x_1964_, v___x_1965_, v___x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1___boxed(lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1();
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSimp(lean_object* v_x_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = ((lean_object*)(l_Lean_Fmt_fmtConvSimp___closed__1));
lean_inc(v_x_1983_);
v___x_1987_ = l_Lean_Syntax_isOfKind(v_x_1983_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
lean_dec(v_x_1983_);
v___x_1988_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v_a_1985_);
return v___x_1989_;
}
else
{
lean_object* v___x_1990_; lean_object* v_cfg_1991_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_1990_ = lean_unsigned_to_nat(1u);
v_cfg_1991_ = l_Lean_Syntax_getArg(v_x_1983_, v___x_1990_);
v___x_2003_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__3));
lean_inc(v_cfg_1991_);
v___x_2004_ = l_Lean_Syntax_isOfKind(v_cfg_1991_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec(v_cfg_1991_);
lean_dec(v_x_1983_);
v___x_2005_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v_a_1985_);
return v___x_2006_;
}
else
{
lean_object* v___x_2007_; lean_object* v_simpTk_2008_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v_lbTk_x3f_2012_; lean_object* v_args_x3f_2013_; lean_object* v_rbTk_x3f_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___x_2028_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v_only_x3f_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v_disch_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2007_ = lean_unsigned_to_nat(0u);
v_simpTk_2008_ = l_Lean_Syntax_getArg(v_x_1983_, v___x_2007_);
v___x_2028_ = lean_unsigned_to_nat(2u);
v___x_2062_ = l_Lean_Syntax_getArg(v_x_1983_, v___x_2028_);
v___x_2063_ = l_Lean_Syntax_isNone(v___x_2062_);
if (v___x_2063_ == 0)
{
uint8_t v___x_2064_; 
lean_inc(v___x_2062_);
v___x_2064_ = l_Lean_Syntax_matchesNull(v___x_2062_, v___x_1990_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec(v___x_2062_);
lean_dec(v_simpTk_2008_);
lean_dec(v_cfg_1991_);
lean_dec(v_x_1983_);
v___x_2065_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v_a_1985_);
return v___x_2066_;
}
else
{
lean_object* v_disch_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_disch_2067_ = l_Lean_Syntax_getArg(v___x_2062_, v___x_2007_);
lean_dec(v___x_2062_);
v___x_2068_ = ((lean_object*)(l_Lean_Fmt_fmtConvSimp___closed__3));
lean_inc(v_disch_2067_);
v___x_2069_ = l_Lean_Syntax_isOfKind(v_disch_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
lean_dec(v_disch_2067_);
lean_dec(v_simpTk_2008_);
lean_dec(v_cfg_1991_);
lean_dec(v_x_1983_);
v___x_2070_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v_a_1985_);
return v___x_2071_;
}
else
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2072_, 0, v_disch_2067_);
v_disch_2050_ = v___x_2072_;
v___y_2051_ = v_a_1984_;
v___y_2052_ = v_a_1985_;
goto v___jp_2049_;
}
}
}
else
{
lean_object* v___x_2073_; 
lean_dec(v___x_2062_);
v___x_2073_ = lean_box(0);
v_disch_2050_ = v___x_2073_;
v___y_2051_ = v_a_1984_;
v___y_2052_ = v_a_1985_;
goto v___jp_2049_;
}
v___jp_2009_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = lean_mk_empty_array_with_capacity(v___x_1990_);
v___x_2018_ = lean_array_push(v___x_2017_, v_simpTk_2008_);
if (lean_obj_tag(v_args_x3f_2013_) == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_box(0);
v___y_1993_ = v___x_2018_;
v___y_1994_ = v___y_2015_;
v___y_1995_ = v___y_2010_;
v___y_1996_ = v_lbTk_x3f_2012_;
v___y_1997_ = v_rbTk_x3f_2014_;
v___y_1998_ = v___y_2011_;
v___y_1999_ = v___y_2016_;
v___y_2000_ = v___x_2019_;
goto v___jp_1992_;
}
else
{
lean_object* v_val_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_val_2020_ = lean_ctor_get(v_args_x3f_2013_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_args_x3f_2013_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v_args_x3f_2013_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_val_2020_);
lean_dec(v_args_x3f_2013_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_val_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
v___y_1993_ = v___x_2018_;
v___y_1994_ = v___y_2015_;
v___y_1995_ = v___y_2010_;
v___y_1996_ = v_lbTk_x3f_2012_;
v___y_1997_ = v_rbTk_x3f_2014_;
v___y_1998_ = v___y_2011_;
v___y_1999_ = v___y_2016_;
v___y_2000_ = v___x_2025_;
goto v___jp_1992_;
}
}
}
}
v___jp_2029_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2035_ = lean_unsigned_to_nat(4u);
v___x_2036_ = l_Lean_Syntax_getArg(v_x_1983_, v___x_2035_);
lean_dec(v_x_1983_);
v___x_2037_ = l_Lean_Syntax_isNone(v___x_2036_);
if (v___x_2037_ == 0)
{
uint8_t v___x_2038_; 
lean_inc(v___x_2036_);
v___x_2038_ = l_Lean_Syntax_matchesNull(v___x_2036_, v___y_2031_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec(v___x_2036_);
lean_dec(v_only_x3f_2032_);
lean_dec(v___y_2030_);
lean_dec(v_simpTk_2008_);
lean_dec(v_cfg_1991_);
v___x_2039_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v___y_2034_);
return v___x_2040_;
}
else
{
lean_object* v_lbTk_x3f_2041_; lean_object* v___x_2042_; lean_object* v_rbTk_x3f_2043_; lean_object* v_args_x3f_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_lbTk_x3f_2041_ = l_Lean_Syntax_getArg(v___x_2036_, v___x_2007_);
v___x_2042_ = l_Lean_Syntax_getArg(v___x_2036_, v___x_1990_);
v_rbTk_x3f_2043_ = l_Lean_Syntax_getArg(v___x_2036_, v___x_2028_);
lean_dec(v___x_2036_);
v_args_x3f_2044_ = l_Lean_Syntax_getArgs(v___x_2042_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_lbTk_x3f_2041_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_args_x3f_2044_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_rbTk_x3f_2043_);
v___y_2010_ = v___y_2030_;
v___y_2011_ = v_only_x3f_2032_;
v_lbTk_x3f_2012_ = v___x_2045_;
v_args_x3f_2013_ = v___x_2046_;
v_rbTk_x3f_2014_ = v___x_2047_;
v___y_2015_ = v___y_2033_;
v___y_2016_ = v___y_2034_;
goto v___jp_2009_;
}
}
else
{
lean_object* v___x_2048_; 
lean_dec(v___x_2036_);
v___x_2048_ = lean_box(0);
v___y_2010_ = v___y_2030_;
v___y_2011_ = v_only_x3f_2032_;
v_lbTk_x3f_2012_ = v___x_2048_;
v_args_x3f_2013_ = v___x_2048_;
v_rbTk_x3f_2014_ = v___x_2048_;
v___y_2015_ = v___y_2033_;
v___y_2016_ = v___y_2034_;
goto v___jp_2009_;
}
}
v___jp_2049_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2053_ = lean_unsigned_to_nat(3u);
v___x_2054_ = l_Lean_Syntax_getArg(v_x_1983_, v___x_2053_);
v___x_2055_ = l_Lean_Syntax_isNone(v___x_2054_);
if (v___x_2055_ == 0)
{
uint8_t v___x_2056_; 
lean_inc(v___x_2054_);
v___x_2056_ = l_Lean_Syntax_matchesNull(v___x_2054_, v___x_1990_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec(v___x_2054_);
lean_dec(v_disch_2050_);
lean_dec(v_simpTk_2008_);
lean_dec(v_cfg_1991_);
lean_dec(v_x_1983_);
v___x_2057_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v___y_2052_);
return v___x_2058_;
}
else
{
lean_object* v_only_x3f_2059_; lean_object* v___x_2060_; 
v_only_x3f_2059_ = l_Lean_Syntax_getArg(v___x_2054_, v___x_2007_);
lean_dec(v___x_2054_);
v___x_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2060_, 0, v_only_x3f_2059_);
v___y_2030_ = v_disch_2050_;
v___y_2031_ = v___x_2053_;
v_only_x3f_2032_ = v___x_2060_;
v___y_2033_ = v___y_2051_;
v___y_2034_ = v___y_2052_;
goto v___jp_2029_;
}
}
else
{
lean_object* v___x_2061_; 
lean_dec(v___x_2054_);
v___x_2061_ = lean_box(0);
v___y_2030_ = v_disch_2050_;
v___y_2031_ = v___x_2053_;
v_only_x3f_2032_ = v___x_2061_;
v___y_2033_ = v___y_2051_;
v___y_2034_ = v___y_2052_;
goto v___jp_2029_;
}
}
}
v___jp_1992_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_box(0);
v___x_2002_ = l_Lean_Fmt_fmtSimpLike(v___y_1993_, v_cfg_1991_, v___y_1995_, v___y_1998_, v___y_1996_, v___y_2000_, v___y_1997_, v___x_2001_, v___y_1994_, v___y_1999_);
return v___x_2002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSimp___boxed(lean_object* v_x_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_Fmt_fmtConvSimp(v_x_2074_, v_a_2075_, v_a_2076_);
lean_dec_ref(v_a_2075_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1(){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2084_ = l_Lean_Fmt_fmtAttribute;
v___x_2085_ = ((lean_object*)(l_Lean_Fmt_fmtConvSimp___closed__1));
v___x_2086_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___closed__1));
v___x_2087_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvSimp___boxed), 3, 0);
v___x_2088_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2084_, v___x_2085_, v___x_2086_, v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1___boxed(lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1();
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDSimp(lean_object* v_x_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = ((lean_object*)(l_Lean_Fmt_fmtConvDSimp___closed__1));
lean_inc(v_x_2098_);
v___x_2102_ = l_Lean_Syntax_isOfKind(v_x_2098_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_dec(v_x_2098_);
v___x_2103_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v_a_2100_);
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; lean_object* v_cfg_2106_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2105_ = lean_unsigned_to_nat(1u);
v_cfg_2106_ = l_Lean_Syntax_getArg(v_x_2098_, v___x_2105_);
v___x_2118_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__3));
lean_inc(v_cfg_2106_);
v___x_2119_ = l_Lean_Syntax_isOfKind(v_cfg_2106_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec(v_cfg_2106_);
lean_dec(v_x_2098_);
v___x_2120_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
lean_ctor_set(v___x_2121_, 1, v_a_2100_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; lean_object* v_dsimpTk_2123_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v_lbTk_x3f_2127_; lean_object* v_args_x3f_2128_; lean_object* v_rbTk_x3f_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___x_2143_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v_only_x3f_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v_disch_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2122_ = lean_unsigned_to_nat(0u);
v_dsimpTk_2123_ = l_Lean_Syntax_getArg(v_x_2098_, v___x_2122_);
v___x_2143_ = lean_unsigned_to_nat(2u);
v___x_2177_ = l_Lean_Syntax_getArg(v_x_2098_, v___x_2143_);
v___x_2178_ = l_Lean_Syntax_isNone(v___x_2177_);
if (v___x_2178_ == 0)
{
uint8_t v___x_2179_; 
lean_inc(v___x_2177_);
v___x_2179_ = l_Lean_Syntax_matchesNull(v___x_2177_, v___x_2105_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
lean_dec(v___x_2177_);
lean_dec(v_dsimpTk_2123_);
lean_dec(v_cfg_2106_);
lean_dec(v_x_2098_);
v___x_2180_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v_a_2100_);
return v___x_2181_;
}
else
{
lean_object* v_disch_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v_disch_2182_ = l_Lean_Syntax_getArg(v___x_2177_, v___x_2122_);
lean_dec(v___x_2177_);
v___x_2183_ = ((lean_object*)(l_Lean_Fmt_fmtConvSimp___closed__3));
lean_inc(v_disch_2182_);
v___x_2184_ = l_Lean_Syntax_isOfKind(v_disch_2182_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec(v_disch_2182_);
lean_dec(v_dsimpTk_2123_);
lean_dec(v_cfg_2106_);
lean_dec(v_x_2098_);
v___x_2185_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v_a_2100_);
return v___x_2186_;
}
else
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2187_, 0, v_disch_2182_);
v_disch_2165_ = v___x_2187_;
v___y_2166_ = v_a_2099_;
v___y_2167_ = v_a_2100_;
goto v___jp_2164_;
}
}
}
else
{
lean_object* v___x_2188_; 
lean_dec(v___x_2177_);
v___x_2188_ = lean_box(0);
v_disch_2165_ = v___x_2188_;
v___y_2166_ = v_a_2099_;
v___y_2167_ = v_a_2100_;
goto v___jp_2164_;
}
v___jp_2124_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = lean_mk_empty_array_with_capacity(v___x_2105_);
v___x_2133_ = lean_array_push(v___x_2132_, v_dsimpTk_2123_);
if (lean_obj_tag(v_args_x3f_2128_) == 0)
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_box(0);
v___y_2108_ = v_rbTk_x3f_2129_;
v___y_2109_ = v___x_2133_;
v___y_2110_ = v___y_2130_;
v___y_2111_ = v___y_2131_;
v___y_2112_ = v___y_2125_;
v___y_2113_ = v_lbTk_x3f_2127_;
v___y_2114_ = v___y_2126_;
v___y_2115_ = v___x_2134_;
goto v___jp_2107_;
}
else
{
lean_object* v_val_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
v_val_2135_ = lean_ctor_get(v_args_x3f_2128_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_args_x3f_2128_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v_args_x3f_2128_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_val_2135_);
lean_dec(v_args_x3f_2128_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_val_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
v___y_2108_ = v_rbTk_x3f_2129_;
v___y_2109_ = v___x_2133_;
v___y_2110_ = v___y_2130_;
v___y_2111_ = v___y_2131_;
v___y_2112_ = v___y_2125_;
v___y_2113_ = v_lbTk_x3f_2127_;
v___y_2114_ = v___y_2126_;
v___y_2115_ = v___x_2140_;
goto v___jp_2107_;
}
}
}
}
v___jp_2144_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2150_ = lean_unsigned_to_nat(4u);
v___x_2151_ = l_Lean_Syntax_getArg(v_x_2098_, v___x_2150_);
lean_dec(v_x_2098_);
v___x_2152_ = l_Lean_Syntax_isNone(v___x_2151_);
if (v___x_2152_ == 0)
{
uint8_t v___x_2153_; 
lean_inc(v___x_2151_);
v___x_2153_ = l_Lean_Syntax_matchesNull(v___x_2151_, v___y_2146_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec(v___x_2151_);
lean_dec(v_only_x3f_2147_);
lean_dec(v___y_2145_);
lean_dec(v_dsimpTk_2123_);
lean_dec(v_cfg_2106_);
v___x_2154_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v___y_2149_);
return v___x_2155_;
}
else
{
lean_object* v_lbTk_x3f_2156_; lean_object* v___x_2157_; lean_object* v_rbTk_x3f_2158_; lean_object* v_args_x3f_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v_lbTk_x3f_2156_ = l_Lean_Syntax_getArg(v___x_2151_, v___x_2122_);
v___x_2157_ = l_Lean_Syntax_getArg(v___x_2151_, v___x_2105_);
v_rbTk_x3f_2158_ = l_Lean_Syntax_getArg(v___x_2151_, v___x_2143_);
lean_dec(v___x_2151_);
v_args_x3f_2159_ = l_Lean_Syntax_getArgs(v___x_2157_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2160_, 0, v_lbTk_x3f_2156_);
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v_args_x3f_2159_);
v___x_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2162_, 0, v_rbTk_x3f_2158_);
v___y_2125_ = v___y_2145_;
v___y_2126_ = v_only_x3f_2147_;
v_lbTk_x3f_2127_ = v___x_2160_;
v_args_x3f_2128_ = v___x_2161_;
v_rbTk_x3f_2129_ = v___x_2162_;
v___y_2130_ = v___y_2148_;
v___y_2131_ = v___y_2149_;
goto v___jp_2124_;
}
}
else
{
lean_object* v___x_2163_; 
lean_dec(v___x_2151_);
v___x_2163_ = lean_box(0);
v___y_2125_ = v___y_2145_;
v___y_2126_ = v_only_x3f_2147_;
v_lbTk_x3f_2127_ = v___x_2163_;
v_args_x3f_2128_ = v___x_2163_;
v_rbTk_x3f_2129_ = v___x_2163_;
v___y_2130_ = v___y_2148_;
v___y_2131_ = v___y_2149_;
goto v___jp_2124_;
}
}
v___jp_2164_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2168_ = lean_unsigned_to_nat(3u);
v___x_2169_ = l_Lean_Syntax_getArg(v_x_2098_, v___x_2168_);
v___x_2170_ = l_Lean_Syntax_isNone(v___x_2169_);
if (v___x_2170_ == 0)
{
uint8_t v___x_2171_; 
lean_inc(v___x_2169_);
v___x_2171_ = l_Lean_Syntax_matchesNull(v___x_2169_, v___x_2105_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec(v___x_2169_);
lean_dec(v_disch_2165_);
lean_dec(v_dsimpTk_2123_);
lean_dec(v_cfg_2106_);
lean_dec(v_x_2098_);
v___x_2172_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
lean_ctor_set(v___x_2173_, 1, v___y_2167_);
return v___x_2173_;
}
else
{
lean_object* v_only_x3f_2174_; lean_object* v___x_2175_; 
v_only_x3f_2174_ = l_Lean_Syntax_getArg(v___x_2169_, v___x_2122_);
lean_dec(v___x_2169_);
v___x_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2175_, 0, v_only_x3f_2174_);
v___y_2145_ = v_disch_2165_;
v___y_2146_ = v___x_2168_;
v_only_x3f_2147_ = v___x_2175_;
v___y_2148_ = v___y_2166_;
v___y_2149_ = v___y_2167_;
goto v___jp_2144_;
}
}
else
{
lean_object* v___x_2176_; 
lean_dec(v___x_2169_);
v___x_2176_ = lean_box(0);
v___y_2145_ = v_disch_2165_;
v___y_2146_ = v___x_2168_;
v_only_x3f_2147_ = v___x_2176_;
v___y_2148_ = v___y_2166_;
v___y_2149_ = v___y_2167_;
goto v___jp_2144_;
}
}
}
v___jp_2107_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_box(0);
v___x_2117_ = l_Lean_Fmt_fmtSimpLike(v___y_2109_, v_cfg_2106_, v___y_2112_, v___y_2114_, v___y_2113_, v___y_2115_, v___y_2108_, v___x_2116_, v___y_2110_, v___y_2111_);
return v___x_2117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDSimp___boxed(lean_object* v_x_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Fmt_fmtConvDSimp(v_x_2189_, v_a_2190_, v_a_2191_);
lean_dec_ref(v_a_2190_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1(){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2199_ = l_Lean_Fmt_fmtAttribute;
v___x_2200_ = ((lean_object*)(l_Lean_Fmt_fmtConvDSimp___closed__1));
v___x_2201_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___closed__1));
v___x_2202_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvDSimp___boxed), 3, 0);
v___x_2203_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2199_, v___x_2200_, v___x_2201_, v___x_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1___boxed(lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1();
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSimpTrace(lean_object* v_x_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2222_ = ((lean_object*)(l_Lean_Fmt_fmtConvSimpTrace___closed__1));
lean_inc(v_x_2219_);
v___x_2223_ = l_Lean_Syntax_isOfKind(v_x_2219_, v___x_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec(v_x_2219_);
v___x_2224_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set(v___x_2225_, 1, v_a_2221_);
return v___x_2225_;
}
else
{
lean_object* v___x_2226_; lean_object* v_cfg_2227_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2226_ = lean_unsigned_to_nat(1u);
v_cfg_2227_ = l_Lean_Syntax_getArg(v_x_2219_, v___x_2226_);
v___x_2239_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__3));
lean_inc(v_cfg_2227_);
v___x_2240_ = l_Lean_Syntax_isOfKind(v_cfg_2227_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec(v_cfg_2227_);
lean_dec(v_x_2219_);
v___x_2241_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v_a_2221_);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; lean_object* v_tk_2244_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v_lbTk_x3f_2248_; lean_object* v_args_x3f_2249_; lean_object* v_rbTk_x3f_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___x_2264_; lean_object* v___y_2266_; lean_object* v_only_x3f_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v_disch_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2243_ = lean_unsigned_to_nat(0u);
v_tk_2244_ = l_Lean_Syntax_getArg(v_x_2219_, v___x_2243_);
v___x_2264_ = lean_unsigned_to_nat(2u);
v___x_2302_ = l_Lean_Syntax_getArg(v_x_2219_, v___x_2264_);
v___x_2303_ = l_Lean_Syntax_isNone(v___x_2302_);
if (v___x_2303_ == 0)
{
uint8_t v___x_2304_; 
lean_inc(v___x_2302_);
v___x_2304_ = l_Lean_Syntax_matchesNull(v___x_2302_, v___x_2226_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_dec(v___x_2302_);
lean_dec(v_tk_2244_);
lean_dec(v_cfg_2227_);
lean_dec(v_x_2219_);
v___x_2305_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v_a_2221_);
return v___x_2306_;
}
else
{
lean_object* v_disch_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v_disch_2307_ = l_Lean_Syntax_getArg(v___x_2302_, v___x_2243_);
lean_dec(v___x_2302_);
v___x_2308_ = ((lean_object*)(l_Lean_Fmt_fmtConvSimp___closed__3));
lean_inc(v_disch_2307_);
v___x_2309_ = l_Lean_Syntax_isOfKind(v_disch_2307_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_dec(v_disch_2307_);
lean_dec(v_tk_2244_);
lean_dec(v_cfg_2227_);
lean_dec(v_x_2219_);
v___x_2310_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v_a_2221_);
return v___x_2311_;
}
else
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2312_, 0, v_disch_2307_);
v_disch_2290_ = v___x_2312_;
v___y_2291_ = v_a_2220_;
v___y_2292_ = v_a_2221_;
goto v___jp_2289_;
}
}
}
else
{
lean_object* v___x_2313_; 
lean_dec(v___x_2302_);
v___x_2313_ = lean_box(0);
v_disch_2290_ = v___x_2313_;
v___y_2291_ = v_a_2220_;
v___y_2292_ = v_a_2221_;
goto v___jp_2289_;
}
v___jp_2245_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_mk_empty_array_with_capacity(v___x_2226_);
v___x_2254_ = lean_array_push(v___x_2253_, v_tk_2244_);
if (lean_obj_tag(v_args_x3f_2249_) == 0)
{
lean_object* v___x_2255_; 
v___x_2255_ = lean_box(0);
v___y_2229_ = v___y_2252_;
v___y_2230_ = v_lbTk_x3f_2248_;
v___y_2231_ = v___x_2254_;
v___y_2232_ = v___y_2251_;
v___y_2233_ = v___y_2246_;
v___y_2234_ = v___y_2247_;
v___y_2235_ = v_rbTk_x3f_2250_;
v___y_2236_ = v___x_2255_;
goto v___jp_2228_;
}
else
{
lean_object* v_val_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
v_val_2256_ = lean_ctor_get(v_args_x3f_2249_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_args_x3f_2249_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v_args_x3f_2249_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_val_2256_);
lean_dec(v_args_x3f_2249_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_val_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
v___y_2229_ = v___y_2252_;
v___y_2230_ = v_lbTk_x3f_2248_;
v___y_2231_ = v___x_2254_;
v___y_2232_ = v___y_2251_;
v___y_2233_ = v___y_2246_;
v___y_2234_ = v___y_2247_;
v___y_2235_ = v_rbTk_x3f_2250_;
v___y_2236_ = v___x_2261_;
goto v___jp_2228_;
}
}
}
}
v___jp_2265_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2270_ = lean_unsigned_to_nat(4u);
v___x_2271_ = l_Lean_Syntax_getArg(v_x_2219_, v___x_2270_);
lean_dec(v_x_2219_);
v___x_2272_ = l_Lean_Syntax_isNone(v___x_2271_);
if (v___x_2272_ == 0)
{
uint8_t v___x_2273_; 
lean_inc(v___x_2271_);
v___x_2273_ = l_Lean_Syntax_matchesNull(v___x_2271_, v___x_2226_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_dec(v___x_2271_);
lean_dec(v_only_x3f_2267_);
lean_dec(v___y_2266_);
lean_dec(v_tk_2244_);
lean_dec(v_cfg_2227_);
v___x_2274_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___y_2269_);
return v___x_2275_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2276_ = l_Lean_Syntax_getArg(v___x_2271_, v___x_2243_);
lean_dec(v___x_2271_);
v___x_2277_ = ((lean_object*)(l_Lean_Fmt_fmtConvSimpTrace___closed__3));
lean_inc(v___x_2276_);
v___x_2278_ = l_Lean_Syntax_isOfKind(v___x_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec(v___x_2276_);
lean_dec(v_only_x3f_2267_);
lean_dec(v___y_2266_);
lean_dec(v_tk_2244_);
lean_dec(v_cfg_2227_);
v___x_2279_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v___y_2269_);
return v___x_2280_;
}
else
{
lean_object* v_lbTk_x3f_2281_; lean_object* v___x_2282_; lean_object* v_rbTk_x3f_2283_; lean_object* v_args_x3f_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v_lbTk_x3f_2281_ = l_Lean_Syntax_getArg(v___x_2276_, v___x_2243_);
v___x_2282_ = l_Lean_Syntax_getArg(v___x_2276_, v___x_2226_);
v_rbTk_x3f_2283_ = l_Lean_Syntax_getArg(v___x_2276_, v___x_2264_);
lean_dec(v___x_2276_);
v_args_x3f_2284_ = l_Lean_Syntax_getArgs(v___x_2282_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2285_, 0, v_lbTk_x3f_2281_);
v___x_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2286_, 0, v_args_x3f_2284_);
v___x_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2287_, 0, v_rbTk_x3f_2283_);
v___y_2246_ = v___y_2266_;
v___y_2247_ = v_only_x3f_2267_;
v_lbTk_x3f_2248_ = v___x_2285_;
v_args_x3f_2249_ = v___x_2286_;
v_rbTk_x3f_2250_ = v___x_2287_;
v___y_2251_ = v___y_2268_;
v___y_2252_ = v___y_2269_;
goto v___jp_2245_;
}
}
}
else
{
lean_object* v___x_2288_; 
lean_dec(v___x_2271_);
v___x_2288_ = lean_box(0);
v___y_2246_ = v___y_2266_;
v___y_2247_ = v_only_x3f_2267_;
v_lbTk_x3f_2248_ = v___x_2288_;
v_args_x3f_2249_ = v___x_2288_;
v_rbTk_x3f_2250_ = v___x_2288_;
v___y_2251_ = v___y_2268_;
v___y_2252_ = v___y_2269_;
goto v___jp_2245_;
}
}
v___jp_2289_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2293_ = lean_unsigned_to_nat(3u);
v___x_2294_ = l_Lean_Syntax_getArg(v_x_2219_, v___x_2293_);
v___x_2295_ = l_Lean_Syntax_isNone(v___x_2294_);
if (v___x_2295_ == 0)
{
uint8_t v___x_2296_; 
lean_inc(v___x_2294_);
v___x_2296_ = l_Lean_Syntax_matchesNull(v___x_2294_, v___x_2226_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec(v___x_2294_);
lean_dec(v_disch_2290_);
lean_dec(v_tk_2244_);
lean_dec(v_cfg_2227_);
lean_dec(v_x_2219_);
v___x_2297_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___y_2292_);
return v___x_2298_;
}
else
{
lean_object* v_only_x3f_2299_; lean_object* v___x_2300_; 
v_only_x3f_2299_ = l_Lean_Syntax_getArg(v___x_2294_, v___x_2243_);
lean_dec(v___x_2294_);
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_only_x3f_2299_);
v___y_2266_ = v_disch_2290_;
v_only_x3f_2267_ = v___x_2300_;
v___y_2268_ = v___y_2291_;
v___y_2269_ = v___y_2292_;
goto v___jp_2265_;
}
}
else
{
lean_object* v___x_2301_; 
lean_dec(v___x_2294_);
v___x_2301_ = lean_box(0);
v___y_2266_ = v_disch_2290_;
v_only_x3f_2267_ = v___x_2301_;
v___y_2268_ = v___y_2291_;
v___y_2269_ = v___y_2292_;
goto v___jp_2265_;
}
}
}
v___jp_2228_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_box(0);
v___x_2238_ = l_Lean_Fmt_fmtSimpLike(v___y_2231_, v_cfg_2227_, v___y_2233_, v___y_2234_, v___y_2230_, v___y_2236_, v___y_2235_, v___x_2237_, v___y_2232_, v___y_2229_);
return v___x_2238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvSimpTrace___boxed(lean_object* v_x_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_Fmt_fmtConvSimpTrace(v_x_2314_, v_a_2315_, v_a_2316_);
lean_dec_ref(v_a_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1(){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2324_ = l_Lean_Fmt_fmtAttribute;
v___x_2325_ = ((lean_object*)(l_Lean_Fmt_fmtConvSimpTrace___closed__1));
v___x_2326_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___closed__1));
v___x_2327_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvSimpTrace___boxed), 3, 0);
v___x_2328_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2324_, v___x_2325_, v___x_2326_, v___x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1___boxed(lean_object* v_a_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1();
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDSimpTrace(lean_object* v_x_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2347_ = ((lean_object*)(l_Lean_Fmt_fmtConvDSimpTrace___closed__1));
lean_inc(v_x_2344_);
v___x_2348_ = l_Lean_Syntax_isOfKind(v_x_2344_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec(v_x_2344_);
v___x_2349_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v_a_2346_);
return v___x_2350_;
}
else
{
lean_object* v___x_2351_; lean_object* v_cfg_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2351_ = lean_unsigned_to_nat(1u);
v_cfg_2352_ = l_Lean_Syntax_getArg(v_x_2344_, v___x_2351_);
v___x_2353_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__3));
lean_inc(v_cfg_2352_);
v___x_2354_ = l_Lean_Syntax_isOfKind(v_cfg_2352_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec(v_cfg_2352_);
lean_dec(v_x_2344_);
v___x_2355_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
lean_ctor_set(v___x_2356_, 1, v_a_2346_);
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; lean_object* v_tk_2358_; lean_object* v___y_2360_; lean_object* v_lbTk_x3f_2361_; lean_object* v_args_x3f_2362_; lean_object* v_rbTk_x3f_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___x_2379_; lean_object* v_only_x3f_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2357_ = lean_unsigned_to_nat(0u);
v_tk_2358_ = l_Lean_Syntax_getArg(v_x_2344_, v___x_2357_);
v___x_2379_ = lean_unsigned_to_nat(2u);
v___x_2403_ = l_Lean_Syntax_getArg(v_x_2344_, v___x_2379_);
v___x_2404_ = l_Lean_Syntax_isNone(v___x_2403_);
if (v___x_2404_ == 0)
{
uint8_t v___x_2405_; 
lean_inc(v___x_2403_);
v___x_2405_ = l_Lean_Syntax_matchesNull(v___x_2403_, v___x_2351_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec(v___x_2403_);
lean_dec(v_tk_2358_);
lean_dec(v_cfg_2352_);
lean_dec(v_x_2344_);
v___x_2406_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v_a_2346_);
return v___x_2407_;
}
else
{
lean_object* v_only_x3f_2408_; lean_object* v___x_2409_; 
v_only_x3f_2408_ = l_Lean_Syntax_getArg(v___x_2403_, v___x_2357_);
lean_dec(v___x_2403_);
v___x_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2409_, 0, v_only_x3f_2408_);
v_only_x3f_2381_ = v___x_2409_;
v___y_2382_ = v_a_2345_;
v___y_2383_ = v_a_2346_;
goto v___jp_2380_;
}
}
else
{
lean_object* v___x_2410_; 
lean_dec(v___x_2403_);
v___x_2410_ = lean_box(0);
v_only_x3f_2381_ = v___x_2410_;
v___y_2382_ = v_a_2345_;
v___y_2383_ = v_a_2346_;
goto v___jp_2380_;
}
v___jp_2359_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = lean_mk_empty_array_with_capacity(v___x_2351_);
v___x_2367_ = lean_array_push(v___x_2366_, v_tk_2358_);
v___x_2368_ = lean_box(0);
if (lean_obj_tag(v_args_x3f_2362_) == 0)
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_Fmt_fmtSimpLike(v___x_2367_, v_cfg_2352_, v___x_2368_, v___y_2360_, v_lbTk_x3f_2361_, v___x_2368_, v_rbTk_x3f_2363_, v___x_2368_, v___y_2364_, v___y_2365_);
return v___x_2369_;
}
else
{
lean_object* v_val_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2378_; 
v_val_2370_ = lean_ctor_get(v_args_x3f_2362_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_args_x3f_2362_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2372_ = v_args_x3f_2362_;
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_val_2370_);
lean_dec(v_args_x3f_2362_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_val_2370_);
v___x_2375_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_Fmt_fmtSimpLike(v___x_2367_, v_cfg_2352_, v___x_2368_, v___y_2360_, v_lbTk_x3f_2361_, v___x_2375_, v_rbTk_x3f_2363_, v___x_2368_, v___y_2364_, v___y_2365_);
return v___x_2376_;
}
}
}
}
v___jp_2380_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2384_ = lean_unsigned_to_nat(3u);
v___x_2385_ = l_Lean_Syntax_getArg(v_x_2344_, v___x_2384_);
lean_dec(v_x_2344_);
v___x_2386_ = l_Lean_Syntax_isNone(v___x_2385_);
if (v___x_2386_ == 0)
{
uint8_t v___x_2387_; 
lean_inc(v___x_2385_);
v___x_2387_ = l_Lean_Syntax_matchesNull(v___x_2385_, v___x_2351_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec(v___x_2385_);
lean_dec(v_only_x3f_2381_);
lean_dec(v_tk_2358_);
lean_dec(v_cfg_2352_);
v___x_2388_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v___y_2383_);
return v___x_2389_;
}
else
{
lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2390_ = l_Lean_Syntax_getArg(v___x_2385_, v___x_2357_);
lean_dec(v___x_2385_);
v___x_2391_ = ((lean_object*)(l_Lean_Fmt_fmtConvDSimpTrace___closed__3));
lean_inc(v___x_2390_);
v___x_2392_ = l_Lean_Syntax_isOfKind(v___x_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec(v___x_2390_);
lean_dec(v_only_x3f_2381_);
lean_dec(v_tk_2358_);
lean_dec(v_cfg_2352_);
v___x_2393_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
lean_ctor_set(v___x_2394_, 1, v___y_2383_);
return v___x_2394_;
}
else
{
lean_object* v_lbTk_x3f_2395_; lean_object* v___x_2396_; lean_object* v_rbTk_x3f_2397_; lean_object* v_args_x3f_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_lbTk_x3f_2395_ = l_Lean_Syntax_getArg(v___x_2390_, v___x_2357_);
v___x_2396_ = l_Lean_Syntax_getArg(v___x_2390_, v___x_2351_);
v_rbTk_x3f_2397_ = l_Lean_Syntax_getArg(v___x_2390_, v___x_2379_);
lean_dec(v___x_2390_);
v_args_x3f_2398_ = l_Lean_Syntax_getArgs(v___x_2396_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v_lbTk_x3f_2395_);
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_args_x3f_2398_);
v___x_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2401_, 0, v_rbTk_x3f_2397_);
v___y_2360_ = v_only_x3f_2381_;
v_lbTk_x3f_2361_ = v___x_2399_;
v_args_x3f_2362_ = v___x_2400_;
v_rbTk_x3f_2363_ = v___x_2401_;
v___y_2364_ = v___y_2382_;
v___y_2365_ = v___y_2383_;
goto v___jp_2359_;
}
}
}
else
{
lean_object* v___x_2402_; 
lean_dec(v___x_2385_);
v___x_2402_ = lean_box(0);
v___y_2360_ = v_only_x3f_2381_;
v_lbTk_x3f_2361_ = v___x_2402_;
v_args_x3f_2362_ = v___x_2402_;
v_rbTk_x3f_2363_ = v___x_2402_;
v___y_2364_ = v___y_2382_;
v___y_2365_ = v___y_2383_;
goto v___jp_2359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvDSimpTrace___boxed(lean_object* v_x_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_Fmt_fmtConvDSimpTrace(v_x_2411_, v_a_2412_, v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1(){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2421_ = l_Lean_Fmt_fmtAttribute;
v___x_2422_ = ((lean_object*)(l_Lean_Fmt_fmtConvDSimpTrace___closed__1));
v___x_2423_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___closed__1));
v___x_2424_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvDSimpTrace___boxed), 3, 0);
v___x_2425_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2421_, v___x_2422_, v___x_2423_, v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1___boxed(lean_object* v_a_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1();
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvPattern(lean_object* v_x_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; 
v___x_2438_ = ((lean_object*)(l_Lean_Fmt_fmtConvPattern___closed__1));
lean_inc(v_x_2435_);
v___x_2439_ = l_Lean_Syntax_isOfKind(v_x_2435_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_dec(v_x_2435_);
v___x_2469_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v_a_2437_);
return v___x_2470_;
}
else
{
lean_object* v___x_2471_; lean_object* v_patternTk_2472_; lean_object* v_occs_x3f_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2471_ = lean_unsigned_to_nat(0u);
v_patternTk_2472_ = l_Lean_Syntax_getArg(v_x_2435_, v___x_2471_);
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = l_Lean_Syntax_getArg(v_x_2435_, v___x_2491_);
v___x_2493_ = l_Lean_Syntax_isNone(v___x_2492_);
if (v___x_2493_ == 0)
{
uint8_t v___x_2494_; 
lean_inc(v___x_2492_);
v___x_2494_ = l_Lean_Syntax_matchesNull(v___x_2492_, v___x_2491_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_dec(v___x_2492_);
lean_dec(v_patternTk_2472_);
lean_dec(v_x_2435_);
v___x_2495_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
lean_ctor_set(v___x_2496_, 1, v_a_2437_);
return v___x_2496_;
}
else
{
lean_object* v_occs_x3f_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v_occs_x3f_2497_ = l_Lean_Syntax_getArg(v___x_2492_, v___x_2471_);
lean_dec(v___x_2492_);
v___x_2498_ = ((lean_object*)(l_Lean_Fmt_fmtConvOccs___closed__1));
lean_inc(v_occs_x3f_2497_);
v___x_2499_ = l_Lean_Syntax_isOfKind(v_occs_x3f_2497_, v___x_2498_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_dec(v_occs_x3f_2497_);
lean_dec(v_patternTk_2472_);
lean_dec(v_x_2435_);
v___x_2500_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v_a_2437_);
return v___x_2501_;
}
else
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_occs_x3f_2497_);
v_occs_x3f_2474_ = v___x_2502_;
v___y_2475_ = v_a_2436_;
v___y_2476_ = v_a_2437_;
goto v___jp_2473_;
}
}
}
else
{
lean_object* v___x_2503_; 
lean_dec(v___x_2492_);
v___x_2503_ = lean_box(0);
v_occs_x3f_2474_ = v___x_2503_;
v___y_2475_ = v_a_2436_;
v___y_2476_ = v_a_2437_;
goto v___jp_2473_;
}
v___jp_2473_:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_Fmt_fmt(v_patternTk_2472_, v___y_2475_, v___y_2476_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v_a_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
v_a_2479_ = lean_ctor_get(v___x_2477_, 1);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2477_, 2);
v___x_2480_ = lean_unsigned_to_nat(2u);
v___x_2481_ = l_Lean_Syntax_getArg(v_x_2435_, v___x_2480_);
lean_dec(v_x_2435_);
if (lean_obj_tag(v_occs_x3f_2474_) == 0)
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_box(0);
v___y_2441_ = v___y_2475_;
v___y_2442_ = v___x_2480_;
v___y_2443_ = v___x_2481_;
v___y_2444_ = v_a_2478_;
v___y_2445_ = v_a_2479_;
v___y_2446_ = v___x_2482_;
goto v___jp_2440_;
}
else
{
lean_object* v_val_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
v_val_2483_ = lean_ctor_get(v_occs_x3f_2474_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_occs_x3f_2474_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v_occs_x3f_2474_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_val_2483_);
lean_dec(v_occs_x3f_2474_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_val_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
v___y_2441_ = v___y_2475_;
v___y_2442_ = v___x_2480_;
v___y_2443_ = v___x_2481_;
v___y_2444_ = v_a_2478_;
v___y_2445_ = v_a_2479_;
v___y_2446_ = v___x_2488_;
goto v___jp_2440_;
}
}
}
}
else
{
lean_dec(v_occs_x3f_2474_);
lean_dec(v_x_2435_);
return v___x_2477_;
}
}
}
v___jp_2440_:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_Fmt_fmt_x3f(v___y_2446_, v___y_2441_, v___y_2445_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v_a_2449_; uint8_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
v_a_2449_ = lean_ctor_get(v___x_2447_, 1);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2447_, 2);
v___x_2450_ = 0;
v___x_2451_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2451_, 0, v___x_2439_);
lean_ctor_set_uint8(v___x_2451_, 1, v___x_2450_);
lean_ctor_set_uint8(v___x_2451_, 2, v___x_2450_);
lean_ctor_set_uint8(v___x_2451_, 3, v___x_2450_);
v___x_2452_ = l_Lean_Fmt_fmt(v___y_2443_, v___y_2441_, v_a_2449_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2468_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_a_2454_ = lean_ctor_get(v___x_2452_, 1);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2456_ = v___x_2452_;
v_isShared_2457_ = v_isSharedCheck_2468_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2468_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2458_ = lean_mk_empty_array_with_capacity(v___y_2442_);
lean_inc_ref(v___x_2458_);
v___x_2459_ = lean_array_push(v___x_2458_, v___y_2444_);
v___x_2460_ = lean_array_push(v___x_2459_, v_a_2448_);
lean_inc_ref(v___x_2451_);
v___x_2461_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2460_, v___x_2451_);
v___x_2462_ = lean_array_push(v___x_2458_, v___x_2461_);
v___x_2463_ = lean_array_push(v___x_2462_, v_a_2453_);
v___x_2464_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2463_, v___x_2451_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2464_);
v___x_2466_ = v___x_2456_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_a_2454_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
else
{
lean_dec_ref_known(v___x_2451_, 0);
lean_dec(v_a_2448_);
lean_dec_ref(v___y_2444_);
return v___x_2452_;
}
}
else
{
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
return v___x_2447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvPattern___boxed(lean_object* v_x_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_Fmt_fmtConvPattern(v_x_2504_, v_a_2505_, v_a_2506_);
lean_dec_ref(v_a_2505_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1(){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2514_ = l_Lean_Fmt_fmtAttribute;
v___x_2515_ = ((lean_object*)(l_Lean_Fmt_fmtConvPattern___closed__1));
v___x_2516_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___closed__1));
v___x_2517_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvPattern___boxed), 3, 0);
v___x_2518_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2514_, v___x_2515_, v___x_2516_, v___x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1___boxed(lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1();
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvExtractLets(lean_object* v_x_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2531_ = ((lean_object*)(l_Lean_Fmt_fmtConvExtractLets___closed__1));
lean_inc(v_x_2528_);
v___x_2532_ = l_Lean_Syntax_isOfKind(v_x_2528_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_dec(v_x_2528_);
v___x_2533_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
lean_ctor_set(v___x_2534_, 1, v_a_2530_);
return v___x_2534_;
}
else
{
lean_object* v___x_2535_; lean_object* v_cfg_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2535_ = lean_unsigned_to_nat(1u);
v_cfg_2536_ = l_Lean_Syntax_getArg(v_x_2528_, v___x_2535_);
v___x_2537_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__3));
lean_inc(v_cfg_2536_);
v___x_2538_ = l_Lean_Syntax_isOfKind(v_cfg_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
lean_dec(v_cfg_2536_);
lean_dec(v_x_2528_);
v___x_2539_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
lean_ctor_set(v___x_2540_, 1, v_a_2530_);
return v___x_2540_;
}
else
{
lean_object* v___x_2541_; lean_object* v_tk_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_args_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2541_ = lean_unsigned_to_nat(0u);
v_tk_2542_ = l_Lean_Syntax_getArg(v_x_2528_, v___x_2541_);
v___x_2543_ = lean_unsigned_to_nat(2u);
v___x_2544_ = l_Lean_Syntax_getArg(v_x_2528_, v___x_2543_);
lean_dec(v_x_2528_);
v_args_2545_ = l_Lean_Syntax_getArgs(v___x_2544_);
lean_dec(v___x_2544_);
v___x_2546_ = lean_box(0);
v___x_2547_ = l_Lean_Fmt_fmtExtractLetsLike___redArg(v_tk_2542_, v_cfg_2536_, v_args_2545_, v___x_2546_, v_a_2529_, v_a_2530_);
return v___x_2547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvExtractLets___boxed(lean_object* v_x_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_Fmt_fmtConvExtractLets(v_x_2548_, v_a_2549_, v_a_2550_);
lean_dec_ref(v_a_2549_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1(){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2558_ = l_Lean_Fmt_fmtAttribute;
v___x_2559_ = ((lean_object*)(l_Lean_Fmt_fmtConvExtractLets___closed__1));
v___x_2560_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___closed__1));
v___x_2561_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvExtractLets___boxed), 3, 0);
v___x_2562_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2558_, v___x_2559_, v___x_2560_, v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1___boxed(lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1();
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvLiftLets(lean_object* v_x_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v___x_2575_; uint8_t v___x_2576_; 
v___x_2575_ = ((lean_object*)(l_Lean_Fmt_fmtConvLiftLets___closed__1));
lean_inc(v_x_2572_);
v___x_2576_ = l_Lean_Syntax_isOfKind(v_x_2572_, v___x_2575_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec(v_x_2572_);
v___x_2577_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
lean_ctor_set(v___x_2578_, 1, v_a_2574_);
return v___x_2578_;
}
else
{
lean_object* v___x_2579_; lean_object* v_cfg_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2579_ = lean_unsigned_to_nat(1u);
v_cfg_2580_ = l_Lean_Syntax_getArg(v_x_2572_, v___x_2579_);
v___x_2581_ = ((lean_object*)(l_Lean_Fmt_fmtConvRw___closed__3));
lean_inc(v_cfg_2580_);
v___x_2582_ = l_Lean_Syntax_isOfKind(v_cfg_2580_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_dec(v_cfg_2580_);
lean_dec(v_x_2572_);
v___x_2583_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v_a_2574_);
return v___x_2584_;
}
else
{
lean_object* v___x_2585_; lean_object* v_tk_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_unsigned_to_nat(0u);
v_tk_2586_ = l_Lean_Syntax_getArg(v_x_2572_, v___x_2585_);
lean_dec(v_x_2572_);
v___x_2587_ = l_Lean_Fmt_fmtLiftLetsLike(v_tk_2586_, v_cfg_2580_, v_a_2573_, v_a_2574_);
return v___x_2587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvLiftLets___boxed(lean_object* v_x_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_Fmt_fmtConvLiftLets(v_x_2588_, v_a_2589_, v_a_2590_);
lean_dec_ref(v_a_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1(){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2598_ = l_Lean_Fmt_fmtAttribute;
v___x_2599_ = ((lean_object*)(l_Lean_Fmt_fmtConvLiftLets___closed__1));
v___x_2600_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___closed__1));
v___x_2601_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvLiftLets___boxed), 3, 0);
v___x_2602_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2598_, v___x_2599_, v___x_2600_, v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1___boxed(lean_object* v_a_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1();
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnterPattern(lean_object* v_x_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v___x_2615_; uint8_t v___x_2616_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; 
v___x_2615_ = ((lean_object*)(l_Lean_Fmt_fmtConvEnterPattern___closed__1));
lean_inc(v_x_2612_);
v___x_2616_ = l_Lean_Syntax_isOfKind(v_x_2612_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_dec(v_x_2612_);
v___x_2646_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
lean_ctor_set(v___x_2647_, 1, v_a_2614_);
return v___x_2647_;
}
else
{
lean_object* v___x_2648_; lean_object* v_inTk_2649_; lean_object* v_occs_x3f_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2648_ = lean_unsigned_to_nat(0u);
v_inTk_2649_ = l_Lean_Syntax_getArg(v_x_2612_, v___x_2648_);
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = l_Lean_Syntax_getArg(v_x_2612_, v___x_2668_);
v___x_2670_ = l_Lean_Syntax_isNone(v___x_2669_);
if (v___x_2670_ == 0)
{
uint8_t v___x_2671_; 
lean_inc(v___x_2669_);
v___x_2671_ = l_Lean_Syntax_matchesNull(v___x_2669_, v___x_2668_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_dec(v___x_2669_);
lean_dec(v_inTk_2649_);
lean_dec(v_x_2612_);
v___x_2672_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
lean_ctor_set(v___x_2673_, 1, v_a_2614_);
return v___x_2673_;
}
else
{
lean_object* v_occs_x3f_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v_occs_x3f_2674_ = l_Lean_Syntax_getArg(v___x_2669_, v___x_2648_);
lean_dec(v___x_2669_);
v___x_2675_ = ((lean_object*)(l_Lean_Fmt_fmtConvOccs___closed__1));
lean_inc(v_occs_x3f_2674_);
v___x_2676_ = l_Lean_Syntax_isOfKind(v_occs_x3f_2674_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec(v_occs_x3f_2674_);
lean_dec(v_inTk_2649_);
lean_dec(v_x_2612_);
v___x_2677_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
lean_ctor_set(v___x_2678_, 1, v_a_2614_);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_occs_x3f_2674_);
v_occs_x3f_2651_ = v___x_2679_;
v___y_2652_ = v_a_2613_;
v___y_2653_ = v_a_2614_;
goto v___jp_2650_;
}
}
}
else
{
lean_object* v___x_2680_; 
lean_dec(v___x_2669_);
v___x_2680_ = lean_box(0);
v_occs_x3f_2651_ = v___x_2680_;
v___y_2652_ = v_a_2613_;
v___y_2653_ = v_a_2614_;
goto v___jp_2650_;
}
v___jp_2650_:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_Fmt_fmt(v_inTk_2649_, v___y_2652_, v___y_2653_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v_a_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
v_a_2656_ = lean_ctor_get(v___x_2654_, 1);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2654_, 2);
v___x_2657_ = lean_unsigned_to_nat(2u);
v___x_2658_ = l_Lean_Syntax_getArg(v_x_2612_, v___x_2657_);
lean_dec(v_x_2612_);
if (lean_obj_tag(v_occs_x3f_2651_) == 0)
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_box(0);
v___y_2618_ = v___x_2658_;
v___y_2619_ = v___y_2652_;
v___y_2620_ = v_a_2656_;
v___y_2621_ = v_a_2655_;
v___y_2622_ = v___x_2657_;
v___y_2623_ = v___x_2659_;
goto v___jp_2617_;
}
else
{
lean_object* v_val_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
v_val_2660_ = lean_ctor_get(v_occs_x3f_2651_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v_occs_x3f_2651_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v_occs_x3f_2651_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_val_2660_);
lean_dec(v_occs_x3f_2651_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_val_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
v___y_2618_ = v___x_2658_;
v___y_2619_ = v___y_2652_;
v___y_2620_ = v_a_2656_;
v___y_2621_ = v_a_2655_;
v___y_2622_ = v___x_2657_;
v___y_2623_ = v___x_2665_;
goto v___jp_2617_;
}
}
}
}
else
{
lean_dec(v_occs_x3f_2651_);
lean_dec(v_x_2612_);
return v___x_2654_;
}
}
}
v___jp_2617_:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_Fmt_fmt_x3f(v___y_2623_, v___y_2619_, v___y_2620_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v_a_2626_; uint8_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
v_a_2626_ = lean_ctor_get(v___x_2624_, 1);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2624_, 2);
v___x_2627_ = 0;
v___x_2628_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2628_, 0, v___x_2616_);
lean_ctor_set_uint8(v___x_2628_, 1, v___x_2627_);
lean_ctor_set_uint8(v___x_2628_, 2, v___x_2627_);
lean_ctor_set_uint8(v___x_2628_, 3, v___x_2627_);
v___x_2629_ = l_Lean_Fmt_fmt(v___y_2618_, v___y_2619_, v_a_2626_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2645_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
v_a_2631_ = lean_ctor_get(v___x_2629_, 1);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2633_ = v___x_2629_;
v_isShared_2634_ = v_isSharedCheck_2645_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_inc(v_a_2630_);
lean_dec(v___x_2629_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2645_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
v___x_2635_ = lean_mk_empty_array_with_capacity(v___y_2622_);
lean_inc_ref(v___x_2635_);
v___x_2636_ = lean_array_push(v___x_2635_, v___y_2621_);
v___x_2637_ = lean_array_push(v___x_2636_, v_a_2625_);
lean_inc_ref(v___x_2628_);
v___x_2638_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2637_, v___x_2628_);
v___x_2639_ = lean_array_push(v___x_2635_, v___x_2638_);
v___x_2640_ = lean_array_push(v___x_2639_, v_a_2630_);
v___x_2641_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2640_, v___x_2628_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_2641_);
v___x_2643_ = v___x_2633_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_a_2631_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
else
{
lean_dec_ref_known(v___x_2628_, 0);
lean_dec(v_a_2625_);
lean_dec_ref(v___y_2621_);
return v___x_2629_;
}
}
else
{
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2618_);
return v___x_2624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnterPattern___boxed(lean_object* v_x_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Lean_Fmt_fmtConvEnterPattern(v_x_2681_, v_a_2682_, v_a_2683_);
lean_dec_ref(v_a_2682_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1(){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2691_ = l_Lean_Fmt_fmtAttribute;
v___x_2692_ = ((lean_object*)(l_Lean_Fmt_fmtConvEnterPattern___closed__1));
v___x_2693_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___closed__1));
v___x_2694_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvEnterPattern___boxed), 3, 0);
v___x_2695_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2691_, v___x_2692_, v___x_2693_, v___x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1___boxed(lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1();
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnterArg(lean_object* v_x_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2712_ = ((lean_object*)(l_Lean_Fmt_fmtConvEnterArg___closed__1));
lean_inc(v_x_2709_);
v___x_2713_ = l_Lean_Syntax_isOfKind(v_x_2709_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_dec(v_x_2709_);
v___x_2714_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
lean_ctor_set(v___x_2715_, 1, v_a_2711_);
return v___x_2715_;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2716_ = lean_unsigned_to_nat(0u);
v___x_2717_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_2716_);
lean_dec(v_x_2709_);
v___x_2718_ = ((lean_object*)(l_Lean_Fmt_fmtConvEnterArg___closed__3));
lean_inc(v___x_2717_);
v___x_2719_ = l_Lean_Syntax_isOfKind(v___x_2717_, v___x_2718_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = ((lean_object*)(l_Lean_Fmt_fmtConvArgArg___closed__3));
lean_inc(v___x_2717_);
v___x_2721_ = l_Lean_Syntax_isOfKind(v___x_2717_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2722_ = ((lean_object*)(l_Lean_Fmt_fmtConvEnterPattern___closed__1));
lean_inc(v___x_2717_);
v___x_2723_ = l_Lean_Syntax_isOfKind(v___x_2717_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec(v___x_2717_);
v___x_2724_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v_a_2711_);
return v___x_2725_;
}
else
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_Fmt_fmt(v___x_2717_, v_a_2710_, v_a_2711_);
return v___x_2726_;
}
}
else
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_Fmt_fmt(v___x_2717_, v_a_2710_, v_a_2711_);
return v___x_2727_;
}
}
else
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Fmt_fmt(v___x_2717_, v_a_2710_, v_a_2711_);
return v___x_2728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnterArg___boxed(lean_object* v_x_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_Fmt_fmtConvEnterArg(v_x_2729_, v_a_2730_, v_a_2731_);
lean_dec_ref(v_a_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1(){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2739_ = l_Lean_Fmt_fmtAttribute;
v___x_2740_ = ((lean_object*)(l_Lean_Fmt_fmtConvEnterArg___closed__1));
v___x_2741_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___closed__1));
v___x_2742_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvEnterArg___boxed), 3, 0);
v___x_2743_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2739_, v___x_2740_, v___x_2741_, v___x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1___boxed(lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1();
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnter(lean_object* v_x_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v___x_2757_; uint8_t v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_Lean_Fmt_fmtConvEnter___closed__1));
lean_inc(v_x_2754_);
v___x_2758_ = l_Lean_Syntax_isOfKind(v_x_2754_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_dec(v_x_2754_);
v___x_2759_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
lean_ctor_set(v___x_2760_, 1, v_a_2756_);
return v___x_2760_;
}
else
{
lean_object* v___x_2761_; lean_object* v_enterTk_2762_; lean_object* v___x_2763_; 
v___x_2761_ = lean_unsigned_to_nat(0u);
v_enterTk_2762_ = l_Lean_Syntax_getArg(v_x_2754_, v___x_2761_);
v___x_2763_ = l_Lean_Fmt_fmt(v_enterTk_2762_, v_a_2755_, v_a_2756_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v_a_2765_; lean_object* v___x_2766_; lean_object* v_lbTk_2767_; lean_object* v___x_2768_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
v_a_2765_ = lean_ctor_get(v___x_2763_, 1);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2763_, 2);
v___x_2766_ = lean_unsigned_to_nat(1u);
v_lbTk_2767_ = l_Lean_Syntax_getArg(v_x_2754_, v___x_2766_);
v___x_2768_ = l_Lean_Fmt_fmt(v_lbTk_2767_, v_a_2755_, v_a_2765_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v_a_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v_args_2773_; lean_object* v___x_2774_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
v_a_2770_ = lean_ctor_get(v___x_2768_, 1);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2768_, 2);
v___x_2771_ = lean_unsigned_to_nat(2u);
v___x_2772_ = l_Lean_Syntax_getArg(v_x_2754_, v___x_2771_);
v_args_2773_ = l_Lean_Syntax_getArgs(v___x_2772_);
lean_dec(v___x_2772_);
v___x_2774_ = l_Lean_Fmt_fmtTSepArray___redArg(v_args_2773_, v_a_2755_, v_a_2770_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v_rbTk_2778_; lean_object* v___x_2779_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
v_a_2776_ = lean_ctor_get(v___x_2774_, 1);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2774_, 2);
v___x_2777_ = lean_unsigned_to_nat(3u);
v_rbTk_2778_ = l_Lean_Syntax_getArg(v_x_2754_, v___x_2777_);
lean_dec(v_x_2754_);
v___x_2779_ = l_Lean_Fmt_fmt(v_rbTk_2778_, v_a_2755_, v_a_2776_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2797_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_a_2781_ = lean_ctor_get(v___x_2779_, 1);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2783_ = v___x_2779_;
v_isShared_2784_ = v_isSharedCheck_2797_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2797_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2785_ = ((lean_object*)(l_Lean_Fmt_fmtConvEnter___closed__2));
v___x_2786_ = 0;
v___x_2787_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2787_, 0, v___x_2786_);
lean_ctor_set_uint8(v___x_2787_, 1, v___x_2758_);
v___x_2788_ = l_Lean_Fmt_Layouts_collection(v___x_2785_, v_a_2769_, v_a_2775_, v_a_2780_, v___x_2787_);
lean_dec(v_a_2775_);
v___x_2789_ = lean_mk_empty_array_with_capacity(v___x_2771_);
v___x_2790_ = lean_array_push(v___x_2789_, v_a_2764_);
v___x_2791_ = lean_array_push(v___x_2790_, v___x_2788_);
v___x_2792_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2792_, 0, v___x_2758_);
lean_ctor_set_uint8(v___x_2792_, 1, v___x_2786_);
lean_ctor_set_uint8(v___x_2792_, 2, v___x_2786_);
lean_ctor_set_uint8(v___x_2792_, 3, v___x_2786_);
v___x_2793_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2791_, v___x_2792_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2793_);
v___x_2795_ = v___x_2783_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_a_2781_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
else
{
lean_dec(v_a_2775_);
lean_dec(v_a_2769_);
lean_dec(v_a_2764_);
return v___x_2779_;
}
}
else
{
lean_object* v_a_2798_; lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_a_2769_);
lean_dec(v_a_2764_);
lean_dec(v_x_2754_);
v_a_2798_ = lean_ctor_get(v___x_2774_, 0);
v_a_2799_ = lean_ctor_get(v___x_2774_, 1);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2774_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_inc(v_a_2798_);
lean_dec(v___x_2774_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2798_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
else
{
lean_dec(v_a_2764_);
lean_dec(v_x_2754_);
return v___x_2768_;
}
}
else
{
lean_dec(v_x_2754_);
return v___x_2763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvEnter___boxed(lean_object* v_x_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_Fmt_fmtConvEnter(v_x_2807_, v_a_2808_, v_a_2809_);
lean_dec_ref(v_a_2808_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1(){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2817_ = l_Lean_Fmt_fmtAttribute;
v___x_2818_ = ((lean_object*)(l_Lean_Fmt_fmtConvEnter___closed__1));
v___x_2819_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___closed__1));
v___x_2820_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvEnter___boxed), 3, 0);
v___x_2821_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2817_, v___x_2818_, v___x_2819_, v___x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1___boxed(lean_object* v_a_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1();
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__2(size_t v_sz_2824_, size_t v_i_2825_, lean_object* v_bs_2826_){
_start:
{
uint8_t v___x_2827_; 
v___x_2827_ = lean_usize_dec_lt(v_i_2825_, v_sz_2824_);
if (v___x_2827_ == 0)
{
return v_bs_2826_;
}
else
{
lean_object* v_v_2828_; lean_object* v_fst_2829_; lean_object* v___x_2830_; lean_object* v_bs_x27_2831_; size_t v___x_2832_; size_t v___x_2833_; lean_object* v___x_2834_; 
v_v_2828_ = lean_array_uget_borrowed(v_bs_2826_, v_i_2825_);
v_fst_2829_ = lean_ctor_get(v_v_2828_, 0);
lean_inc(v_fst_2829_);
v___x_2830_ = lean_unsigned_to_nat(0u);
v_bs_x27_2831_ = lean_array_uset(v_bs_2826_, v_i_2825_, v___x_2830_);
v___x_2832_ = ((size_t)1ULL);
v___x_2833_ = lean_usize_add(v_i_2825_, v___x_2832_);
v___x_2834_ = lean_array_uset(v_bs_x27_2831_, v_i_2825_, v_fst_2829_);
v_i_2825_ = v___x_2833_;
v_bs_2826_ = v___x_2834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__2___boxed(lean_object* v_sz_2836_, lean_object* v_i_2837_, lean_object* v_bs_2838_){
_start:
{
size_t v_sz_boxed_2839_; size_t v_i_boxed_2840_; lean_object* v_res_2841_; 
v_sz_boxed_2839_ = lean_unbox_usize(v_sz_2836_);
lean_dec(v_sz_2836_);
v_i_boxed_2840_ = lean_unbox_usize(v_i_2837_);
lean_dec(v_i_2837_);
v_res_2841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__2(v_sz_boxed_2839_, v_i_boxed_2840_, v_bs_2838_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__1(size_t v_sz_2842_, size_t v_i_2843_, lean_object* v_bs_2844_){
_start:
{
uint8_t v___x_2845_; 
v___x_2845_ = lean_usize_dec_lt(v_i_2843_, v_sz_2842_);
if (v___x_2845_ == 0)
{
return v_bs_2844_;
}
else
{
lean_object* v_v_2846_; lean_object* v_snd_2847_; lean_object* v___x_2848_; lean_object* v_bs_x27_2849_; size_t v___x_2850_; size_t v___x_2851_; lean_object* v___x_2852_; 
v_v_2846_ = lean_array_uget_borrowed(v_bs_2844_, v_i_2843_);
v_snd_2847_ = lean_ctor_get(v_v_2846_, 1);
lean_inc(v_snd_2847_);
v___x_2848_ = lean_unsigned_to_nat(0u);
v_bs_x27_2849_ = lean_array_uset(v_bs_2844_, v_i_2843_, v___x_2848_);
v___x_2850_ = ((size_t)1ULL);
v___x_2851_ = lean_usize_add(v_i_2843_, v___x_2850_);
v___x_2852_ = lean_array_uset(v_bs_x27_2849_, v_i_2843_, v_snd_2847_);
v_i_2843_ = v___x_2851_;
v_bs_2844_ = v___x_2852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__1___boxed(lean_object* v_sz_2854_, lean_object* v_i_2855_, lean_object* v_bs_2856_){
_start:
{
size_t v_sz_boxed_2857_; size_t v_i_boxed_2858_; lean_object* v_res_2859_; 
v_sz_boxed_2857_ = lean_unbox_usize(v_sz_2854_);
lean_dec(v_sz_2854_);
v_i_boxed_2858_ = lean_unbox_usize(v_i_2855_);
lean_dec(v_i_2855_);
v_res_2859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__1(v_sz_boxed_2857_, v_i_boxed_2858_, v_bs_2856_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0(size_t v_sz_2863_, size_t v_i_2864_, lean_object* v_bs_2865_){
_start:
{
uint8_t v___x_2866_; 
v___x_2866_ = lean_usize_dec_lt(v_i_2864_, v_sz_2863_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_bs_2865_);
return v___x_2867_;
}
else
{
lean_object* v_v_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v_v_2868_ = lean_array_uget(v_bs_2865_, v_i_2864_);
v___x_2869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0___closed__1));
lean_inc(v_v_2868_);
v___x_2870_ = l_Lean_Syntax_isOfKind(v_v_2868_, v___x_2869_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; 
lean_dec(v_v_2868_);
lean_dec_ref(v_bs_2865_);
v___x_2871_ = lean_box(0);
return v___x_2871_;
}
else
{
lean_object* v___x_2872_; lean_object* v_convs_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2872_ = lean_unsigned_to_nat(1u);
v_convs_2873_ = l_Lean_Syntax_getArg(v_v_2868_, v___x_2872_);
v___x_2874_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v_convs_2873_);
v___x_2875_ = l_Lean_Syntax_isOfKind(v_convs_2873_, v___x_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; 
lean_dec(v_convs_2873_);
lean_dec(v_v_2868_);
lean_dec_ref(v_bs_2865_);
v___x_2876_ = lean_box(0);
return v___x_2876_;
}
else
{
lean_object* v___x_2877_; lean_object* v_bs_x27_2878_; lean_object* v_barTks_2879_; lean_object* v___x_2880_; size_t v___x_2881_; size_t v___x_2882_; lean_object* v___x_2883_; 
v___x_2877_ = lean_unsigned_to_nat(0u);
v_bs_x27_2878_ = lean_array_uset(v_bs_2865_, v_i_2864_, v___x_2877_);
v_barTks_2879_ = l_Lean_Syntax_getArg(v_v_2868_, v___x_2877_);
lean_dec(v_v_2868_);
v___x_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2880_, 0, v_barTks_2879_);
lean_ctor_set(v___x_2880_, 1, v_convs_2873_);
v___x_2881_ = ((size_t)1ULL);
v___x_2882_ = lean_usize_add(v_i_2864_, v___x_2881_);
v___x_2883_ = lean_array_uset(v_bs_x27_2878_, v_i_2864_, v___x_2880_);
v_i_2864_ = v___x_2882_;
v_bs_2865_ = v___x_2883_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0___boxed(lean_object* v_sz_2885_, lean_object* v_i_2886_, lean_object* v_bs_2887_){
_start:
{
size_t v_sz_boxed_2888_; size_t v_i_boxed_2889_; lean_object* v_res_2890_; 
v_sz_boxed_2888_ = lean_unbox_usize(v_sz_2885_);
lean_dec(v_sz_2885_);
v_i_boxed_2889_ = lean_unbox_usize(v_i_2886_);
lean_dec(v_i_2886_);
v_res_2890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0(v_sz_boxed_2888_, v_i_boxed_2889_, v_bs_2887_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFirst(lean_object* v_x_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = ((lean_object*)(l_Lean_Fmt_fmtConvFirst___closed__1));
lean_inc(v_x_2898_);
v___x_2902_ = l_Lean_Syntax_isOfKind(v_x_2898_, v___x_2901_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_dec(v_x_2898_);
v___x_2903_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
lean_ctor_set(v___x_2904_, 1, v_a_2900_);
return v___x_2904_;
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; size_t v_sz_2908_; size_t v___x_2909_; lean_object* v___x_2910_; 
v___x_2905_ = lean_unsigned_to_nat(1u);
v___x_2906_ = l_Lean_Syntax_getArg(v_x_2898_, v___x_2905_);
v___x_2907_ = l_Lean_Syntax_getArgs(v___x_2906_);
lean_dec(v___x_2906_);
v_sz_2908_ = lean_array_size(v___x_2907_);
v___x_2909_ = ((size_t)0ULL);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__0(v_sz_2908_, v___x_2909_, v___x_2907_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
lean_dec(v_x_2898_);
v___x_2911_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v_a_2900_);
return v___x_2912_;
}
else
{
lean_object* v_val_2913_; lean_object* v___x_2914_; lean_object* v_firstTk_2915_; size_t v_sz_2916_; lean_object* v_convs_2917_; lean_object* v_barTks_2918_; lean_object* v___x_2919_; 
v_val_2913_ = lean_ctor_get(v___x_2910_, 0);
lean_inc_n(v_val_2913_, 2);
lean_dec_ref_known(v___x_2910_, 1);
v___x_2914_ = lean_unsigned_to_nat(0u);
v_firstTk_2915_ = l_Lean_Syntax_getArg(v_x_2898_, v___x_2914_);
lean_dec(v_x_2898_);
v_sz_2916_ = lean_array_size(v_val_2913_);
v_convs_2917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__1(v_sz_2916_, v___x_2909_, v_val_2913_);
v_barTks_2918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConvFirst_spec__2(v_sz_2916_, v___x_2909_, v_val_2913_);
v___x_2919_ = l_Lean_Fmt_fmtAltsTactic___redArg(v_firstTk_2915_, v_barTks_2918_, v_convs_2917_, v_a_2899_, v_a_2900_);
lean_dec_ref(v_convs_2917_);
lean_dec_ref(v_barTks_2918_);
return v___x_2919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvFirst___boxed(lean_object* v_x_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Fmt_fmtConvFirst(v_x_2920_, v_a_2921_, v_a_2922_);
lean_dec_ref(v_a_2921_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1(){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2930_ = l_Lean_Fmt_fmtAttribute;
v___x_2931_ = ((lean_object*)(l_Lean_Fmt_fmtConvFirst___closed__1));
v___x_2932_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___closed__1));
v___x_2933_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvFirst___boxed), 3, 0);
v___x_2934_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2930_, v___x_2931_, v___x_2932_, v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1___boxed(lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1();
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTactic(lean_object* v_x_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v___x_2950_; uint8_t v___x_2951_; lean_object* v___y_2953_; lean_object* v___y_2954_; uint8_t v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; 
v___x_2950_ = ((lean_object*)(l_Lean_Fmt_fmtConvTactic___closed__1));
lean_inc(v_x_2947_);
v___x_2951_ = l_Lean_Syntax_isOfKind(v_x_2947_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_dec(v_x_2947_);
v___x_3066_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v_a_2949_);
return v___x_3067_;
}
else
{
lean_object* v___x_3068_; lean_object* v_convTk_3069_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v_inTk_x3f_3073_; lean_object* v_occs_x3f_3074_; lean_object* v_t_x3f_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v_occs_x3f_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___x_3114_; lean_object* v_atTk_x3f_3116_; lean_object* v_id_x3f_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3068_ = lean_unsigned_to_nat(0u);
v_convTk_3069_ = l_Lean_Syntax_getArg(v_x_2947_, v___x_3068_);
v___x_3114_ = lean_unsigned_to_nat(1u);
v___x_3141_ = l_Lean_Syntax_getArg(v_x_2947_, v___x_3114_);
v___x_3142_ = l_Lean_Syntax_isNone(v___x_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; uint8_t v___x_3144_; 
v___x_3143_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3141_);
v___x_3144_ = l_Lean_Syntax_matchesNull(v___x_3141_, v___x_3143_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_dec(v___x_3141_);
lean_dec(v_convTk_3069_);
lean_dec(v_x_2947_);
v___x_3145_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
lean_ctor_set(v___x_3146_, 1, v_a_2949_);
return v___x_3146_;
}
else
{
lean_object* v_id_x3f_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_id_x3f_3147_ = l_Lean_Syntax_getArg(v___x_3141_, v___x_3114_);
v___x_3148_ = ((lean_object*)(l_Lean_Fmt_fmtConvTactic___closed__3));
lean_inc(v_id_x3f_3147_);
v___x_3149_ = l_Lean_Syntax_isOfKind(v_id_x3f_3147_, v___x_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_dec(v_id_x3f_3147_);
lean_dec(v___x_3141_);
lean_dec(v_convTk_3069_);
lean_dec(v_x_2947_);
v___x_3150_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v_a_2949_);
return v___x_3151_;
}
else
{
lean_object* v_atTk_x3f_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v_atTk_x3f_3152_ = l_Lean_Syntax_getArg(v___x_3141_, v___x_3068_);
lean_dec(v___x_3141_);
v___x_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3153_, 0, v_atTk_x3f_3152_);
v___x_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3154_, 0, v_id_x3f_3147_);
v_atTk_x3f_3116_ = v___x_3153_;
v_id_x3f_3117_ = v___x_3154_;
v___y_3118_ = v_a_2948_;
v___y_3119_ = v_a_2949_;
goto v___jp_3115_;
}
}
}
else
{
lean_object* v___x_3155_; 
lean_dec(v___x_3141_);
v___x_3155_ = lean_box(0);
v_atTk_x3f_3116_ = v___x_3155_;
v_id_x3f_3117_ = v___x_3155_;
v___y_3118_ = v_a_2948_;
v___y_3119_ = v_a_2949_;
goto v___jp_3115_;
}
v___jp_3070_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3078_ = lean_unsigned_to_nat(4u);
v___x_3079_ = l_Lean_Syntax_getArg(v_x_2947_, v___x_3078_);
v___x_3080_ = ((lean_object*)(l_Lean_Fmt_fmtConvSeq___closed__1));
lean_inc(v___x_3079_);
v___x_3081_ = l_Lean_Syntax_isOfKind(v___x_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_dec(v___x_3079_);
lean_dec(v_t_x3f_3075_);
lean_dec(v_occs_x3f_3074_);
lean_dec(v_inTk_x3f_3073_);
lean_dec(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v_convTk_3069_);
lean_dec(v_x_2947_);
v___x_3082_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set(v___x_3083_, 1, v___y_3077_);
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_Fmt_fmt(v_convTk_3069_, v___y_3076_, v___y_3077_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v_a_3086_; lean_object* v___x_3087_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3085_);
v_a_3086_ = lean_ctor_get(v___x_3084_, 1);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3084_, 2);
v___x_3087_ = l_Lean_Fmt_fmt_x3f(v___y_3071_, v___y_3076_, v_a_3086_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; lean_object* v_a_3089_; lean_object* v___x_3090_; lean_object* v_arrowTk_3091_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
v_a_3089_ = lean_ctor_get(v___x_3087_, 1);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3087_, 2);
v___x_3090_ = lean_unsigned_to_nat(3u);
v_arrowTk_3091_ = l_Lean_Syntax_getArg(v_x_2947_, v___x_3090_);
lean_dec(v_x_2947_);
if (lean_obj_tag(v___y_3072_) == 0)
{
lean_object* v___x_3092_; 
v___x_3092_ = lean_box(0);
v___y_3036_ = v_arrowTk_3091_;
v___y_3037_ = v_inTk_x3f_3073_;
v___y_3038_ = v_occs_x3f_3074_;
v___y_3039_ = v_a_3089_;
v___y_3040_ = v___y_3076_;
v___y_3041_ = v_a_3085_;
v___y_3042_ = v_a_3088_;
v___y_3043_ = v_t_x3f_3075_;
v___y_3044_ = v___x_3090_;
v___y_3045_ = v___x_3079_;
v___y_3046_ = v___x_3092_;
goto v___jp_3035_;
}
else
{
lean_object* v_val_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
v_val_3093_ = lean_ctor_get(v___y_3072_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___y_3072_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___y_3072_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_val_3093_);
lean_dec(v___y_3072_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_val_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
v___y_3036_ = v_arrowTk_3091_;
v___y_3037_ = v_inTk_x3f_3073_;
v___y_3038_ = v_occs_x3f_3074_;
v___y_3039_ = v_a_3089_;
v___y_3040_ = v___y_3076_;
v___y_3041_ = v_a_3085_;
v___y_3042_ = v_a_3088_;
v___y_3043_ = v_t_x3f_3075_;
v___y_3044_ = v___x_3090_;
v___y_3045_ = v___x_3079_;
v___y_3046_ = v___x_3098_;
goto v___jp_3035_;
}
}
}
}
else
{
lean_dec(v_a_3085_);
lean_dec(v___x_3079_);
lean_dec(v_t_x3f_3075_);
lean_dec(v_occs_x3f_3074_);
lean_dec(v_inTk_x3f_3073_);
lean_dec(v___y_3072_);
lean_dec(v_x_2947_);
return v___x_3087_;
}
}
else
{
lean_dec(v___x_3079_);
lean_dec(v_t_x3f_3075_);
lean_dec(v_occs_x3f_3074_);
lean_dec(v_inTk_x3f_3073_);
lean_dec(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v_x_2947_);
return v___x_3084_;
}
}
}
v___jp_3101_:
{
lean_object* v_t_x3f_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v_t_x3f_3110_ = l_Lean_Syntax_getArg(v___y_3106_, v___y_3104_);
lean_dec(v___y_3106_);
v___x_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___y_3102_);
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v_occs_x3f_3107_);
v___x_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3113_, 0, v_t_x3f_3110_);
v___y_3071_ = v___y_3103_;
v___y_3072_ = v___y_3105_;
v_inTk_x3f_3073_ = v___x_3111_;
v_occs_x3f_3074_ = v___x_3112_;
v_t_x3f_3075_ = v___x_3113_;
v___y_3076_ = v___y_3108_;
v___y_3077_ = v___y_3109_;
goto v___jp_3070_;
}
v___jp_3115_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3120_ = lean_unsigned_to_nat(2u);
v___x_3121_ = l_Lean_Syntax_getArg(v_x_2947_, v___x_3120_);
v___x_3122_ = l_Lean_Syntax_isNone(v___x_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3123_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_3121_);
v___x_3124_ = l_Lean_Syntax_matchesNull(v___x_3121_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec(v___x_3121_);
lean_dec(v_id_x3f_3117_);
lean_dec(v_atTk_x3f_3116_);
lean_dec(v_convTk_3069_);
lean_dec(v_x_2947_);
v___x_3125_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v___y_3119_);
return v___x_3126_;
}
else
{
lean_object* v_inTk_x3f_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v_inTk_x3f_3127_ = l_Lean_Syntax_getArg(v___x_3121_, v___x_3068_);
v___x_3128_ = l_Lean_Syntax_getArg(v___x_3121_, v___x_3114_);
v___x_3129_ = l_Lean_Syntax_isNone(v___x_3128_);
if (v___x_3129_ == 0)
{
uint8_t v___x_3130_; 
lean_inc(v___x_3128_);
v___x_3130_ = l_Lean_Syntax_matchesNull(v___x_3128_, v___x_3114_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_dec(v___x_3128_);
lean_dec(v_inTk_x3f_3127_);
lean_dec(v___x_3121_);
lean_dec(v_id_x3f_3117_);
lean_dec(v_atTk_x3f_3116_);
lean_dec(v_convTk_3069_);
lean_dec(v_x_2947_);
v___x_3131_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set(v___x_3132_, 1, v___y_3119_);
return v___x_3132_;
}
else
{
lean_object* v_occs_x3f_3133_; lean_object* v___x_3134_; uint8_t v___x_3135_; 
v_occs_x3f_3133_ = l_Lean_Syntax_getArg(v___x_3128_, v___x_3068_);
lean_dec(v___x_3128_);
v___x_3134_ = ((lean_object*)(l_Lean_Fmt_fmtConvOccs___closed__1));
lean_inc(v_occs_x3f_3133_);
v___x_3135_ = l_Lean_Syntax_isOfKind(v_occs_x3f_3133_, v___x_3134_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_dec(v_occs_x3f_3133_);
lean_dec(v_inTk_x3f_3127_);
lean_dec(v___x_3121_);
lean_dec(v_id_x3f_3117_);
lean_dec(v_atTk_x3f_3116_);
lean_dec(v_convTk_3069_);
lean_dec(v_x_2947_);
v___x_3136_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
lean_ctor_set(v___x_3137_, 1, v___y_3119_);
return v___x_3137_;
}
else
{
lean_object* v___x_3138_; 
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_occs_x3f_3133_);
v___y_3102_ = v_inTk_x3f_3127_;
v___y_3103_ = v_atTk_x3f_3116_;
v___y_3104_ = v___x_3120_;
v___y_3105_ = v_id_x3f_3117_;
v___y_3106_ = v___x_3121_;
v_occs_x3f_3107_ = v___x_3138_;
v___y_3108_ = v___y_3118_;
v___y_3109_ = v___y_3119_;
goto v___jp_3101_;
}
}
}
else
{
lean_object* v___x_3139_; 
lean_dec(v___x_3128_);
v___x_3139_ = lean_box(0);
v___y_3102_ = v_inTk_x3f_3127_;
v___y_3103_ = v_atTk_x3f_3116_;
v___y_3104_ = v___x_3120_;
v___y_3105_ = v_id_x3f_3117_;
v___y_3106_ = v___x_3121_;
v_occs_x3f_3107_ = v___x_3139_;
v___y_3108_ = v___y_3118_;
v___y_3109_ = v___y_3119_;
goto v___jp_3101_;
}
}
}
else
{
lean_object* v___x_3140_; 
lean_dec(v___x_3121_);
v___x_3140_ = lean_box(0);
v___y_3071_ = v_atTk_x3f_3116_;
v___y_3072_ = v_id_x3f_3117_;
v_inTk_x3f_3073_ = v___x_3140_;
v_occs_x3f_3074_ = v___x_3140_;
v_t_x3f_3075_ = v___x_3140_;
v___y_3076_ = v___y_3118_;
v___y_3077_ = v___y_3119_;
goto v___jp_3070_;
}
}
}
v___jp_2952_:
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Lean_Fmt_fmt_x3f(v___y_2963_, v___y_2954_, v___y_2960_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v_a_2966_; lean_object* v___x_2967_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
v_a_2966_ = lean_ctor_get(v___x_2964_, 1);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2964_, 2);
v___x_2967_ = l_Lean_Fmt_fmt(v___y_2953_, v___y_2954_, v_a_2966_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v_a_2969_; lean_object* v___x_2970_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
v_a_2969_ = lean_ctor_get(v___x_2967_, 1);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2967_, 2);
v___x_2970_ = l_Lean_Fmt_fmt(v___y_2962_, v___y_2954_, v_a_2969_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2991_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
v_a_2972_ = lean_ctor_get(v___x_2970_, 1);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2974_ = v___x_2970_;
v_isShared_2975_ = v_isSharedCheck_2991_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_inc(v_a_2971_);
lean_dec(v___x_2970_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2991_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
uint8_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2976_ = 0;
v___x_2977_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v___y_2958_, v___y_2959_, v___x_2976_);
v___x_2978_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v___y_2957_, v_a_2965_, v___x_2976_);
v___x_2979_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2979_, 0, v___y_2956_);
lean_ctor_set_uint8(v___x_2979_, sizeof(void*)*1, v___x_2951_);
v___x_2980_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2980_, 0, v___x_2977_);
lean_ctor_set_uint8(v___x_2980_, sizeof(void*)*1, v___x_2951_);
v___x_2981_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2981_, 0, v___x_2978_);
lean_ctor_set_uint8(v___x_2981_, sizeof(void*)*1, v___x_2951_);
v___x_2982_ = lean_mk_empty_array_with_capacity(v___y_2961_);
v___x_2983_ = lean_array_push(v___x_2982_, v___x_2979_);
v___x_2984_ = lean_array_push(v___x_2983_, v___x_2980_);
v___x_2985_ = lean_array_push(v___x_2984_, v___x_2981_);
v___x_2986_ = l_Lean_Fmt_Layouts_blocks(v___x_2985_, v___x_2951_);
lean_dec_ref(v___x_2985_);
v___x_2987_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_2986_, v_a_2968_, v_a_2971_, v___y_2955_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2987_);
v___x_2989_ = v___x_2974_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_a_2972_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
else
{
lean_dec(v_a_2968_);
lean_dec(v_a_2965_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
return v___x_2970_;
}
}
else
{
lean_dec(v_a_2965_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
return v___x_2967_;
}
}
else
{
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2953_);
return v___x_2964_;
}
}
v___jp_2992_:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_Fmt_fmt_x3f(v___y_3003_, v___y_2995_, v___y_3000_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
v_a_3006_ = lean_ctor_get(v___x_3004_, 1);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3004_, 2);
v___x_3007_ = lean_unsigned_to_nat(2u);
v___x_3008_ = lean_mk_empty_array_with_capacity(v___x_3007_);
v___x_3009_ = lean_array_push(v___x_3008_, v___y_2994_);
v___x_3010_ = lean_array_push(v___x_3009_, v_a_3005_);
v___x_3011_ = 0;
v___x_3012_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3012_, 0, v___x_2951_);
lean_ctor_set_uint8(v___x_3012_, 1, v___x_3011_);
lean_ctor_set_uint8(v___x_3012_, 2, v___x_3011_);
lean_ctor_set_uint8(v___x_3012_, 3, v___x_3011_);
v___x_3013_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3010_, v___x_3012_);
if (lean_obj_tag(v___y_2999_) == 0)
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_box(0);
v___y_2953_ = v___y_2993_;
v___y_2954_ = v___y_2995_;
v___y_2955_ = v___x_3011_;
v___y_2956_ = v___y_2996_;
v___y_2957_ = v___x_3013_;
v___y_2958_ = v___y_2997_;
v___y_2959_ = v___y_2998_;
v___y_2960_ = v_a_3006_;
v___y_2961_ = v___y_3002_;
v___y_2962_ = v___y_3001_;
v___y_2963_ = v___x_3014_;
goto v___jp_2952_;
}
else
{
lean_object* v_val_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
v_val_3015_ = lean_ctor_get(v___y_2999_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___y_2999_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___y_2999_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_val_3015_);
lean_dec(v___y_2999_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_val_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
v___y_2953_ = v___y_2993_;
v___y_2954_ = v___y_2995_;
v___y_2955_ = v___x_3011_;
v___y_2956_ = v___y_2996_;
v___y_2957_ = v___x_3013_;
v___y_2958_ = v___y_2997_;
v___y_2959_ = v___y_2998_;
v___y_2960_ = v_a_3006_;
v___y_2961_ = v___y_3002_;
v___y_2962_ = v___y_3001_;
v___y_2963_ = v___x_3020_;
goto v___jp_2952_;
}
}
}
}
else
{
lean_dec(v___y_3001_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
return v___x_3004_;
}
}
v___jp_3023_:
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_box(0);
v___y_2993_ = v___y_3024_;
v___y_2994_ = v___y_3025_;
v___y_2995_ = v___y_3026_;
v___y_2996_ = v___y_3027_;
v___y_2997_ = v___y_3028_;
v___y_2998_ = v___y_3029_;
v___y_2999_ = v___y_3031_;
v___y_3000_ = v___y_3030_;
v___y_3001_ = v___y_3033_;
v___y_3002_ = v___y_3032_;
v___y_3003_ = v___x_3034_;
goto v___jp_2992_;
}
v___jp_3035_:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_Fmt_fmt_x3f(v___y_3046_, v___y_3040_, v___y_3039_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v_a_3049_; lean_object* v___x_3050_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
v_a_3049_ = lean_ctor_get(v___x_3047_, 1);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3047_, 2);
v___x_3050_ = l_Lean_Fmt_fmt_x3f(v___y_3037_, v___y_3040_, v_a_3049_);
if (lean_obj_tag(v___x_3050_) == 0)
{
if (lean_obj_tag(v___y_3038_) == 0)
{
lean_object* v_a_3051_; lean_object* v_a_3052_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
v_a_3052_ = lean_ctor_get(v___x_3050_, 1);
lean_inc(v_a_3052_);
lean_dec_ref_known(v___x_3050_, 2);
v___y_3024_ = v___y_3036_;
v___y_3025_ = v_a_3051_;
v___y_3026_ = v___y_3040_;
v___y_3027_ = v___y_3041_;
v___y_3028_ = v___y_3042_;
v___y_3029_ = v_a_3048_;
v___y_3030_ = v_a_3052_;
v___y_3031_ = v___y_3043_;
v___y_3032_ = v___y_3044_;
v___y_3033_ = v___y_3045_;
goto v___jp_3023_;
}
else
{
lean_object* v_val_3053_; 
v_val_3053_ = lean_ctor_get(v___y_3038_, 0);
lean_inc(v_val_3053_);
lean_dec_ref_known(v___y_3038_, 1);
if (lean_obj_tag(v_val_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v_a_3055_; 
v_a_3054_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3054_);
v_a_3055_ = lean_ctor_get(v___x_3050_, 1);
lean_inc(v_a_3055_);
lean_dec_ref_known(v___x_3050_, 2);
v___y_3024_ = v___y_3036_;
v___y_3025_ = v_a_3054_;
v___y_3026_ = v___y_3040_;
v___y_3027_ = v___y_3041_;
v___y_3028_ = v___y_3042_;
v___y_3029_ = v_a_3048_;
v___y_3030_ = v_a_3055_;
v___y_3031_ = v___y_3043_;
v___y_3032_ = v___y_3044_;
v___y_3033_ = v___y_3045_;
goto v___jp_3023_;
}
else
{
lean_object* v_a_3056_; lean_object* v_a_3057_; lean_object* v_val_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
v_a_3056_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3056_);
v_a_3057_ = lean_ctor_get(v___x_3050_, 1);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3050_, 2);
v_val_3058_ = lean_ctor_get(v_val_3053_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_val_3053_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v_val_3053_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_val_3058_);
lean_dec(v_val_3053_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_val_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
v___y_2993_ = v___y_3036_;
v___y_2994_ = v_a_3056_;
v___y_2995_ = v___y_3040_;
v___y_2996_ = v___y_3041_;
v___y_2997_ = v___y_3042_;
v___y_2998_ = v_a_3048_;
v___y_2999_ = v___y_3043_;
v___y_3000_ = v_a_3057_;
v___y_3001_ = v___y_3045_;
v___y_3002_ = v___y_3044_;
v___y_3003_ = v___x_3063_;
goto v___jp_2992_;
}
}
}
}
}
else
{
lean_dec(v_a_3048_);
lean_dec(v___y_3045_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3038_);
lean_dec(v___y_3036_);
return v___x_3050_;
}
}
else
{
lean_dec(v___y_3045_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec(v___y_3036_);
return v___x_3047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConvTactic___boxed(lean_object* v_x_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_Fmt_fmtConvTactic(v_x_3156_, v_a_3157_, v_a_3158_);
lean_dec_ref(v_a_3157_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1(){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3166_ = l_Lean_Fmt_fmtAttribute;
v___x_3167_ = ((lean_object*)(l_Lean_Fmt_fmtConvTactic___closed__1));
v___x_3168_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___closed__1));
v___x_3169_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtConvTactic___boxed), 3, 0);
v___x_3170_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3166_, v___x_3167_, v___x_3168_, v___x_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1___boxed(lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1();
return v_res_3172_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Conv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq1Indented___regBuiltin_Lean_Fmt_fmtConvSeq1Indented__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqBracketed___regBuiltin_Lean_Fmt_fmtConvSeqBracketed__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeq___regBuiltin_Lean_Fmt_fmtConvSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccsIndexed___regBuiltin_Lean_Fmt_fmtConvOccsIndexed__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvOccs___regBuiltin_Lean_Fmt_fmtConvOccs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgArg___regBuiltin_Lean_Fmt_fmtConvArgArg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvWithAnnotateState___regBuiltin_Lean_Fmt_fmtConvWithAnnotateState__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvArgTactic___regBuiltin_Lean_Fmt_fmtConvArgTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExt___regBuiltin_Lean_Fmt_fmtConvExt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvChange___regBuiltin_Lean_Fmt_fmtConvChange__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDelta___regBuiltin_Lean_Fmt_fmtConvDelta__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvUnfold___regBuiltin_Lean_Fmt_fmtConvUnfold__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvClear___regBuiltin_Lean_Fmt_fmtConvClear__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvIntro___regBuiltin_Lean_Fmt_fmtConvIntro__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvApply___regBuiltin_Lean_Fmt_fmtConvApply__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTacticCore___regBuiltin_Lean_Fmt_fmtConvNestedTacticCore__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedTactic___regBuiltin_Lean_Fmt_fmtConvNestedTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTacticInTactic___regBuiltin_Lean_Fmt_fmtConvTacticInTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvConvSeq___regBuiltin_Lean_Fmt_fmtConvConvSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNestedConv___regBuiltin_Lean_Fmt_fmtConvNestedConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvParen___regBuiltin_Lean_Fmt_fmtConvParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAllGoals___regBuiltin_Lean_Fmt_fmtConvAllGoals__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvAnyGoals___regBuiltin_Lean_Fmt_fmtConvAnyGoals__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFocus___regBuiltin_Lean_Fmt_fmtConvFocus__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFailIfSuccess___regBuiltin_Lean_Fmt_fmtConvFailIfSuccess__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTry___regBuiltin_Lean_Fmt_fmtConvTry__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRepeat___regBuiltin_Lean_Fmt_fmtConvRepeat__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase___regBuiltin_Lean_Fmt_fmtConvCase__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvCase_x27___regBuiltin_Lean_Fmt_fmtConvCase_x27__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvNext___regBuiltin_Lean_Fmt_fmtConvNext__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDot___regBuiltin_Lean_Fmt_fmtConvDot__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtConvSeqFocus = _init_l_Lean_Fmt_fmtConvSeqFocus();
lean_mark_persistent(l_Lean_Fmt_fmtConvSeqFocus);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSeqFocus___regBuiltin_Lean_Fmt_fmtConvSeqFocus__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRw___regBuiltin_Lean_Fmt_fmtConvRw__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvErw___regBuiltin_Lean_Fmt_fmtConvErw__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvRewrite___regBuiltin_Lean_Fmt_fmtConvRewrite__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimp___regBuiltin_Lean_Fmt_fmtConvSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimp___regBuiltin_Lean_Fmt_fmtConvDSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvSimpTrace___regBuiltin_Lean_Fmt_fmtConvSimpTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvDSimpTrace___regBuiltin_Lean_Fmt_fmtConvDSimpTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvPattern___regBuiltin_Lean_Fmt_fmtConvPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvExtractLets___regBuiltin_Lean_Fmt_fmtConvExtractLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvLiftLets___regBuiltin_Lean_Fmt_fmtConvLiftLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterPattern___regBuiltin_Lean_Fmt_fmtConvEnterPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnterArg___regBuiltin_Lean_Fmt_fmtConvEnterArg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvEnter___regBuiltin_Lean_Fmt_fmtConvEnter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvFirst___regBuiltin_Lean_Fmt_fmtConvFirst__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Conv_0__Lean_Fmt_fmtConvTactic___regBuiltin_Lean_Fmt_fmtConvTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Conv(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Conv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Conv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Init_Tactics(uint8_t builtin);
lean_object* initialize_Init_Conv(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Conv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Conv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Conv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Conv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Conv(builtin);
}
#ifdef __cplusplus
}
#endif
