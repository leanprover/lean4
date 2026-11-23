// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Notation
// Imports: public import Lean.Fmt.FmtM.Basic import Lean.Fmt.Formatters.Lean.Parser.Term meta import Init.Notation import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
extern lean_object* l_Lean_Fmt_conditionalFmtAttribute;
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
lean_object* l_Lean_Fmt_fmtWith_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDocCommentWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pipeOperator(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtPrefixOperator___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtPrefixOperator(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtPostfixOperator___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAppLike(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_collection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_deconstructPipeProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtPipeProjLike(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_infixFmtAttribute;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_space;
lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_subtype(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtPostfixOperator(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtPrecParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prec(_)"};
static const lean_object* l_Lean_Fmt_fmtPrecParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPrecParen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtPrecParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrecParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 33, 53, 78, 65, 16, 125, 133)}};
static const lean_object* l_Lean_Fmt_fmtPrecParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtPrecParen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrecParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrecParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtPrecParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 23, 96, 194, 116, 151, 106, 26)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtAddPrec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(65) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtAddPrec___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtAddPrec___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtAddPrec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAddPrec___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtAddPrec___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtAddPrec___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtAddPrec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtAddPrec___closed__2;
static lean_once_cell_t l_Lean_Fmt_fmtAddPrec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtAddPrec___closed__3;
static lean_once_cell_t l_Lean_Fmt_fmtAddPrec___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtAddPrec___closed__4;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAddPrec;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "addPrec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 68, 23, 63, 244, 39, 18, 227)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtAddPrec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(213, 147, 153, 50, 242, 18, 16, 53)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__5 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubPrec;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "subPrec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 162, 64, 41, 156, 201, 248, 85)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtSubPrec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 164, 15, 20, 212, 241, 147, 68)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAddPrio;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "addPrio"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 218, 70, 150, 87, 9, 79, 160)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtAddPrio"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 162, 213, 191, 36, 127, 132, 30)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubPrio;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "subPrio"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 112, 238, 38, 106, 122, 129, 24)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 12, 102, 115, 130, 88, 1, 102)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtSubPrio"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(230, 179, 127, 27, 135, 26, 10, 240)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtPrioParen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "prio(_)"};
static const lean_object* l_Lean_Fmt_fmtPrioParen___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPrioParen___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtPrioParen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrioParen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 123, 236, 48, 43, 160, 232, 105)}};
static const lean_object* l_Lean_Fmt_fmtPrioParen___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtPrioParen___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrioParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrioParen___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtPrioParen"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 27, 184, 217, 140, 114, 15)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxPostfix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxPostfix___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtPostfixOperator___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stx_+"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(219, 88, 43, 6, 184, 140, 229, 35)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtStxPostfix"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 69, 57, 156, 243, 19, 247, 54)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stx_*"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 71, 213, 204, 158, 232, 142, 136)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "stx_,*"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 173, 54, 129, 112, 44, 137, 241)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5___boxed(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "stx_,+"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 123, 52, 191, 7, 250, 165, 126)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7___boxed(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stx_,*,\?"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 140, 12, 208, 120, 186, 89, 209)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9___boxed(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stx_,+,\?"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 21, 106, 219, 154, 51, 82, 79)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_empty_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_empty_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_empty_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_empty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInNonIdent_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInNonIdent_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInNonIdent_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInNonIdent_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInIdent_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInIdent_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInIdent_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInIdent_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedEndsInIdent_default;
LEAN_EXPORT uint8_t l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instInhabitedEndsInIdent;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent_prio(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent_prio___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2_spec__3(lean_object*, size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2___boxed(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__1_value;
static const lean_array_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxOptional(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxOptional___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stx_\?"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 110, 207, 78, 164, 149, 1, 207)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtStxOptional"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 233, 190, 231, 149, 123, 152, 185)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtStxNotFollowedBy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stx!_"};
static const lean_object* l_Lean_Fmt_fmtStxNotFollowedBy___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtStxNotFollowedBy___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtStxNotFollowedBy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtStxNotFollowedBy___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 84, 127, 174, 33, 34, 118, 100)}};
static const lean_object* l_Lean_Fmt_fmtStxNotFollowedBy___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtStxNotFollowedBy___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxNotFollowedBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxNotFollowedBy___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtStxNotFollowedBy"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 161, 217, 150, 160, 11, 33, 92)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtStxOrelse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtStxOrelse___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtStxOrelse___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtStxOrelse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtStxOrelse___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtStxOrelse___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtStxOrelse___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtStxOrelse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtStxOrelse___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxOrelse;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stx_<|>_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 97, 122, 56, 37, 186, 212, 102)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtStxOrelse"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(127, 198, 189, 168, 61, 31, 178, 21)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermNot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermNot___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtPrefixOperator___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 6, .m_data = "term¬_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 122, 71, 36, 131, 84, 176, 236)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtTermNot"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(192, 238, 38, 156, 84, 28, 178, 219)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term!_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 176, 120, 218, 62, 77, 52, 243)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTermNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term-_"};
static const lean_object* l_Lean_Fmt_fmtTermNeg___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermNeg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermNeg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermNeg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 127, 37, 42, 155, 196, 209, 131)}};
static const lean_object* l_Lean_Fmt_fmtTermNeg___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermNeg___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtTermNeg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Fmt_fmtTermNeg___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTermNeg___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermNeg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermNeg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Fmt_fmtTermNeg___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtTermNeg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermNeg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermNeg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtTermNeg"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 94, 222, 132, 49, 133, 117, 86)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTermInv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 7, .m_data = "term_⁻¹"};
static const lean_object* l_Lean_Fmt_fmtTermInv___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermInv___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermInv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermInv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 245, 188, 102, 250, 83, 210, 162)}};
static const lean_object* l_Lean_Fmt_fmtTermInv___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermInv___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermInv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermInv___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtTermInv"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 92, 232, 4, 101, 202, 176, 208)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtTermMem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtTermMem___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermMem___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermMem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermMem___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtTermMem___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermMem___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtTermMem___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTermMem___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermMem;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∈_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 149, 102, 29, 65, 152, 113, 144)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtTermMem"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(231, 229, 6, 164, 162, 142, 87, 81)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermNotMem;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∉_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 191, 47, 82, 105, 120, 162, 72)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtTermNotMem"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 94, 80, 244, 134, 5, 22, 42)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtTermLe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtTermLe___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermLe___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermLe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermLe___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtTermLe___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermLe___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtTermLe___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTermLe___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermLe;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≤_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 3, 61, 112, 38, 138, 106, 121)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtTermLe"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 156, 64, 208, 178, 22, 184, 112)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermGe;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≥_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 65, 30, 214, 7, 203, 184, 211)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtTermGe"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(175, 196, 2, 228, 63, 87, 236, 95)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtTermAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtTermAnd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermAnd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermAnd___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtTermAnd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermAnd___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtTermAnd___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTermAnd___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermAnd;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∧_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 224, 85, 99, 168, 124, 84, 223)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtTermAnd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(45, 2, 175, 216, 163, 119, 254, 112)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Fmt_fmtTermOr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_fmtTermOr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermOr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermOr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTermOr___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtTermOr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermOr___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_fmtTermOr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtTermOr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermOr;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∨_"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 23, 28, 64, 30, 253, 248, 167)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtTermOr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(58, 151, 151, 159, 205, 196, 223, 78)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_fmtPipeOperator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtPipeOperator___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPipeOperator___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPipeOperator(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPipeOperator___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTermPipeLeft___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_<|_"};
static const lean_object* l_Lean_Fmt_fmtTermPipeLeft___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermPipeLeft___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermPipeLeft___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermPipeLeft___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 38, 96, 140, 215, 46, 31, 82)}};
static const lean_object* l_Lean_Fmt_fmtTermPipeLeft___lam__0___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermPipeLeft___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeLeft___lam__0(lean_object*);
static const lean_closure_object l_Lean_Fmt_fmtTermPipeLeft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtTermPipeLeft___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtTermPipeLeft___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermPipeLeft___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeLeft___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtTermPipeLeft"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 30, 177, 165, 27, 148, 58, 55)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTermPipeRight___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_|>_"};
static const lean_object* l_Lean_Fmt_fmtTermPipeRight___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermPipeRight___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermPipeRight___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermPipeRight___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 176, 95, 176, 96, 75, 16, 99)}};
static const lean_object* l_Lean_Fmt_fmtTermPipeRight___lam__0___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermPipeRight___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeRight___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeRight___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_fmtTermPipeRight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtTermPipeRight___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtTermPipeRight___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermPipeRight___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeRight___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtTermPipeRight"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 41, 209, 221, 217, 187, 123, 40)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTermDollar___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_$__"};
static const lean_object* l_Lean_Fmt_fmtTermDollar___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermDollar___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTermDollar___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTermDollar___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 217, 134, 45, 19, 162, 148, 100)}};
static const lean_object* l_Lean_Fmt_fmtTermDollar___lam__0___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTermDollar___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermDollar___lam__0(lean_object*);
static const lean_closure_object l_Lean_Fmt_fmtTermDollar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtTermDollar___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtTermDollar___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTermDollar___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermDollar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermDollar___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtTermDollar"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 230, 103, 171, 211, 218, 153, 96)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRawNatLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rawNatLit"};
static const lean_object* l_Lean_Fmt_fmtRawNatLit___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRawNatLit___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRawNatLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRawNatLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 17, 27, 214, 55, 10, 193, 23)}};
static const lean_object* l_Lean_Fmt_fmtRawNatLit___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRawNatLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawNatLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawNatLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtRawNatLit"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 101, 209, 171, 251, 34, 113, 1)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBinderIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean_Fmt_fmtBinderIdent___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderIdent___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderIdent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Lean_Fmt_fmtBinderIdent___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtBinderIdent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtBinderIdent___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtBinderIdent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Fmt_fmtBinderIdent___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderIdent___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderIdent___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderIdent___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtBinderIdent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Fmt_fmtBinderIdent___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtBinderIdent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtBinderIdent___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtBinderIdent___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtBinderIdent___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtBinderIdent___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderIdent___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtBinderIdent"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 212, 231, 123, 43, 131, 218, 5)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCaseArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Fmt_fmtCaseArg___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCaseArg___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtCaseArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l_Lean_Fmt_fmtCaseArg___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCaseArg___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtCaseArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCaseArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCaseArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCaseArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCaseArg___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCaseArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Fmt_fmtCaseArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCaseArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtCaseArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l_Lean_Fmt_fmtCaseArg___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtCaseArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCaseArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCaseArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtCaseArg"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 144, 220, 198, 140, 59, 127, 69)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtIfThenElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l_Lean_Fmt_fmtIfThenElse___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtIfThenElse___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtIfThenElse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIfThenElse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l_Lean_Fmt_fmtIfThenElse___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtIfThenElse___closed__1_value;
static const lean_array_object l_Lean_Fmt_fmtIfThenElse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtIfThenElse___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtIfThenElse___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfThenElse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfThenElse___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtIfThenElse"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 210, 8, 44, 116, 212, 163, 12)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDepIfThenElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDepIfThenElse"};
static const lean_object* l_Lean_Fmt_fmtDepIfThenElse___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDepIfThenElse___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDepIfThenElse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDepIfThenElse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 94, 17, 11, 145, 108, 236, 173)}};
static const lean_object* l_Lean_Fmt_fmtDepIfThenElse___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDepIfThenElse___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDepIfThenElse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDepIfThenElse___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtDepIfThenElse"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 185, 112, 140, 193, 70, 216, 244)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfLet___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfLet___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtIfLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "termIfLet"};
static const lean_object* l_Lean_Fmt_fmtIfLet___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtIfLet___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtIfLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtIfLet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 66, 194, 161, 28, 240, 193, 192)}};
static const lean_object* l_Lean_Fmt_fmtIfLet___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtIfLet___closed__1_value;
static const lean_closure_object l_Lean_Fmt_fmtIfLet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtIfLet___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtIfLet___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtIfLet___closed__2_value;
static lean_once_cell_t l_Lean_Fmt_fmtIfLet___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtIfLet___closed__3;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfLet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfLet___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fmtIfLet"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 151, 98, 35, 31, 34, 94, 216)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBoolIfThenElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "boolIfThenElse"};
static const lean_object* l_Lean_Fmt_fmtBoolIfThenElse___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBoolIfThenElse___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBoolIfThenElse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtBoolIfThenElse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 230, 17, 23, 40, 101, 10, 159)}};
static const lean_object* l_Lean_Fmt_fmtBoolIfThenElse___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBoolIfThenElse___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBoolIfThenElse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBoolIfThenElse___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtBoolIfThenElse"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 125, 93, 190, 101, 36, 184, 183)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSubtype___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "term{_:_//_}"};
static const lean_object* l_Lean_Fmt_fmtSubtype___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSubtype___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSubtype___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtSubtype___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 133, 82, 74, 101, 189, 164, 87)}};
static const lean_object* l_Lean_Fmt_fmtSubtype___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSubtype___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubtype(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubtype___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtSubtype"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 19, 113, 148, 144, 30, 68, 62)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtWithoutExpectedType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "termWithout_expected_type_"};
static const lean_object* l_Lean_Fmt_fmtWithoutExpectedType___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtWithoutExpectedType___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtWithoutExpectedType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtWithoutExpectedType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 37, 243, 95, 254, 219, 220, 5)}};
static const lean_object* l_Lean_Fmt_fmtWithoutExpectedType___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtWithoutExpectedType___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithoutExpectedType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithoutExpectedType___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtWithoutExpectedType"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 58, 89, 55, 241, 146, 11, 167)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtModCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "modCast"};
static const lean_object* l_Lean_Fmt_fmtModCast___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtModCast___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtModCast___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtModCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtModCast___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtModCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 150, 13, 6, 253, 161, 172, 138)}};
static const lean_object* l_Lean_Fmt_fmtModCast___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtModCast___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtModCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtModCast___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtModCast"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 118, 183, 42, 248, 103, 187, 239)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtIncludeStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "includeStr"};
static const lean_object* l_Lean_Fmt_fmtIncludeStr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtIncludeStr___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtIncludeStr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtIncludeStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtIncludeStr___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtIncludeStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 248, 250, 99, 174, 199, 105, 129)}};
static const lean_object* l_Lean_Fmt_fmtIncludeStr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtIncludeStr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIncludeStr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIncludeStr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtIncludeStr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 13, 202, 166, 208, 107, 120, 55)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtWithAnnotateTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withAnnotateTerm"};
static const lean_object* l_Lean_Fmt_fmtWithAnnotateTerm___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtWithAnnotateTerm___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtWithAnnotateTerm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtWithAnnotateTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtWithAnnotateTerm___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtWithAnnotateTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 55, 241, 226, 210, 131, 126, 179)}};
static const lean_object* l_Lean_Fmt_fmtWithAnnotateTerm___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtWithAnnotateTerm___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithAnnotateTerm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithAnnotateTerm___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtWithAnnotateTerm"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 150, 79, 138, 130, 70, 238, 220)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtByElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "byElab"};
static const lean_object* l_Lean_Fmt_fmtByElab___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtByElab___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtByElab___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtByElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtByElab___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtByElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 97, 248, 220, 225, 122, 28, 239)}};
static const lean_object* l_Lean_Fmt_fmtByElab___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtByElab___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtByElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtByElab___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtByElab"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 111, 54, 23, 117, 75, 14, 156)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDeprecated___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l_Lean_Fmt_fmtDeprecated___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDeprecated___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeprecated___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeprecated___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeprecated___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtDeprecated___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 123, 37, 172, 84, 157, 83, 143)}};
static const lean_object* l_Lean_Fmt_fmtDeprecated___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDeprecated___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDeprecated___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Fmt_fmtDeprecated___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDeprecated___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeprecated___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDeprecated___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Fmt_fmtDeprecated___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDeprecated___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtDeprecated___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "deprecatedTypeChanged"};
static const lean_object* l_Lean_Fmt_fmtDeprecated___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDeprecated___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeprecated___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeprecated___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeprecated___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtDeprecated___closed__4_value),LEAN_SCALAR_PTR_LITERAL(82, 186, 25, 73, 96, 22, 207, 47)}};
static const lean_object* l_Lean_Fmt_fmtDeprecated___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtDeprecated___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeprecated(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeprecated___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtDeprecated"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 117, 29, 81, 215, 213, 246, 85)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDeprecatedArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecated_arg"};
static const lean_object* l_Lean_Fmt_fmtDeprecatedArg___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDeprecatedArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDeprecatedArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDeprecatedArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDeprecatedArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtDeprecatedArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 53, 92, 118, 242, 48, 253, 4)}};
static const lean_object* l_Lean_Fmt_fmtDeprecatedArg___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDeprecatedArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeprecatedArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeprecatedArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtDeprecatedArg"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 33, 28, 185, 73, 51, 41, 56)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSuggestFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "suggest_for"};
static const lean_object* l_Lean_Fmt_fmtSuggestFor___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSuggestFor___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSuggestFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSuggestFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSuggestFor___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSuggestFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 118, 89, 220, 12, 6, 188, 182)}};
static const lean_object* l_Lean_Fmt_fmtSuggestFor___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSuggestFor___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSuggestFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSuggestFor___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtSuggestFor"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 79, 51, 235, 106, 111, 73, 63)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtUnivOutParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "univ_out_params"};
static const lean_object* l_Lean_Fmt_fmtUnivOutParams___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtUnivOutParams___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtUnivOutParams___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtUnivOutParams___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnivOutParams___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtUnivOutParams___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 117, 107, 12, 66, 157, 101, 88)}};
static const lean_object* l_Lean_Fmt_fmtUnivOutParams___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtUnivOutParams___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnivOutParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnivOutParams___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtUnivOutParams"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 115, 40, 62, 133, 16, 201, 76)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCommandCodeAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "command_code_action"};
static const lean_object* l_Lean_Fmt_fmtCommandCodeAction___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCommandCodeAction___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCommandCodeAction___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCommandCodeAction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCommandCodeAction___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtCommandCodeAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 163, 59, 210, 246, 85, 101, 130)}};
static const lean_object* l_Lean_Fmt_fmtCommandCodeAction___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCommandCodeAction___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCommandCodeAction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCommandCodeAction___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtCommandCodeAction"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 161, 149, 71, 36, 97, 164, 133)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtBuiltinCommandCodeAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "builtin_command_code_action"};
static const lean_object* l_Lean_Fmt_fmtBuiltinCommandCodeAction___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinCommandCodeAction___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCommandCodeAction___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtBuiltinCommandCodeAction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtBuiltinCommandCodeAction___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtBuiltinCommandCodeAction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 158, 252, 78, 187, 139, 222, 168)}};
static const lean_object* l_Lean_Fmt_fmtBuiltinCommandCodeAction___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtBuiltinCommandCodeAction___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCommandCodeAction(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCommandCodeAction___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "fmtBuiltinCommandCodeAction"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 132, 199, 12, 242, 145, 20, 96)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunDoSeqCmd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunDoSeqCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRunCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "runCmd"};
static const lean_object* l_Lean_Fmt_fmtRunCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRunCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRunCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRunCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRunCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRunCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 158, 215, 209, 131, 110, 142, 142)}};
static const lean_object* l_Lean_Fmt_fmtRunCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRunCmd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtRunCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 97, 100, 135, 220, 167, 181, 2)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRunElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runElab"};
static const lean_object* l_Lean_Fmt_fmtRunElab___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRunElab___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRunElab___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRunElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRunElab___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRunElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 119, 23, 194, 21, 41, 64, 160)}};
static const lean_object* l_Lean_Fmt_fmtRunElab___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRunElab___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunElab___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtRunElab"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 1, 91, 69, 48, 127, 52, 123)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRunMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runMeta"};
static const lean_object* l_Lean_Fmt_fmtRunMeta___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRunMeta___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtRunMeta___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRunMeta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRunMeta___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRunMeta___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 198, 37, 218, 35, 42, 219, 1)}};
static const lean_object* l_Lean_Fmt_fmtRunMeta___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRunMeta___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunMeta(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunMeta___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtRunMeta"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 128, 125, 34, 205, 102, 228, 5)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtReduceConfig_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtReduceConfig_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtReduceConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceConfig"};
static const lean_object* l_Lean_Fmt_fmtReduceConfig___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtReduceConfig___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtReduceConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtReduceConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtReduceConfig___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtReduceConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 253, 130, 239, 111, 41, 58, 114)}};
static const lean_object* l_Lean_Fmt_fmtReduceConfig___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtReduceConfig___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReduceConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReduceConfig___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtReduceCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reduceCmd"};
static const lean_object* l_Lean_Fmt_fmtReduceCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtReduceCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtReduceCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtReduceCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtReduceCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtReduceCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 70, 101, 28, 121, 166, 124, 59)}};
static const lean_object* l_Lean_Fmt_fmtReduceCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtReduceCmd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReduceCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReduceCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtReduceCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 94, 246, 94, 60, 196, 27, 38)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSetLibrarySuggestions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "setLibrarySuggestionsCmd"};
static const lean_object* l_Lean_Fmt_fmtSetLibrarySuggestions___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSetLibrarySuggestions___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSetLibrarySuggestions___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSetLibrarySuggestions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSetLibrarySuggestions___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtSetLibrarySuggestions___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 118, 147, 72, 144, 22, 225, 39)}};
static const lean_object* l_Lean_Fmt_fmtSetLibrarySuggestions___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSetLibrarySuggestions___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSetLibrarySuggestions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSetLibrarySuggestions___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "fmtSetLibrarySuggestions"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 44, 155, 129, 57, 14, 111, 180)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "discrTreeKeyCmd"};
static const lean_object* l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 219, 125, 248, 144, 53, 202, 0)}};
static const lean_object* l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDiscrTreeKeyCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDiscrTreeKeyCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtDiscrTreeKeyCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 123, 42, 243, 17, 201, 173, 85)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "discrTreeSimpKeyCmd"};
static const lean_object* l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 149, 220, 6, 67, 233, 242, 209)}};
static const lean_object* l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtDiscrTreeSimpKeyCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 135, 146, 65, 92, 133, 151, 18)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtSeal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "commandSeal__"};
static const lean_object* l_Lean_Fmt_fmtSeal___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtSeal___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtSeal___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtSeal___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSeal___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtSeal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtSeal___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtSeal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 18, 164, 158, 224, 111, 205, 126)}};
static const lean_object* l_Lean_Fmt_fmtSeal___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtSeal___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeal___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fmtSeal"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 134, 233, 155, 64, 144, 52, 79)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtUnseal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "commandUnseal__"};
static const lean_object* l_Lean_Fmt_fmtUnseal___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtUnseal___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtUnseal___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtUnseal___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnseal___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtUnseal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtUnseal___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtUnseal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 104, 124, 98, 239, 195, 9, 203)}};
static const lean_object* l_Lean_Fmt_fmtUnseal___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtUnseal___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnseal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnseal___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtUnseal"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 246, 7, 235, 46, 17, 86, 160)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTimeCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "timeCmd"};
static const lean_object* l_Lean_Fmt_fmtTimeCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTimeCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTimeCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTimeCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTimeCmd___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtTimeCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTimeCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTimeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 30, 11, 88, 214, 137, 225, 32)}};
static const lean_object* l_Lean_Fmt_fmtTimeCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTimeCmd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtTimeCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 3, 149, 13, 62, 97, 126, 71)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCheckTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "checkTactic"};
static const lean_object* l_Lean_Fmt_fmtCheckTactic___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCheckTactic___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCheckTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCheckTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCheckTactic___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCheckTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCheckTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCheckTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 196, 193, 73, 233, 22, 219, 16)}};
static const lean_object* l_Lean_Fmt_fmtCheckTactic___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCheckTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckTactic___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtCheckTactic"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 105, 151, 74, 186, 78, 116, 236)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCheckTacticFailure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "checkTacticFailure"};
static const lean_object* l_Lean_Fmt_fmtCheckTacticFailure___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCheckTacticFailure___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCheckTacticFailure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCheckTacticFailure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCheckTacticFailure___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCheckTacticFailure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCheckTacticFailure___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCheckTacticFailure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 178, 39, 246, 220, 9, 15, 154)}};
static const lean_object* l_Lean_Fmt_fmtCheckTacticFailure___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCheckTacticFailure___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckTacticFailure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckTacticFailure___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtCheckTacticFailure"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 34, 85, 93, 90, 123, 37, 227)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCheckSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "checkSimp"};
static const lean_object* l_Lean_Fmt_fmtCheckSimp___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCheckSimp___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCheckSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCheckSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCheckSimp___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCheckSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCheckSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCheckSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 79, 163, 70, 127, 40, 174, 58)}};
static const lean_object* l_Lean_Fmt_fmtCheckSimp___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCheckSimp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckSimp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckSimp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtCheckSimp"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 6, 108, 200, 65, 45, 17, 17)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtCheckSimpFailure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "checkSimpFailure"};
static const lean_object* l_Lean_Fmt_fmtCheckSimpFailure___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtCheckSimpFailure___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtCheckSimpFailure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtCheckSimpFailure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCheckSimpFailure___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtCheckSimpFailure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtCheckSimpFailure___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtCheckSimpFailure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 64, 91, 201, 12, 111, 199, 188)}};
static const lean_object* l_Lean_Fmt_fmtCheckSimpFailure___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtCheckSimpFailure___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckSimpFailure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckSimpFailure___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtCheckSimpFailure"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 251, 194, 31, 55, 90, 204, 193)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsFilter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "guardMsgsFilter"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsFilter___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsFilter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsFilter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 187, 182, 29, 56, 60, 165, 253)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsFilter___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsFilter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "guardMsgsFilterSeverity"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsFilter___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsFilter___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsFilter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 215, 239, 32, 31, 172, 250, 25)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsFilter___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsFilter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "guardMsgsFilterAction"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsFilter___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsFilter___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsFilter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__4_value),LEAN_SCALAR_PTR_LITERAL(20, 4, 244, 232, 164, 150, 223, 103)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsFilter___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsFilter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsFilter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsFilter___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtGuardMsgsFilter"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 6, 180, 9, 96, 154, 231, 184)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "guardMsgsWhitespace"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 106, 1, 198, 8, 55, 77, 8)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "guardMsgsWhitespaceArg"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 245, 235, 68, 150, 72, 242, 178)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsWhitespace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsWhitespace___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtGuardMsgsWhitespace"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 154, 86, 143, 146, 163, 250, 175)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsOrdering___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "guardMsgsOrdering"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsOrdering___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsOrdering___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsOrdering___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsOrdering___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsOrdering___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsOrdering___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 53, 236, 42, 85, 133, 64, 61)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsOrdering___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsOrdering___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsOrdering___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "guardMsgsOrderingArg"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsOrdering___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsOrdering___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsOrdering___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsOrdering___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsOrdering___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsOrdering___closed__2_value),LEAN_SCALAR_PTR_LITERAL(126, 165, 201, 178, 250, 91, 17, 12)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsOrdering___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsOrdering___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsOrdering(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsOrdering___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtGuardMsgsOrdering"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 126, 23, 246, 212, 142, 167, 51)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsPositions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "guardMsgsPositions"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsPositions___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsPositions___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsPositions___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsPositions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsPositions___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsPositions___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 241, 109, 166, 211, 83, 245, 15)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsPositions___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsPositions___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsPositions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "guardMsgsPositionsArg"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsPositions___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsPositions___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsPositions___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsPositions___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsPositions___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsPositions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 235, 102, 225, 139, 166, 36, 119)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsPositions___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsPositions___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsPositions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsPositions___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtGuardMsgsPositions"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 64, 158, 4, 233, 162, 47, 124)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsSubstring___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "guardMsgsSubstring"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsSubstring___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsSubstring___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsSubstring___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsSubstring___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsSubstring___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsSubstring___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 68, 193, 70, 193, 109, 117, 133)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsSubstring___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsSubstring___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSubstring(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSubstring___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtGuardMsgsSubstring"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 122, 159, 9, 136, 203, 224, 116)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSpecElt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSpecElt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "guardMsgsSpecElt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 108, 205, 157, 13, 129, 29, 60)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtGuardMsgsSpecElt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 21, 235, 68, 159, 214, 16, 86)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "guardMsgsSpec"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsSpec___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsSpec___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsSpec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsSpec___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsSpec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 228, 141, 39, 164, 16, 16, 29)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsSpec___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsSpec___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsSpec___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsSpec___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSpec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSpec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGuardMsgsSpec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 117, 134, 186, 87, 5, 137, 28)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "guardMsgsCmd"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(80, 121, 62, 112, 73, 11, 102, 99)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsCmd___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtDocComment"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsCmd___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 24, 108, 32, 4, 238, 127, 124)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsCmd___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsCmd___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsCmd___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__7_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardMsgsCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__7_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtGuardMsgsCmd___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtGuardMsgsCmd___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtGuardMsgsCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 63, 75, 33, 31, 200, 61, 100)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGuardPanicCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "guardPanicCmd"};
static const lean_object* l_Lean_Fmt_fmtGuardPanicCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGuardPanicCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtGuardPanicCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGuardPanicCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGuardPanicCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGuardPanicCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 189, 140, 114, 132, 102, 231, 43)}};
static const lean_object* l_Lean_Fmt_fmtGuardPanicCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGuardPanicCmd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardPanicCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardPanicCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtGuardPanicCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 234, 31, 103, 186, 98, 38, 12)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtInfoTreesCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "infoTreesCmd"};
static const lean_object* l_Lean_Fmt_fmtInfoTreesCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtInfoTreesCmd___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtInfoTreesCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtInfoTreesCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtInfoTreesCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtInfoTreesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 96, 116, 19, 43, 63, 104, 107)}};
static const lean_object* l_Lean_Fmt_fmtInfoTreesCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtInfoTreesCmd___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfoTreesCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfoTreesCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtInfoTreesCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 85, 240, 203, 152, 168, 239, 42)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrecParen(lean_object* v_x_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lean_Fmt_fmtPrecParen___closed__1));
lean_inc(v_x_4_);
v___x_8_ = l_Lean_Syntax_isOfKind(v_x_4_, v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_x_4_);
v___x_9_ = l_Lean_Fmt_Error_partialFormatter;
v___x_10_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v_a_6_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v_lbTk_12_; lean_object* v___x_13_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v_lbTk_12_ = l_Lean_Syntax_getArg(v_x_4_, v___x_11_);
v___x_13_ = l_Lean_Fmt_fmt(v_lbTk_12_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v_a_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
v_a_15_ = lean_ctor_get(v___x_13_, 1);
lean_inc(v_a_15_);
lean_dec_ref_known(v___x_13_, 2);
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = l_Lean_Syntax_getArg(v_x_4_, v___x_16_);
v___x_18_ = l_Lean_Fmt_fmt(v___x_17_, v_a_5_, v_a_15_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v_a_20_; lean_object* v___x_21_; lean_object* v_rbTk_22_; lean_object* v___x_23_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
v_a_20_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_a_20_);
lean_dec_ref_known(v___x_18_, 2);
v___x_21_ = lean_unsigned_to_nat(2u);
v_rbTk_22_ = l_Lean_Syntax_getArg(v_x_4_, v___x_21_);
lean_dec(v_x_4_);
v___x_23_ = l_Lean_Fmt_fmt(v_rbTk_22_, v_a_5_, v_a_20_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_33_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_a_25_ = lean_ctor_get(v___x_23_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_33_ == 0)
{
v___x_27_ = v___x_23_;
v_isShared_28_ = v_isSharedCheck_33_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_33_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; lean_object* v___x_31_; 
v___x_29_ = l_Lean_Fmt_Layouts_parens(v_a_14_, v_a_19_, v_a_24_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_29_);
v___x_31_ = v___x_27_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_a_25_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
else
{
lean_dec(v_a_19_);
lean_dec(v_a_14_);
return v___x_23_;
}
}
else
{
lean_dec(v_a_14_);
lean_dec(v_x_4_);
return v___x_18_;
}
}
else
{
lean_dec(v_x_4_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrecParen___boxed(lean_object* v_x_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Fmt_fmtPrecParen(v_x_34_, v_a_35_, v_a_36_);
lean_dec_ref(v_a_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1(){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_46_ = l_Lean_Fmt_fmtAttribute;
v___x_47_ = ((lean_object*)(l_Lean_Fmt_fmtPrecParen___closed__1));
v___x_48_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___closed__3));
v___x_49_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPrecParen___boxed), 3, 0);
v___x_50_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_46_, v___x_47_, v___x_48_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1___boxed(lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1();
return v_res_52_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtAddPrec___closed__2(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_box(0);
v___x_60_ = lean_unsigned_to_nat(16u);
v___x_61_ = lean_mk_array(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtAddPrec___closed__3(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&l_Lean_Fmt_fmtAddPrec___closed__2, &l_Lean_Fmt_fmtAddPrec___closed__2_once, _init_l_Lean_Fmt_fmtAddPrec___closed__2);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtAddPrec___closed__4(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; 
v___x_65_ = lean_obj_once(&l_Lean_Fmt_fmtAddPrec___closed__3, &l_Lean_Fmt_fmtAddPrec___closed__3_once, _init_l_Lean_Fmt_fmtAddPrec___closed__3);
v___x_66_ = ((lean_object*)(l_Lean_Fmt_fmtAddPrec___closed__1));
v___x_67_ = 0;
v___x_68_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set(v___x_68_, 1, v___x_65_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*2, v___x_67_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*2 + 1, v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtAddPrec(void){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_obj_once(&l_Lean_Fmt_fmtAddPrec___closed__4, &l_Lean_Fmt_fmtAddPrec___closed__4_once, _init_l_Lean_Fmt_fmtAddPrec___closed__4);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1(){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_84_ = l_Lean_Fmt_infixFmtAttribute;
v___x_85_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__3));
v___x_86_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___closed__5));
v___x_87_ = l_Lean_Fmt_fmtAddPrec;
v___x_88_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_84_, v___x_85_, v___x_86_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1___boxed(lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1();
return v_res_90_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSubPrec(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Lean_Fmt_fmtAddPrec___closed__4, &l_Lean_Fmt_fmtAddPrec___closed__4_once, _init_l_Lean_Fmt_fmtAddPrec___closed__4);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1(){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_104_ = l_Lean_Fmt_infixFmtAttribute;
v___x_105_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__1));
v___x_106_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___closed__3));
v___x_107_ = l_Lean_Fmt_fmtSubPrec;
v___x_108_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_104_, v___x_105_, v___x_106_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1___boxed(lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1();
return v_res_110_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtAddPrio(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_Fmt_fmtAddPrec___closed__4, &l_Lean_Fmt_fmtAddPrec___closed__4_once, _init_l_Lean_Fmt_fmtAddPrec___closed__4);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1(){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_124_ = l_Lean_Fmt_infixFmtAttribute;
v___x_125_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__1));
v___x_126_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___closed__3));
v___x_127_ = l_Lean_Fmt_fmtAddPrio;
v___x_128_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_124_, v___x_125_, v___x_126_, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1___boxed(lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1();
return v_res_130_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtSubPrio(void){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&l_Lean_Fmt_fmtAddPrec___closed__4, &l_Lean_Fmt_fmtAddPrec___closed__4_once, _init_l_Lean_Fmt_fmtAddPrec___closed__4);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_144_ = l_Lean_Fmt_infixFmtAttribute;
v___x_145_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__1));
v___x_146_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___closed__3));
v___x_147_ = l_Lean_Fmt_fmtSubPrio;
v___x_148_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_144_, v___x_145_, v___x_146_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1___boxed(lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1();
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrioParen(lean_object* v_x_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_Fmt_fmtPrioParen___closed__1));
lean_inc(v_x_154_);
v___x_158_ = l_Lean_Syntax_isOfKind(v_x_154_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v_x_154_);
v___x_159_ = l_Lean_Fmt_Error_partialFormatter;
v___x_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v_a_156_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; lean_object* v_lbTk_162_; lean_object* v___x_163_; 
v___x_161_ = lean_unsigned_to_nat(0u);
v_lbTk_162_ = l_Lean_Syntax_getArg(v_x_154_, v___x_161_);
v___x_163_ = l_Lean_Fmt_fmt(v_lbTk_162_, v_a_155_, v_a_156_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v_a_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
v_a_165_ = lean_ctor_get(v___x_163_, 1);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_163_, 2);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = l_Lean_Syntax_getArg(v_x_154_, v___x_166_);
v___x_168_ = l_Lean_Fmt_fmt(v___x_167_, v_a_155_, v_a_165_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v_a_170_; lean_object* v___x_171_; lean_object* v_rbTk_172_; lean_object* v___x_173_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
v_a_170_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_a_170_);
lean_dec_ref_known(v___x_168_, 2);
v___x_171_ = lean_unsigned_to_nat(2u);
v_rbTk_172_ = l_Lean_Syntax_getArg(v_x_154_, v___x_171_);
lean_dec(v_x_154_);
v___x_173_ = l_Lean_Fmt_fmt(v_rbTk_172_, v_a_155_, v_a_170_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_a_175_ = lean_ctor_get(v___x_173_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v___x_173_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = l_Lean_Fmt_Layouts_parens(v_a_164_, v_a_169_, v_a_174_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_a_175_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_dec(v_a_169_);
lean_dec(v_a_164_);
return v___x_173_;
}
}
else
{
lean_dec(v_a_164_);
lean_dec(v_x_154_);
return v___x_168_;
}
}
else
{
lean_dec(v_x_154_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrioParen___boxed(lean_object* v_x_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Fmt_fmtPrioParen(v_x_184_, v_a_185_, v_a_186_);
lean_dec_ref(v_a_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1(){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_194_ = l_Lean_Fmt_fmtAttribute;
v___x_195_ = ((lean_object*)(l_Lean_Fmt_fmtPrioParen___closed__1));
v___x_196_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___closed__1));
v___x_197_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPrioParen___boxed), 3, 0);
v___x_198_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_194_, v___x_195_, v___x_196_, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1___boxed(lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1();
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxPostfix(lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Fmt_fmtPostfixOperator(v_a_201_, v_a_202_, v_a_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxPostfix___boxed(lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Fmt_fmtStxPostfix(v_a_205_, v_a_206_, v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1(){
_start:
{
lean_object* v___f_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___f_219_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__0));
v___x_220_ = l_Lean_Fmt_fmtAttribute;
v___x_221_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__2));
v___x_222_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4));
v___x_223_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_220_, v___x_221_, v___x_222_, v___f_219_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___boxed(lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1();
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3(){
_start:
{
lean_object* v___f_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___f_230_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__0));
v___x_231_ = l_Lean_Fmt_fmtAttribute;
v___x_232_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3___closed__1));
v___x_233_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4));
v___x_234_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_231_, v___x_232_, v___x_233_, v___f_230_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3___boxed(lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3();
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5(){
_start:
{
lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___f_241_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__0));
v___x_242_ = l_Lean_Fmt_fmtAttribute;
v___x_243_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5___closed__1));
v___x_244_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4));
v___x_245_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_242_, v___x_243_, v___x_244_, v___f_241_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5___boxed(lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5();
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7(){
_start:
{
lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___f_252_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__0));
v___x_253_ = l_Lean_Fmt_fmtAttribute;
v___x_254_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7___closed__1));
v___x_255_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4));
v___x_256_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_253_, v___x_254_, v___x_255_, v___f_252_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7___boxed(lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7();
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9(){
_start:
{
lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___f_263_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__0));
v___x_264_ = l_Lean_Fmt_fmtAttribute;
v___x_265_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9___closed__1));
v___x_266_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4));
v___x_267_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_264_, v___x_265_, v___x_266_, v___f_263_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9___boxed(lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9();
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11(){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___f_274_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__0));
v___x_275_ = l_Lean_Fmt_fmtAttribute;
v___x_276_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11___closed__1));
v___x_277_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1___closed__4));
v___x_278_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_275_, v___x_276_, v___x_277_, v___f_274_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11___boxed(lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11();
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorIdx___impl(uint8_t v_x_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_box(v_x_281_);
v___x_283_ = lean_obj_tag_nat(v___x_282_);
lean_dec(v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorIdx___impl___boxed(lean_object* v_x_284_){
_start:
{
uint8_t v_x_4__boxed_285_; lean_object* v_res_286_; 
v_x_4__boxed_285_ = lean_unbox(v_x_284_);
v_res_286_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorIdx___impl(v_x_4__boxed_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorElim___redArg(lean_object* v_k_287_){
_start:
{
lean_inc(v_k_287_);
return v_k_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorElim___redArg___boxed(lean_object* v_k_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorElim___redArg(v_k_288_);
lean_dec(v_k_288_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorElim(lean_object* v_motive_290_, lean_object* v_ctorIdx_291_, uint8_t v_t_292_, lean_object* v_h_293_, lean_object* v_k_294_){
_start:
{
lean_inc(v_k_294_);
return v_k_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorElim___boxed(lean_object* v_motive_295_, lean_object* v_ctorIdx_296_, lean_object* v_t_297_, lean_object* v_h_298_, lean_object* v_k_299_){
_start:
{
uint8_t v_t_boxed_300_; lean_object* v_res_301_; 
v_t_boxed_300_ = lean_unbox(v_t_297_);
v_res_301_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_ctorElim(v_motive_295_, v_ctorIdx_296_, v_t_boxed_300_, v_h_298_, v_k_299_);
lean_dec(v_k_299_);
lean_dec(v_ctorIdx_296_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_empty_elim___redArg(lean_object* v_empty_302_){
_start:
{
lean_inc(v_empty_302_);
return v_empty_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_empty_elim___redArg___boxed(lean_object* v_empty_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_empty_elim___redArg(v_empty_303_);
lean_dec(v_empty_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_empty_elim(lean_object* v_motive_305_, uint8_t v_t_306_, lean_object* v_h_307_, lean_object* v_empty_308_){
_start:
{
lean_inc(v_empty_308_);
return v_empty_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_empty_elim___boxed(lean_object* v_motive_309_, lean_object* v_t_310_, lean_object* v_h_311_, lean_object* v_empty_312_){
_start:
{
uint8_t v_t_boxed_313_; lean_object* v_res_314_; 
v_t_boxed_313_ = lean_unbox(v_t_310_);
v_res_314_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_empty_elim(v_motive_309_, v_t_boxed_313_, v_h_311_, v_empty_312_);
lean_dec(v_empty_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInNonIdent_elim___redArg(lean_object* v_endsInNonIdent_315_){
_start:
{
lean_inc(v_endsInNonIdent_315_);
return v_endsInNonIdent_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInNonIdent_elim___redArg___boxed(lean_object* v_endsInNonIdent_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInNonIdent_elim___redArg(v_endsInNonIdent_316_);
lean_dec(v_endsInNonIdent_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInNonIdent_elim(lean_object* v_motive_318_, uint8_t v_t_319_, lean_object* v_h_320_, lean_object* v_endsInNonIdent_321_){
_start:
{
lean_inc(v_endsInNonIdent_321_);
return v_endsInNonIdent_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInNonIdent_elim___boxed(lean_object* v_motive_322_, lean_object* v_t_323_, lean_object* v_h_324_, lean_object* v_endsInNonIdent_325_){
_start:
{
uint8_t v_t_boxed_326_; lean_object* v_res_327_; 
v_t_boxed_326_ = lean_unbox(v_t_323_);
v_res_327_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInNonIdent_elim(v_motive_322_, v_t_boxed_326_, v_h_324_, v_endsInNonIdent_325_);
lean_dec(v_endsInNonIdent_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInIdent_elim___redArg(lean_object* v_endsInIdent_328_){
_start:
{
lean_inc(v_endsInIdent_328_);
return v_endsInIdent_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInIdent_elim___redArg___boxed(lean_object* v_endsInIdent_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInIdent_elim___redArg(v_endsInIdent_329_);
lean_dec(v_endsInIdent_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInIdent_elim(lean_object* v_motive_331_, uint8_t v_t_332_, lean_object* v_h_333_, lean_object* v_endsInIdent_334_){
_start:
{
lean_inc(v_endsInIdent_334_);
return v_endsInIdent_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInIdent_elim___boxed(lean_object* v_motive_335_, lean_object* v_t_336_, lean_object* v_h_337_, lean_object* v_endsInIdent_338_){
_start:
{
uint8_t v_t_boxed_339_; lean_object* v_res_340_; 
v_t_boxed_339_ = lean_unbox(v_t_336_);
v_res_340_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_EndsInIdent_endsInIdent_elim(v_motive_335_, v_t_boxed_339_, v_h_337_, v_endsInIdent_338_);
lean_dec(v_endsInIdent_338_);
return v_res_340_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedEndsInIdent_default(void){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = 0;
return v___x_341_;
}
}
static uint8_t _init_l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instInhabitedEndsInIdent(void){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = 0;
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent_prio(uint8_t v_a_343_){
_start:
{
switch(v_a_343_)
{
case 0:
{
lean_object* v___x_344_; 
v___x_344_ = lean_unsigned_to_nat(0u);
return v___x_344_;
}
case 1:
{
lean_object* v___x_345_; 
v___x_345_ = lean_unsigned_to_nat(2u);
return v___x_345_;
}
default: 
{
lean_object* v___x_346_; 
v___x_346_ = lean_unsigned_to_nat(1u);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent_prio___boxed(lean_object* v_a_347_){
_start:
{
uint8_t v_a_34__boxed_348_; lean_object* v_res_349_; 
v_a_34__boxed_348_ = lean_unbox(v_a_347_);
v_res_349_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent_prio(v_a_34__boxed_348_);
return v_res_349_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent___lam__0(uint8_t v_a_350_, uint8_t v_b_351_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_352_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent_prio(v_b_351_);
v___x_353_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent_prio(v_a_350_);
v___x_354_ = lean_nat_dec_le(v___x_352_, v___x_353_);
lean_dec(v___x_353_);
lean_dec(v___x_352_);
if (v___x_354_ == 0)
{
return v_b_351_;
}
else
{
return v_a_350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent___lam__0___boxed(lean_object* v_a_355_, lean_object* v_b_356_){
_start:
{
uint8_t v_a_boxed_357_; uint8_t v_b_boxed_358_; uint8_t v_res_359_; lean_object* v_r_360_; 
v_a_boxed_357_ = lean_unbox(v_a_355_);
v_b_boxed_358_ = lean_unbox(v_b_356_);
v_res_359_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent___lam__0(v_a_boxed_357_, v_b_boxed_358_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__1(lean_object* v_as_363_, size_t v_i_364_, size_t v_stop_365_, lean_object* v_b_366_){
_start:
{
lean_object* v___y_368_; uint8_t v___x_372_; 
v___x_372_ = lean_usize_dec_eq(v_i_364_, v_stop_365_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = lean_array_uget_borrowed(v_as_363_, v_i_364_);
v___x_374_ = lean_unbox(v___x_373_);
if (v___x_374_ == 0)
{
v___y_368_ = v_b_366_;
goto v___jp_367_;
}
else
{
lean_object* v___x_375_; 
lean_inc(v___x_373_);
v___x_375_ = lean_array_push(v_b_366_, v___x_373_);
v___y_368_ = v___x_375_;
goto v___jp_367_;
}
}
else
{
return v_b_366_;
}
v___jp_367_:
{
size_t v___x_369_; size_t v___x_370_; 
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_add(v_i_364_, v___x_369_);
v_i_364_ = v___x_370_;
v_b_366_ = v___y_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__1___boxed(lean_object* v_as_376_, lean_object* v_i_377_, lean_object* v_stop_378_, lean_object* v_b_379_){
_start:
{
size_t v_i_boxed_380_; size_t v_stop_boxed_381_; lean_object* v_res_382_; 
v_i_boxed_380_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_stop_boxed_381_ = lean_unbox_usize(v_stop_378_);
lean_dec(v_stop_378_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__1(v_as_376_, v_i_boxed_380_, v_stop_boxed_381_, v_b_379_);
lean_dec_ref(v_as_376_);
return v_res_382_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2_spec__3(lean_object* v_as_383_, size_t v_i_384_, size_t v_stop_385_, uint8_t v_b_386_){
_start:
{
uint8_t v___y_388_; uint8_t v___x_392_; 
v___x_392_ = lean_usize_dec_eq(v_i_384_, v_stop_385_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_393_ = lean_array_uget_borrowed(v_as_383_, v_i_384_);
v___x_394_ = lean_unbox(v___x_393_);
v___x_395_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent_prio(v___x_394_);
v___x_396_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instMaxEndsInIdent_prio(v_b_386_);
v___x_397_ = lean_nat_dec_le(v___x_395_, v___x_396_);
lean_dec(v___x_396_);
lean_dec(v___x_395_);
if (v___x_397_ == 0)
{
uint8_t v___x_398_; 
v___x_398_ = lean_unbox(v___x_393_);
v___y_388_ = v___x_398_;
goto v___jp_387_;
}
else
{
v___y_388_ = v_b_386_;
goto v___jp_387_;
}
}
else
{
return v_b_386_;
}
v___jp_387_:
{
size_t v___x_389_; size_t v___x_390_; 
v___x_389_ = ((size_t)1ULL);
v___x_390_ = lean_usize_add(v_i_384_, v___x_389_);
v_i_384_ = v___x_390_;
v_b_386_ = v___y_388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2_spec__3___boxed(lean_object* v_as_399_, lean_object* v_i_400_, lean_object* v_stop_401_, lean_object* v_b_402_){
_start:
{
size_t v_i_boxed_403_; size_t v_stop_boxed_404_; uint8_t v_b_boxed_405_; uint8_t v_res_406_; lean_object* v_r_407_; 
v_i_boxed_403_ = lean_unbox_usize(v_i_400_);
lean_dec(v_i_400_);
v_stop_boxed_404_ = lean_unbox_usize(v_stop_401_);
lean_dec(v_stop_401_);
v_b_boxed_405_ = lean_unbox(v_b_402_);
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2_spec__3(v_as_399_, v_i_boxed_403_, v_stop_boxed_404_, v_b_boxed_405_);
lean_dec_ref(v_as_399_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT uint8_t l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2___redArg(lean_object* v_arr_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_array_fget_borrowed(v_arr_408_, v___x_409_);
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_array_get_size(v_arr_408_);
v___x_413_ = lean_nat_dec_lt(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; 
v___x_414_ = lean_unbox(v___x_410_);
return v___x_414_;
}
else
{
size_t v___x_415_; size_t v___x_416_; uint8_t v___x_417_; uint8_t v___x_418_; 
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_of_nat(v___x_412_);
v___x_417_ = lean_unbox(v___x_410_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2_spec__3(v_arr_408_, v___x_415_, v___x_416_, v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2___redArg___boxed(lean_object* v_arr_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2___redArg(v_arr_419_);
lean_dec_ref(v_arr_419_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2(lean_object* v_arr_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_423_ = lean_array_get_size(v_arr_422_);
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_nat_dec_eq(v___x_423_, v___x_424_);
if (v___x_425_ == 0)
{
uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2___redArg(v_arr_422_);
v___x_427_ = lean_box(v___x_426_);
v___x_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_box(0);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2___boxed(lean_object* v_arr_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2(v_arr_430_);
lean_dec_ref(v_arr_430_);
return v_res_431_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent(lean_object* v_a_437_){
_start:
{
lean_object* v___y_439_; 
switch(lean_obj_tag(v_a_437_))
{
case 0:
{
uint8_t v___x_447_; 
v___x_447_ = 0;
return v___x_447_;
}
case 1:
{
lean_object* v_kind_448_; lean_object* v_args_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_kind_448_ = lean_ctor_get(v_a_437_, 1);
lean_inc(v_kind_448_);
v_args_449_ = lean_ctor_get(v_a_437_, 2);
lean_inc_ref(v_args_449_);
lean_dec_ref_known(v_a_437_, 3);
v___x_450_ = lean_array_get_size(v_args_449_);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_nat_dec_eq(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__1));
v___x_454_ = lean_name_eq(v_kind_448_, v___x_453_);
lean_dec(v_kind_448_);
if (v___x_454_ == 0)
{
size_t v_sz_455_; size_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_sz_455_ = lean_array_size(v_args_449_);
v___x_456_ = ((size_t)0ULL);
v___x_457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__0(v_sz_455_, v___x_456_, v_args_449_);
v___x_458_ = lean_array_get_size(v___x_457_);
v___x_459_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___closed__2));
v___x_460_ = lean_nat_dec_lt(v___x_451_, v___x_458_);
if (v___x_460_ == 0)
{
lean_dec_ref(v___x_457_);
v___y_439_ = v___x_459_;
goto v___jp_438_;
}
else
{
size_t v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_usize_of_nat(v___x_458_);
v___x_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__1(v___x_457_, v___x_456_, v___x_461_, v___x_459_);
lean_dec_ref(v___x_457_);
v___y_439_ = v___x_462_;
goto v___jp_438_;
}
}
else
{
size_t v_sz_463_; size_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_sz_463_ = lean_array_size(v_args_449_);
v___x_464_ = ((size_t)0ULL);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__0(v_sz_463_, v___x_464_, v_args_449_);
v___x_466_ = l_Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2(v___x_465_);
lean_dec_ref(v___x_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
uint8_t v___x_467_; 
v___x_467_ = 0;
return v___x_467_;
}
else
{
lean_object* v_val_468_; uint8_t v___x_469_; 
v_val_468_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_val_468_);
lean_dec_ref_known(v___x_466_, 1);
v___x_469_ = lean_unbox(v_val_468_);
lean_dec(v_val_468_);
return v___x_469_;
}
}
}
else
{
uint8_t v___x_470_; 
lean_dec_ref(v_args_449_);
lean_dec(v_kind_448_);
v___x_470_ = 0;
return v___x_470_;
}
}
case 2:
{
uint8_t v___x_471_; 
lean_dec_ref_known(v_a_437_, 2);
v___x_471_ = 1;
return v___x_471_;
}
default: 
{
uint8_t v___x_472_; 
lean_dec_ref_known(v_a_437_, 4);
v___x_472_ = 2;
return v___x_472_;
}
}
v___jp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_440_ = lean_array_get_size(v___y_439_);
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_sub(v___x_440_, v___x_441_);
v___x_443_ = lean_nat_dec_lt(v___x_442_, v___x_440_);
if (v___x_443_ == 0)
{
uint8_t v___x_444_; 
lean_dec(v___x_442_);
lean_dec_ref(v___y_439_);
v___x_444_ = 0;
return v___x_444_;
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_array_fget(v___y_439_, v___x_442_);
lean_dec(v___x_442_);
lean_dec_ref(v___y_439_);
v___x_446_ = lean_unbox(v___x_445_);
lean_dec(v___x_445_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__0(size_t v_sz_473_, size_t v_i_474_, lean_object* v_bs_475_){
_start:
{
uint8_t v___x_476_; 
v___x_476_ = lean_usize_dec_lt(v_i_474_, v_sz_473_);
if (v___x_476_ == 0)
{
return v_bs_475_;
}
else
{
lean_object* v_v_477_; lean_object* v___x_478_; lean_object* v_bs_x27_479_; uint8_t v___x_480_; size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_v_477_ = lean_array_uget(v_bs_475_, v_i_474_);
v___x_478_ = lean_unsigned_to_nat(0u);
v_bs_x27_479_ = lean_array_uset(v_bs_475_, v_i_474_, v___x_478_);
v___x_480_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent(v_v_477_);
v___x_481_ = ((size_t)1ULL);
v___x_482_ = lean_usize_add(v_i_474_, v___x_481_);
v___x_483_ = lean_box(v___x_480_);
v___x_484_ = lean_array_uset(v_bs_x27_479_, v_i_474_, v___x_483_);
v_i_474_ = v___x_482_;
v_bs_475_ = v___x_484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__0___boxed(lean_object* v_sz_486_, lean_object* v_i_487_, lean_object* v_bs_488_){
_start:
{
size_t v_sz_boxed_489_; size_t v_i_boxed_490_; lean_object* v_res_491_; 
v_sz_boxed_489_ = lean_unbox_usize(v_sz_486_);
lean_dec(v_sz_486_);
v_i_boxed_490_ = lean_unbox_usize(v_i_487_);
lean_dec(v_i_487_);
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__0(v_sz_boxed_489_, v_i_boxed_490_, v_bs_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent___boxed(lean_object* v_a_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent(v_a_492_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT uint8_t l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2(lean_object* v_arr_495_, lean_object* v_h_496_){
_start:
{
uint8_t v___x_497_; 
v___x_497_ = l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2___redArg(v_arr_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2___boxed(lean_object* v_arr_498_, lean_object* v_h_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Array_max___at___00Array_max_x3f___at___00__private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent_spec__2_spec__2(v_arr_498_, v_h_499_);
lean_dec_ref(v_arr_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxOptional(lean_object* v_stx_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_505_ = l_Lean_Syntax_getNumArgs(v_stx_502_);
v___x_506_ = lean_unsigned_to_nat(2u);
v___x_507_ = lean_nat_dec_eq(v___x_505_, v___x_506_);
lean_dec(v___x_505_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = l_Lean_Fmt_Error_partialFormatter;
v___x_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_a_504_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_502_, v___x_510_, v_a_504_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v_a_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
v_a_513_ = lean_ctor_get(v___x_511_, 1);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_511_, 2);
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_502_, v___x_514_, v_a_513_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v_a_517_; uint8_t v___x_518_; lean_object* v___x_519_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
v_a_517_ = lean_ctor_get(v___x_515_, 1);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_515_, 2);
lean_inc(v_a_512_);
v___x_518_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional_endsInIdent(v_a_512_);
v___x_519_ = l_Lean_Fmt_fmt(v_a_512_, v_a_503_, v_a_517_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v_a_521_; lean_object* v___x_522_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
v_a_521_ = lean_ctor_get(v___x_519_, 1);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_519_, 2);
v___x_522_ = l_Lean_Fmt_fmt(v_a_516_, v_a_503_, v_a_521_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_536_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_a_524_ = lean_ctor_get(v___x_522_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_536_ == 0)
{
v___x_526_ = v___x_522_;
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_536_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
uint8_t v___y_529_; 
if (v___x_518_ == 2)
{
uint8_t v___x_534_; 
v___x_534_ = 1;
v___y_529_ = v___x_534_;
goto v___jp_528_;
}
else
{
uint8_t v___x_535_; 
v___x_535_ = 0;
v___y_529_ = v___x_535_;
goto v___jp_528_;
}
v___jp_528_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = l_Lean_Fmt_Layouts_postfixOperator(v_a_520_, v_a_523_, v___y_529_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_530_);
v___x_532_ = v___x_526_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_a_524_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_dec(v_a_520_);
return v___x_522_;
}
}
else
{
lean_dec(v_a_516_);
return v___x_519_;
}
}
else
{
lean_object* v_a_537_; lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec(v_a_512_);
v_a_537_ = lean_ctor_get(v___x_515_, 0);
v_a_538_ = lean_ctor_get(v___x_515_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_515_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_inc(v_a_537_);
lean_dec(v___x_515_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_537_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_546_ = lean_ctor_get(v___x_511_, 0);
v_a_547_ = lean_ctor_get(v___x_511_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_511_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_inc(v_a_546_);
lean_dec(v___x_511_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_546_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxOptional___boxed(lean_object* v_stx_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Fmt_fmtStxOptional(v_stx_555_, v_a_556_, v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_stx_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1(){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_568_ = l_Lean_Fmt_fmtAttribute;
v___x_569_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__1));
v___x_570_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___closed__3));
v___x_571_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtStxOptional___boxed), 3, 0);
v___x_572_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_568_, v___x_569_, v___x_570_, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1___boxed(lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1();
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxNotFollowedBy(lean_object* v_x_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = ((lean_object*)(l_Lean_Fmt_fmtStxNotFollowedBy___closed__1));
lean_inc(v_x_578_);
v___x_582_ = l_Lean_Syntax_isOfKind(v_x_578_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v_x_578_);
v___x_583_ = l_Lean_Fmt_Error_partialFormatter;
v___x_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v_a_580_);
return v___x_584_;
}
else
{
lean_object* v___x_585_; lean_object* v_notTk_586_; lean_object* v___x_587_; 
v___x_585_ = lean_unsigned_to_nat(0u);
v_notTk_586_ = l_Lean_Syntax_getArg(v_x_578_, v___x_585_);
v___x_587_ = l_Lean_Fmt_fmt(v_notTk_586_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
v_a_589_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_587_, 2);
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = l_Lean_Syntax_getArg(v_x_578_, v___x_590_);
lean_dec(v_x_578_);
v___x_592_ = l_Lean_Fmt_fmt(v___x_591_, v_a_579_, v_a_589_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_603_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_a_594_ = lean_ctor_get(v___x_592_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_603_ == 0)
{
v___x_596_ = v___x_592_;
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_598_ = 1;
v___x_599_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_588_, v_a_593_, v___x_598_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_599_);
v___x_601_ = v___x_596_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_a_594_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
lean_dec(v_a_588_);
return v___x_592_;
}
}
else
{
lean_dec(v_x_578_);
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStxNotFollowedBy___boxed(lean_object* v_x_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Fmt_fmtStxNotFollowedBy(v_x_604_, v_a_605_, v_a_606_);
lean_dec_ref(v_a_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1(){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_614_ = l_Lean_Fmt_fmtAttribute;
v___x_615_ = ((lean_object*)(l_Lean_Fmt_fmtStxNotFollowedBy___closed__1));
v___x_616_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___closed__1));
v___x_617_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtStxNotFollowedBy___boxed), 3, 0);
v___x_618_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_614_, v___x_615_, v___x_616_, v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1___boxed(lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1();
return v_res_620_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtStxOrelse___closed__2(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; 
v___x_626_ = lean_obj_once(&l_Lean_Fmt_fmtAddPrec___closed__3, &l_Lean_Fmt_fmtAddPrec___closed__3_once, _init_l_Lean_Fmt_fmtAddPrec___closed__3);
v___x_627_ = ((lean_object*)(l_Lean_Fmt_fmtStxOrelse___closed__1));
v___x_628_ = 0;
v___x_629_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v___x_626_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*2, v___x_628_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*2 + 1, v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtStxOrelse(void){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_obj_once(&l_Lean_Fmt_fmtStxOrelse___closed__2, &l_Lean_Fmt_fmtStxOrelse___closed__2_once, _init_l_Lean_Fmt_fmtStxOrelse___closed__2);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1(){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_640_ = l_Lean_Fmt_infixFmtAttribute;
v___x_641_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__1));
v___x_642_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___closed__3));
v___x_643_ = l_Lean_Fmt_fmtStxOrelse;
v___x_644_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_640_, v___x_641_, v___x_642_, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1___boxed(lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1();
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermNot(lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Fmt_fmtPrefixOperator(v_a_647_, v_a_648_, v_a_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermNot___boxed(lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Fmt_fmtTermNot(v_a_651_, v_a_652_, v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1(){
_start:
{
lean_object* v___f_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___f_665_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__0));
v___x_666_ = l_Lean_Fmt_fmtAttribute;
v___x_667_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__2));
v___x_668_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__4));
v___x_669_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_666_, v___x_667_, v___x_668_, v___f_665_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___boxed(lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1();
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3(){
_start:
{
lean_object* v___f_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___f_676_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__0));
v___x_677_ = l_Lean_Fmt_fmtAttribute;
v___x_678_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3___closed__1));
v___x_679_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1___closed__4));
v___x_680_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_677_, v___x_678_, v___x_679_, v___f_676_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3___boxed(lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3();
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermNeg(lean_object* v_x_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_Fmt_fmtTermNeg___closed__1));
lean_inc(v_x_689_);
v___x_693_ = l_Lean_Syntax_isOfKind(v_x_689_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
lean_dec(v_x_689_);
v___x_694_ = l_Lean_Fmt_Error_partialFormatter;
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_a_691_);
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v_negTk_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v_negTk_697_ = l_Lean_Syntax_getArg(v_x_689_, v___x_696_);
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = l_Lean_Syntax_getArg(v_x_689_, v___x_698_);
lean_dec(v_x_689_);
v___x_700_ = ((lean_object*)(l_Lean_Fmt_fmtTermNeg___closed__3));
lean_inc(v___x_699_);
v___x_701_ = l_Lean_Syntax_isOfKind(v___x_699_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Fmt_fmt(v_negTk_697_, v_a_690_, v_a_691_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v_a_704_; lean_object* v___x_705_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
v_a_704_ = lean_ctor_get(v___x_702_, 1);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_702_, 2);
v___x_705_ = l_Lean_Fmt_fmt(v___x_699_, v_a_690_, v_a_704_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_716_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_a_707_ = lean_ctor_get(v___x_705_, 1);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_716_ == 0)
{
v___x_709_ = v___x_705_;
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_711_ = 1;
v___x_712_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_703_, v_a_706_, v___x_711_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_712_);
v___x_714_ = v___x_709_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_a_707_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_dec(v_a_703_);
return v___x_705_;
}
}
else
{
lean_dec(v___x_699_);
return v___x_702_;
}
}
else
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Fmt_fmt(v_negTk_697_, v_a_690_, v_a_691_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_a_719_; lean_object* v___x_720_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
v_a_719_ = lean_ctor_get(v___x_717_, 1);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_717_, 2);
v___x_720_ = l_Lean_Fmt_fmt(v___x_699_, v_a_690_, v_a_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_731_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_a_722_ = lean_ctor_get(v___x_720_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_731_ == 0)
{
v___x_724_ = v___x_720_;
v_isShared_725_ = v_isSharedCheck_731_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_731_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_726_ = 0;
v___x_727_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_718_, v_a_721_, v___x_726_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_727_);
v___x_729_ = v___x_724_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_a_722_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
else
{
lean_dec(v_a_718_);
return v___x_720_;
}
}
else
{
lean_dec(v___x_699_);
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermNeg___boxed(lean_object* v_x_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Fmt_fmtTermNeg(v_x_732_, v_a_733_, v_a_734_);
lean_dec_ref(v_a_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1(){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_742_ = l_Lean_Fmt_fmtAttribute;
v___x_743_ = ((lean_object*)(l_Lean_Fmt_fmtTermNeg___closed__1));
v___x_744_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___closed__1));
v___x_745_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTermNeg___boxed), 3, 0);
v___x_746_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_742_, v___x_743_, v___x_744_, v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1___boxed(lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1();
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermInv(lean_object* v_x_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = ((lean_object*)(l_Lean_Fmt_fmtTermInv___closed__1));
lean_inc(v_x_752_);
v___x_756_ = l_Lean_Syntax_isOfKind(v_x_752_, v___x_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec(v_x_752_);
v___x_757_ = l_Lean_Fmt_Error_partialFormatter;
v___x_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v_a_754_);
return v___x_758_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = l_Lean_Syntax_getArg(v_x_752_, v___x_759_);
v___x_761_ = l_Lean_Fmt_fmt(v___x_760_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v_a_763_; lean_object* v___x_764_; lean_object* v_invTk_765_; lean_object* v___x_766_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
v_a_763_ = lean_ctor_get(v___x_761_, 1);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_761_, 2);
v___x_764_ = lean_unsigned_to_nat(1u);
v_invTk_765_ = l_Lean_Syntax_getArg(v_x_752_, v___x_764_);
lean_dec(v_x_752_);
v___x_766_ = l_Lean_Fmt_fmt(v_invTk_765_, v_a_753_, v_a_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_779_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_a_768_ = lean_ctor_get(v___x_766_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_779_ == 0)
{
v___x_770_ = v___x_766_;
v_isShared_771_ = v_isSharedCheck_779_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_779_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
uint8_t v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_772_ = 0;
v___x_773_ = l_Lean_Fmt_Layouts_postfixOperator(v_a_762_, v_a_767_, v___x_772_);
v___x_774_ = 0;
v___x_775_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_773_, v___x_774_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_775_);
v___x_777_ = v___x_770_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_a_768_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
lean_dec(v_a_762_);
return v___x_766_;
}
}
else
{
lean_dec(v_x_752_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermInv___boxed(lean_object* v_x_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Fmt_fmtTermInv(v_x_780_, v_a_781_, v_a_782_);
lean_dec_ref(v_a_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1(){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_790_ = l_Lean_Fmt_fmtAttribute;
v___x_791_ = ((lean_object*)(l_Lean_Fmt_fmtTermInv___closed__1));
v___x_792_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___closed__1));
v___x_793_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTermInv___boxed), 3, 0);
v___x_794_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_790_, v___x_791_, v___x_792_, v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1___boxed(lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1();
return v_res_796_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermMem___closed__2(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; lean_object* v___x_804_; 
v___x_801_ = lean_obj_once(&l_Lean_Fmt_fmtAddPrec___closed__3, &l_Lean_Fmt_fmtAddPrec___closed__3_once, _init_l_Lean_Fmt_fmtAddPrec___closed__3);
v___x_802_ = ((lean_object*)(l_Lean_Fmt_fmtTermMem___closed__1));
v___x_803_ = 0;
v___x_804_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_801_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*2, v___x_803_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*2 + 1, v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermMem(void){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = lean_obj_once(&l_Lean_Fmt_fmtTermMem___closed__2, &l_Lean_Fmt_fmtTermMem___closed__2_once, _init_l_Lean_Fmt_fmtTermMem___closed__2);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1(){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_815_ = l_Lean_Fmt_infixFmtAttribute;
v___x_816_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__1));
v___x_817_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___closed__3));
v___x_818_ = l_Lean_Fmt_fmtTermMem;
v___x_819_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_815_, v___x_816_, v___x_817_, v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1___boxed(lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1();
return v_res_821_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermNotMem(void){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = lean_obj_once(&l_Lean_Fmt_fmtTermMem___closed__2, &l_Lean_Fmt_fmtTermMem___closed__2_once, _init_l_Lean_Fmt_fmtTermMem___closed__2);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1(){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_832_ = l_Lean_Fmt_infixFmtAttribute;
v___x_833_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__1));
v___x_834_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___closed__3));
v___x_835_ = l_Lean_Fmt_fmtTermNotMem;
v___x_836_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_832_, v___x_833_, v___x_834_, v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1___boxed(lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1();
return v_res_838_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermLe___closed__2(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; 
v___x_844_ = lean_obj_once(&l_Lean_Fmt_fmtAddPrec___closed__3, &l_Lean_Fmt_fmtAddPrec___closed__3_once, _init_l_Lean_Fmt_fmtAddPrec___closed__3);
v___x_845_ = ((lean_object*)(l_Lean_Fmt_fmtTermLe___closed__1));
v___x_846_ = 0;
v___x_847_ = 1;
v___x_848_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_848_, 0, v___x_845_);
lean_ctor_set(v___x_848_, 1, v___x_844_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*2, v___x_847_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*2 + 1, v___x_846_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermLe(void){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_obj_once(&l_Lean_Fmt_fmtTermLe___closed__2, &l_Lean_Fmt_fmtTermLe___closed__2_once, _init_l_Lean_Fmt_fmtTermLe___closed__2);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1(){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_859_ = l_Lean_Fmt_infixFmtAttribute;
v___x_860_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__1));
v___x_861_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___closed__3));
v___x_862_ = l_Lean_Fmt_fmtTermLe;
v___x_863_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_859_, v___x_860_, v___x_861_, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1___boxed(lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1();
return v_res_865_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermGe(void){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = lean_obj_once(&l_Lean_Fmt_fmtTermLe___closed__2, &l_Lean_Fmt_fmtTermLe___closed__2_once, _init_l_Lean_Fmt_fmtTermLe___closed__2);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1(){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_876_ = l_Lean_Fmt_infixFmtAttribute;
v___x_877_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__1));
v___x_878_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___closed__3));
v___x_879_ = l_Lean_Fmt_fmtTermGe;
v___x_880_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_876_, v___x_877_, v___x_878_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1___boxed(lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1();
return v_res_882_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermAnd___closed__2(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; lean_object* v___x_891_; 
v___x_888_ = lean_obj_once(&l_Lean_Fmt_fmtAddPrec___closed__3, &l_Lean_Fmt_fmtAddPrec___closed__3_once, _init_l_Lean_Fmt_fmtAddPrec___closed__3);
v___x_889_ = ((lean_object*)(l_Lean_Fmt_fmtTermAnd___closed__1));
v___x_890_ = 0;
v___x_891_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_888_);
lean_ctor_set_uint8(v___x_891_, sizeof(void*)*2, v___x_890_);
lean_ctor_set_uint8(v___x_891_, sizeof(void*)*2 + 1, v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermAnd(void){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_obj_once(&l_Lean_Fmt_fmtTermAnd___closed__2, &l_Lean_Fmt_fmtTermAnd___closed__2_once, _init_l_Lean_Fmt_fmtTermAnd___closed__2);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1(){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_902_ = l_Lean_Fmt_infixFmtAttribute;
v___x_903_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__1));
v___x_904_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___closed__3));
v___x_905_ = l_Lean_Fmt_fmtTermAnd;
v___x_906_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_902_, v___x_903_, v___x_904_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1___boxed(lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1();
return v_res_908_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermOr___closed__2(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; 
v___x_914_ = lean_obj_once(&l_Lean_Fmt_fmtAddPrec___closed__3, &l_Lean_Fmt_fmtAddPrec___closed__3_once, _init_l_Lean_Fmt_fmtAddPrec___closed__3);
v___x_915_ = ((lean_object*)(l_Lean_Fmt_fmtTermOr___closed__1));
v___x_916_ = 0;
v___x_917_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_914_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*2, v___x_916_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*2 + 1, v___x_916_);
return v___x_917_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtTermOr(void){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = lean_obj_once(&l_Lean_Fmt_fmtTermOr___closed__2, &l_Lean_Fmt_fmtTermOr___closed__2_once, _init_l_Lean_Fmt_fmtTermOr___closed__2);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1(){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_928_ = l_Lean_Fmt_infixFmtAttribute;
v___x_929_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__1));
v___x_930_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___closed__3));
v___x_931_ = l_Lean_Fmt_fmtTermOr;
v___x_932_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_928_, v___x_929_, v___x_930_, v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1___boxed(lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1();
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0___redArg(lean_object* v_deconstruct_x3f_935_, lean_object* v_a_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_fst_939_; lean_object* v_snd_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_983_; 
v_fst_939_ = lean_ctor_get(v_a_936_, 0);
v_snd_940_ = lean_ctor_get(v_a_936_, 1);
v_isSharedCheck_983_ = !lean_is_exclusive(v_a_936_);
if (v_isSharedCheck_983_ == 0)
{
v___x_942_ = v_a_936_;
v_isShared_943_ = v_isSharedCheck_983_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_snd_940_);
lean_inc(v_fst_939_);
lean_dec(v_a_936_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_983_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; 
lean_inc_ref(v_deconstruct_x3f_935_);
lean_inc(v_fst_939_);
v___x_944_ = lean_apply_1(v_deconstruct_x3f_935_, v_fst_939_);
if (lean_obj_tag(v___x_944_) == 1)
{
lean_object* v_val_945_; lean_object* v_lhs_946_; lean_object* v_pipeTk_947_; lean_object* v_rhs_948_; lean_object* v___x_949_; 
lean_dec(v_fst_939_);
v_val_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v___x_944_, 1);
v_lhs_946_ = lean_ctor_get(v_val_945_, 0);
lean_inc(v_lhs_946_);
v_pipeTk_947_ = lean_ctor_get(v_val_945_, 1);
lean_inc(v_pipeTk_947_);
v_rhs_948_ = lean_ctor_get(v_val_945_, 2);
lean_inc(v_rhs_948_);
lean_dec(v_val_945_);
v___x_949_ = l_Lean_Fmt_fmt(v_lhs_946_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v_a_951_; lean_object* v___x_952_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
v_a_951_ = lean_ctor_get(v___x_949_, 1);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_949_, 2);
v___x_952_ = l_Lean_Fmt_fmt(v_pipeTk_947_, v___y_937_, v_a_951_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
v_a_954_ = lean_ctor_get(v___x_952_, 1);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_952_, 2);
v___x_955_ = lean_array_push(v_snd_940_, v_a_950_);
v___x_956_ = lean_array_push(v___x_955_, v_a_953_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_956_);
lean_ctor_set(v___x_942_, 0, v_rhs_948_);
v___x_958_ = v___x_942_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_rhs_948_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v___x_956_);
v___x_958_ = v_reuseFailAlloc_960_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
v_a_936_ = v___x_958_;
v___y_938_ = v_a_954_;
goto _start;
}
}
else
{
lean_object* v_a_961_; lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec(v_a_950_);
lean_dec(v_rhs_948_);
lean_del_object(v___x_942_);
lean_dec(v_snd_940_);
lean_dec_ref(v_deconstruct_x3f_935_);
v_a_961_ = lean_ctor_get(v___x_952_, 0);
v_a_962_ = lean_ctor_get(v___x_952_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_952_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_inc(v_a_961_);
lean_dec(v___x_952_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_961_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v_rhs_948_);
lean_dec(v_pipeTk_947_);
lean_del_object(v___x_942_);
lean_dec(v_snd_940_);
lean_dec_ref(v_deconstruct_x3f_935_);
v_a_970_ = lean_ctor_get(v___x_949_, 0);
v_a_971_ = lean_ctor_get(v___x_949_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_949_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_inc(v_a_970_);
lean_dec(v___x_949_);
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
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_970_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v___x_980_; 
lean_dec(v___x_944_);
lean_dec_ref(v_deconstruct_x3f_935_);
if (v_isShared_943_ == 0)
{
v___x_980_ = v___x_942_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_fst_939_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_snd_940_);
v___x_980_ = v_reuseFailAlloc_982_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; 
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___y_938_);
return v___x_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0___redArg___boxed(lean_object* v_deconstruct_x3f_984_, lean_object* v_a_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0___redArg(v_deconstruct_x3f_984_, v_a_985_, v___y_986_, v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPipeOperator(lean_object* v_deconstruct_x3f_991_, lean_object* v_stx_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_995_; lean_object* v_chain_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_995_ = lean_unsigned_to_nat(0u);
v_chain_996_ = ((lean_object*)(l_Lean_Fmt_fmtPipeOperator___closed__0));
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v_stx_992_);
lean_ctor_set(v___x_997_, 1, v_chain_996_);
v___x_998_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0___redArg(v_deconstruct_x3f_991_, v___x_997_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1024_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_a_1000_ = lean_ctor_get(v___x_998_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1002_ = v___x_998_;
v_isShared_1003_ = v_isSharedCheck_1024_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1024_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_fst_1004_; lean_object* v_snd_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_fst_1004_ = lean_ctor_get(v_a_999_, 0);
lean_inc(v_fst_1004_);
v_snd_1005_ = lean_ctor_get(v_a_999_, 1);
lean_inc(v_snd_1005_);
lean_dec(v_a_999_);
v___x_1006_ = lean_array_get_size(v_snd_1005_);
v___x_1007_ = lean_nat_dec_eq(v___x_1006_, v___x_995_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_del_object(v___x_1002_);
v___x_1008_ = l_Lean_Fmt_fmt(v_fst_1004_, v_a_993_, v_a_1000_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1019_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_a_1010_ = lean_ctor_get(v___x_1008_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1012_ = v___x_1008_;
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1014_ = lean_array_push(v_snd_1005_, v_a_1009_);
v___x_1015_ = l_Lean_Fmt_Layouts_pipeOperator(v___x_1014_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1015_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_a_1010_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
else
{
lean_dec(v_snd_1005_);
return v___x_1008_;
}
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
lean_dec(v_snd_1005_);
lean_dec(v_fst_1004_);
v___x_1020_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 1);
lean_ctor_set(v___x_1002_, 0, v___x_1020_);
v___x_1022_ = v___x_1002_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_a_1000_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1025_ = lean_ctor_get(v___x_998_, 0);
v_a_1026_ = lean_ctor_get(v___x_998_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_998_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_inc(v_a_1025_);
lean_dec(v___x_998_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1025_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPipeOperator___boxed(lean_object* v_deconstruct_x3f_1034_, lean_object* v_stx_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Fmt_fmtPipeOperator(v_deconstruct_x3f_1034_, v_stx_1035_, v_a_1036_, v_a_1037_);
lean_dec_ref(v_a_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0(lean_object* v_deconstruct_x3f_1039_, lean_object* v_inst_1040_, lean_object* v_a_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0___redArg(v_deconstruct_x3f_1039_, v_a_1041_, v___y_1042_, v___y_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0___boxed(lean_object* v_deconstruct_x3f_1045_, lean_object* v_inst_1046_, lean_object* v_a_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtPipeOperator_spec__0(v_deconstruct_x3f_1045_, v_inst_1046_, v_a_1047_, v___y_1048_, v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeLeft___lam__0(lean_object* v_x_1054_){
_start:
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_Fmt_fmtTermPipeLeft___lam__0___closed__1));
lean_inc(v_x_1054_);
v___x_1056_ = l_Lean_Syntax_isOfKind(v_x_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
lean_dec(v_x_1054_);
v___x_1057_ = lean_box(0);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v_pipeTk_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = l_Lean_Syntax_getArg(v_x_1054_, v___x_1058_);
v___x_1060_ = lean_unsigned_to_nat(1u);
v_pipeTk_1061_ = l_Lean_Syntax_getArg(v_x_1054_, v___x_1060_);
v___x_1062_ = lean_unsigned_to_nat(2u);
v___x_1063_ = l_Lean_Syntax_getArg(v_x_1054_, v___x_1062_);
lean_dec(v_x_1054_);
v___x_1064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1059_);
lean_ctor_set(v___x_1064_, 1, v_pipeTk_1061_);
lean_ctor_set(v___x_1064_, 2, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeLeft(lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___f_1070_; lean_object* v___x_1071_; 
v___f_1070_ = ((lean_object*)(l_Lean_Fmt_fmtTermPipeLeft___closed__0));
v___x_1071_ = l_Lean_Fmt_fmtPipeOperator(v___f_1070_, v_a_1067_, v_a_1068_, v_a_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeLeft___boxed(lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Fmt_fmtTermPipeLeft(v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec_ref(v_a_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1(){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1082_ = l_Lean_Fmt_fmtAttribute;
v___x_1083_ = ((lean_object*)(l_Lean_Fmt_fmtTermPipeLeft___lam__0___closed__1));
v___x_1084_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___closed__1));
v___x_1085_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTermPipeLeft___boxed), 3, 0);
v___x_1086_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1082_, v___x_1083_, v___x_1084_, v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1___boxed(lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1();
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeRight___lam__0(lean_object* v_x_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_Fmt_fmtTermPipeRight___lam__0___closed__1));
lean_inc(v_x_1092_);
v___x_1096_ = l_Lean_Syntax_isOfKind(v_x_1092_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Fmt_deconstructPipeProj(v_x_1092_, v___y_1093_, v___y_1094_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; lean_object* v_pipeTk_1099_; lean_object* v___x_1100_; 
v___x_1098_ = lean_unsigned_to_nat(1u);
v_pipeTk_1099_ = l_Lean_Syntax_getArg(v_x_1092_, v___x_1098_);
v___x_1100_ = l_Lean_Fmt_fmt(v_pipeTk_1099_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v_a_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
v_a_1102_ = lean_ctor_get(v___x_1100_, 1);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1100_, 2);
v___x_1103_ = lean_unsigned_to_nat(2u);
v___x_1104_ = l_Lean_Syntax_getArg(v_x_1092_, v___x_1103_);
v___x_1105_ = l_Lean_Fmt_fmt(v___x_1104_, v___y_1093_, v_a_1102_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1120_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_a_1107_ = lean_ctor_get(v___x_1105_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1109_ = v___x_1105_;
v_isShared_1110_ = v_isSharedCheck_1120_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1120_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = l_Lean_Syntax_getArg(v_x_1092_, v___x_1111_);
lean_dec(v_x_1092_);
v___x_1113_ = 2;
v___x_1114_ = l_Lean_Fmt_Layouts_prefixOperator(v_a_1101_, v_a_1106_, v___x_1113_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1112_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1116_);
v___x_1118_ = v___x_1109_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_a_1107_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v_a_1101_);
lean_dec(v_x_1092_);
v_a_1121_ = lean_ctor_get(v___x_1105_, 0);
v_a_1122_ = lean_ctor_get(v___x_1105_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1105_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_inc(v_a_1121_);
lean_dec(v___x_1105_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1121_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_x_1092_);
v_a_1130_ = lean_ctor_get(v___x_1100_, 0);
v_a_1131_ = lean_ctor_get(v___x_1100_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1100_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_inc(v_a_1130_);
lean_dec(v___x_1100_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1130_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeRight___lam__0___boxed(lean_object* v_x_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_Fmt_fmtTermPipeRight___lam__0(v_x_1139_, v___y_1140_, v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeRight(lean_object* v_stx_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___f_1147_; lean_object* v___x_1148_; 
v___f_1147_ = ((lean_object*)(l_Lean_Fmt_fmtTermPipeRight___closed__0));
v___x_1148_ = l_Lean_Fmt_fmtPipeProjLike(v_stx_1144_, v___f_1147_, v_a_1145_, v_a_1146_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermPipeRight___boxed(lean_object* v_stx_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Fmt_fmtTermPipeRight(v_stx_1149_, v_a_1150_, v_a_1151_);
lean_dec_ref(v_a_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1(){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1159_ = l_Lean_Fmt_fmtAttribute;
v___x_1160_ = ((lean_object*)(l_Lean_Fmt_fmtTermPipeRight___lam__0___closed__1));
v___x_1161_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___closed__1));
v___x_1162_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTermPipeRight___boxed), 3, 0);
v___x_1163_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1159_, v___x_1160_, v___x_1161_, v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1___boxed(lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1();
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermDollar___lam__0(lean_object* v_x_1169_){
_start:
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_Lean_Fmt_fmtTermDollar___lam__0___closed__1));
lean_inc(v_x_1169_);
v___x_1171_ = l_Lean_Syntax_isOfKind(v_x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
lean_dec(v_x_1169_);
v___x_1172_ = lean_box(0);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_dollarTk_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = l_Lean_Syntax_getArg(v_x_1169_, v___x_1173_);
v___x_1175_ = lean_unsigned_to_nat(1u);
v_dollarTk_1176_ = l_Lean_Syntax_getArg(v_x_1169_, v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(2u);
v___x_1178_ = l_Lean_Syntax_getArg(v_x_1169_, v___x_1177_);
lean_dec(v_x_1169_);
v___x_1179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1174_);
lean_ctor_set(v___x_1179_, 1, v_dollarTk_1176_);
lean_ctor_set(v___x_1179_, 2, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermDollar(lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v___f_1185_; lean_object* v___x_1186_; 
v___f_1185_ = ((lean_object*)(l_Lean_Fmt_fmtTermDollar___closed__0));
v___x_1186_ = l_Lean_Fmt_fmtPipeOperator(v___f_1185_, v_a_1182_, v_a_1183_, v_a_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTermDollar___boxed(lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Fmt_fmtTermDollar(v_a_1187_, v_a_1188_, v_a_1189_);
lean_dec_ref(v_a_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1(){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1197_ = l_Lean_Fmt_fmtAttribute;
v___x_1198_ = ((lean_object*)(l_Lean_Fmt_fmtTermDollar___lam__0___closed__1));
v___x_1199_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___closed__1));
v___x_1200_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTermDollar___boxed), 3, 0);
v___x_1201_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1197_, v___x_1198_, v___x_1199_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1___boxed(lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1();
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawNatLit(lean_object* v_x_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = ((lean_object*)(l_Lean_Fmt_fmtRawNatLit___closed__1));
lean_inc(v_x_1207_);
v___x_1211_ = l_Lean_Syntax_isOfKind(v_x_1207_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec(v_x_1207_);
v___x_1212_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v_a_1209_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1214_ = lean_unsigned_to_nat(1u);
v___x_1215_ = l_Lean_Syntax_getArg(v_x_1207_, v___x_1214_);
v___x_1216_ = ((lean_object*)(l_Lean_Fmt_fmtTermNeg___closed__3));
lean_inc(v___x_1215_);
v___x_1217_ = l_Lean_Syntax_isOfKind(v___x_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v___x_1215_);
lean_dec(v_x_1207_);
v___x_1218_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v_a_1209_);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; lean_object* v_natLitTk_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1220_ = lean_unsigned_to_nat(0u);
v_natLitTk_1221_ = l_Lean_Syntax_getArg(v_x_1207_, v___x_1220_);
lean_dec(v_x_1207_);
v___x_1222_ = lean_unsigned_to_nat(2u);
v___x_1223_ = lean_mk_empty_array_with_capacity(v___x_1222_);
v___x_1224_ = lean_array_push(v___x_1223_, v_natLitTk_1221_);
v___x_1225_ = lean_array_push(v___x_1224_, v___x_1215_);
v___x_1226_ = l_Lean_Fmt_fmtAppLike(v___x_1225_, v_a_1208_, v_a_1209_);
return v___x_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawNatLit___boxed(lean_object* v_x_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Fmt_fmtRawNatLit(v_x_1227_, v_a_1228_, v_a_1229_);
lean_dec_ref(v_a_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1(){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1237_ = l_Lean_Fmt_fmtAttribute;
v___x_1238_ = ((lean_object*)(l_Lean_Fmt_fmtRawNatLit___closed__1));
v___x_1239_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___closed__1));
v___x_1240_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRawNatLit___boxed), 3, 0);
v___x_1241_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1237_, v___x_1238_, v___x_1239_, v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1___boxed(lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1();
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderIdent(lean_object* v_x_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = ((lean_object*)(l_Lean_Fmt_fmtBinderIdent___closed__1));
lean_inc(v_x_1258_);
v___x_1262_ = l_Lean_Syntax_isOfKind(v_x_1258_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec(v_x_1258_);
v___x_1263_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v_a_1260_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = l_Lean_Syntax_getArg(v_x_1258_, v___x_1265_);
lean_dec(v_x_1258_);
v___x_1267_ = ((lean_object*)(l_Lean_Fmt_fmtBinderIdent___closed__4));
lean_inc(v___x_1266_);
v___x_1268_ = l_Lean_Syntax_isOfKind(v___x_1266_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_Fmt_fmtBinderIdent___closed__6));
lean_inc(v___x_1266_);
v___x_1270_ = l_Lean_Syntax_isOfKind(v___x_1266_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec(v___x_1266_);
v___x_1271_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v_a_1260_);
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_Fmt_fmt(v___x_1266_, v_a_1259_, v_a_1260_);
return v___x_1273_;
}
}
else
{
lean_object* v_holeTk_1274_; lean_object* v___x_1275_; 
v_holeTk_1274_ = l_Lean_Syntax_getArg(v___x_1266_, v___x_1265_);
lean_dec(v___x_1266_);
v___x_1275_ = l_Lean_Fmt_fmt(v_holeTk_1274_, v_a_1259_, v_a_1260_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderIdent___boxed(lean_object* v_x_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Fmt_fmtBinderIdent(v_x_1276_, v_a_1277_, v_a_1278_);
lean_dec_ref(v_a_1277_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1(){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1286_ = l_Lean_Fmt_fmtAttribute;
v___x_1287_ = ((lean_object*)(l_Lean_Fmt_fmtBinderIdent___closed__1));
v___x_1288_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___closed__1));
v___x_1289_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBinderIdent___boxed), 3, 0);
v___x_1290_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1286_, v___x_1287_, v___x_1288_, v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1___boxed(lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1();
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCaseArg(lean_object* v_x_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_Fmt_fmtCaseArg___closed__2));
lean_inc(v_x_1300_);
v___x_1304_ = l_Lean_Syntax_isOfKind(v_x_1300_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec(v_x_1300_);
v___x_1305_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v_a_1302_);
return v___x_1306_;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = l_Lean_Syntax_getArg(v_x_1300_, v___x_1307_);
v___x_1309_ = ((lean_object*)(l_Lean_Fmt_fmtBinderIdent___closed__1));
lean_inc(v___x_1308_);
v___x_1310_ = l_Lean_Syntax_isOfKind(v___x_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_dec(v___x_1308_);
lean_dec(v_x_1300_);
v___x_1311_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v_a_1302_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_Fmt_fmt(v___x_1308_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_ids_1318_; lean_object* v___x_1319_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
v_a_1315_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1313_, 2);
v___x_1316_ = lean_unsigned_to_nat(1u);
v___x_1317_ = l_Lean_Syntax_getArg(v_x_1300_, v___x_1316_);
lean_dec(v_x_1300_);
v_ids_1318_ = l_Lean_Syntax_getArgs(v___x_1317_);
lean_dec(v___x_1317_);
v___x_1319_ = l_Lean_Fmt_fmtArray___redArg(v_ids_1318_, v_a_1301_, v_a_1315_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1334_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_a_1321_ = lean_ctor_get(v___x_1319_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1323_ = v___x_1319_;
v_isShared_1324_ = v_isSharedCheck_1334_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1334_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1325_ = lean_mk_empty_array_with_capacity(v___x_1316_);
v___x_1326_ = lean_array_push(v___x_1325_, v_a_1314_);
v___x_1327_ = l_Array_append___redArg(v___x_1326_, v_a_1320_);
lean_dec(v_a_1320_);
v___x_1328_ = 0;
v___x_1329_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1329_, 0, v___x_1310_);
lean_ctor_set_uint8(v___x_1329_, 1, v___x_1328_);
lean_ctor_set_uint8(v___x_1329_, 2, v___x_1328_);
lean_ctor_set_uint8(v___x_1329_, 3, v___x_1328_);
v___x_1330_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_1327_, v___x_1329_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1330_);
v___x_1332_ = v___x_1323_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_a_1321_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v_a_1314_);
v_a_1335_ = lean_ctor_get(v___x_1319_, 0);
v_a_1336_ = lean_ctor_get(v___x_1319_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1319_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_inc(v_a_1335_);
lean_dec(v___x_1319_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1335_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_dec(v_x_1300_);
return v___x_1313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCaseArg___boxed(lean_object* v_x_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_Fmt_fmtCaseArg(v_x_1344_, v_a_1345_, v_a_1346_);
lean_dec_ref(v_a_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1(){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1354_ = l_Lean_Fmt_fmtAttribute;
v___x_1355_ = ((lean_object*)(l_Lean_Fmt_fmtCaseArg___closed__2));
v___x_1356_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___closed__1));
v___x_1357_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCaseArg___boxed), 3, 0);
v___x_1358_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1354_, v___x_1355_, v___x_1356_, v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1___boxed(lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1();
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfThenElse(lean_object* v_x_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = ((lean_object*)(l_Lean_Fmt_fmtIfThenElse___closed__1));
lean_inc(v_x_1366_);
v___x_1370_ = l_Lean_Syntax_isOfKind(v_x_1366_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec(v_x_1366_);
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v_a_1368_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = l_Lean_Syntax_getArg(v_x_1366_, v___x_1373_);
v___x_1375_ = l_Lean_Fmt_fmt(v___x_1374_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1399_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_a_1377_ = lean_ctor_get(v___x_1375_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1379_ = v___x_1375_;
v_isShared_1380_ = v_isSharedCheck_1399_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1399_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v_ifTk_1382_; lean_object* v___x_1383_; lean_object* v_thenTk_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v_elseTk_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v_ifTk_1382_ = l_Lean_Syntax_getArg(v_x_1366_, v___x_1381_);
v___x_1383_ = lean_unsigned_to_nat(2u);
v_thenTk_1384_ = l_Lean_Syntax_getArg(v_x_1366_, v___x_1383_);
v___x_1385_ = lean_unsigned_to_nat(3u);
v___x_1386_ = l_Lean_Syntax_getArg(v_x_1366_, v___x_1385_);
v___x_1387_ = lean_unsigned_to_nat(4u);
v_elseTk_1388_ = l_Lean_Syntax_getArg(v_x_1366_, v___x_1387_);
v___x_1389_ = lean_unsigned_to_nat(5u);
v___x_1390_ = l_Lean_Syntax_getArg(v_x_1366_, v___x_1389_);
lean_dec(v_x_1366_);
v___x_1391_ = ((lean_object*)(l_Lean_Fmt_fmtIfThenElse___closed__2));
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v_elseTk_1388_);
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1390_);
v___x_1394_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1394_, 0, v_ifTk_1382_);
lean_ctor_set(v___x_1394_, 1, v_a_1376_);
lean_ctor_set(v___x_1394_, 2, v_thenTk_1384_);
lean_ctor_set(v___x_1394_, 3, v___x_1386_);
lean_ctor_set(v___x_1394_, 4, v___x_1391_);
lean_ctor_set(v___x_1394_, 5, v___x_1392_);
lean_ctor_set(v___x_1394_, 6, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1395_);
v___x_1397_ = v___x_1379_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_a_1377_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec(v_x_1366_);
v_a_1400_ = lean_ctor_get(v___x_1375_, 0);
v_a_1401_ = lean_ctor_get(v___x_1375_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1375_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_inc(v_a_1400_);
lean_dec(v___x_1375_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1400_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfThenElse___boxed(lean_object* v_x_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Fmt_fmtIfThenElse(v_x_1409_, v_a_1410_, v_a_1411_);
lean_dec_ref(v_a_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1(){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1419_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_1420_ = ((lean_object*)(l_Lean_Fmt_fmtIfThenElse___closed__1));
v___x_1421_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___closed__1));
v___x_1422_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtIfThenElse___boxed), 3, 0);
v___x_1423_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1419_, v___x_1420_, v___x_1421_, v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1___boxed(lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1();
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDepIfThenElse(lean_object* v_x_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = ((lean_object*)(l_Lean_Fmt_fmtDepIfThenElse___closed__1));
lean_inc(v_x_1429_);
v___x_1433_ = l_Lean_Syntax_isOfKind(v_x_1429_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec(v_x_1429_);
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
lean_ctor_set(v___x_1435_, 1, v_a_1431_);
return v___x_1435_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = l_Lean_Syntax_getArg(v_x_1429_, v___x_1436_);
v___x_1438_ = ((lean_object*)(l_Lean_Fmt_fmtBinderIdent___closed__1));
lean_inc(v___x_1437_);
v___x_1439_ = l_Lean_Syntax_isOfKind(v___x_1437_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec(v___x_1437_);
lean_dec(v_x_1429_);
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v_a_1431_);
return v___x_1441_;
}
else
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Fmt_fmt(v___x_1437_, v_a_1430_, v_a_1431_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v_a_1444_; lean_object* v___x_1445_; lean_object* v_colonTk_1446_; lean_object* v___x_1447_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
v_a_1444_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1442_, 2);
v___x_1445_ = lean_unsigned_to_nat(2u);
v_colonTk_1446_ = l_Lean_Syntax_getArg(v_x_1429_, v___x_1445_);
v___x_1447_ = l_Lean_Fmt_fmt(v_colonTk_1446_, v_a_1430_, v_a_1444_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v_a_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
v_a_1449_ = lean_ctor_get(v___x_1447_, 1);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1447_, 2);
v___x_1450_ = lean_unsigned_to_nat(3u);
v___x_1451_ = l_Lean_Syntax_getArg(v_x_1429_, v___x_1450_);
v___x_1452_ = l_Lean_Fmt_fmt(v___x_1451_, v_a_1430_, v_a_1449_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1479_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_a_1454_ = lean_ctor_get(v___x_1452_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1456_ = v___x_1452_;
v_isShared_1457_ = v_isSharedCheck_1479_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1479_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v_ifTk_1459_; lean_object* v___x_1460_; lean_object* v_thenTk_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v_elseTk_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v_ifTk_1459_ = l_Lean_Syntax_getArg(v_x_1429_, v___x_1458_);
v___x_1460_ = lean_unsigned_to_nat(4u);
v_thenTk_1461_ = l_Lean_Syntax_getArg(v_x_1429_, v___x_1460_);
v___x_1462_ = lean_unsigned_to_nat(5u);
v___x_1463_ = l_Lean_Syntax_getArg(v_x_1429_, v___x_1462_);
v___x_1464_ = lean_unsigned_to_nat(6u);
v_elseTk_1465_ = l_Lean_Syntax_getArg(v_x_1429_, v___x_1464_);
v___x_1466_ = lean_unsigned_to_nat(7u);
v___x_1467_ = l_Lean_Syntax_getArg(v_x_1429_, v___x_1466_);
lean_dec(v_x_1429_);
v___x_1468_ = 0;
v___x_1469_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1469_, 0, v___x_1439_);
lean_ctor_set_uint8(v___x_1469_, 1, v___x_1468_);
lean_ctor_set_uint8(v___x_1469_, 2, v___x_1439_);
lean_ctor_set_uint8(v___x_1469_, 3, v___x_1439_);
v___x_1470_ = l_Lean_Fmt_Layouts_typeAscription(v_a_1443_, v_a_1448_, v_a_1453_, v___x_1469_);
lean_dec_ref_known(v___x_1469_, 0);
v___x_1471_ = ((lean_object*)(l_Lean_Fmt_fmtIfThenElse___closed__2));
v___x_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_elseTk_1465_);
v___x_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1467_);
v___x_1474_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1474_, 0, v_ifTk_1459_);
lean_ctor_set(v___x_1474_, 1, v___x_1470_);
lean_ctor_set(v___x_1474_, 2, v_thenTk_1461_);
lean_ctor_set(v___x_1474_, 3, v___x_1463_);
lean_ctor_set(v___x_1474_, 4, v___x_1471_);
lean_ctor_set(v___x_1474_, 5, v___x_1472_);
lean_ctor_set(v___x_1474_, 6, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1475_);
v___x_1477_ = v___x_1456_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_a_1454_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v_a_1448_);
lean_dec(v_a_1443_);
lean_dec(v_x_1429_);
v_a_1480_ = lean_ctor_get(v___x_1452_, 0);
v_a_1481_ = lean_ctor_get(v___x_1452_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1452_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_inc(v_a_1480_);
lean_dec(v___x_1452_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1480_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_a_1443_);
lean_dec(v_x_1429_);
v_a_1489_ = lean_ctor_get(v___x_1447_, 0);
v_a_1490_ = lean_ctor_get(v___x_1447_, 1);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1447_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_inc(v_a_1489_);
lean_dec(v___x_1447_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1489_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_x_1429_);
v_a_1498_ = lean_ctor_get(v___x_1442_, 0);
v_a_1499_ = lean_ctor_get(v___x_1442_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1442_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_inc(v_a_1498_);
lean_dec(v___x_1442_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1498_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDepIfThenElse___boxed(lean_object* v_x_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Fmt_fmtDepIfThenElse(v_x_1507_, v_a_1508_, v_a_1509_);
lean_dec_ref(v_a_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1(){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1517_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_1518_ = ((lean_object*)(l_Lean_Fmt_fmtDepIfThenElse___closed__1));
v___x_1519_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___closed__1));
v___x_1520_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDepIfThenElse___boxed), 3, 0);
v___x_1521_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1517_, v___x_1518_, v___x_1519_, v___x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1___boxed(lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1();
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfLet___lam__0(lean_object* v___y_1524_){
_start:
{
lean_inc_ref(v___y_1524_);
return v___y_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfLet___lam__0___boxed(lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_Fmt_fmtIfLet___lam__0(v___y_1525_);
lean_dec_ref(v___y_1525_);
return v_res_1526_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtIfLet___closed__3(void){
_start:
{
lean_object* v___f_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___f_1531_ = ((lean_object*)(l_Lean_Fmt_fmtIfLet___closed__2));
v___x_1532_ = l_Lean_Fmt_TaggedDoc_space;
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___f_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfLet(lean_object* v_x_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_Lean_Fmt_fmtIfLet___closed__1));
lean_inc(v_x_1534_);
v___x_1538_ = l_Lean_Syntax_isOfKind(v_x_1534_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec(v_x_1534_);
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v_a_1536_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; lean_object* v_letTk_1542_; lean_object* v___x_1543_; 
v___x_1541_ = lean_unsigned_to_nat(1u);
v_letTk_1542_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1541_);
v___x_1543_ = l_Lean_Fmt_fmt(v_letTk_1542_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v_a_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
v_a_1545_ = lean_ctor_get(v___x_1543_, 1);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1543_, 2);
v___x_1546_ = lean_unsigned_to_nat(2u);
v___x_1547_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1546_);
v___x_1548_ = l_Lean_Fmt_fmt(v___x_1547_, v_a_1535_, v_a_1545_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v_a_1550_; lean_object* v___x_1551_; lean_object* v_colonEqTk_1552_; lean_object* v___x_1553_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
v_a_1550_ = lean_ctor_get(v___x_1548_, 1);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1548_, 2);
v___x_1551_ = lean_unsigned_to_nat(3u);
v_colonEqTk_1552_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1551_);
v___x_1553_ = l_Lean_Fmt_fmt(v_colonEqTk_1552_, v_a_1535_, v_a_1550_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
v_a_1555_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1553_, 2);
v___x_1556_ = lean_unsigned_to_nat(4u);
v___x_1557_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1556_);
v___x_1558_ = l_Lean_Fmt_fmt(v___x_1557_, v_a_1535_, v_a_1555_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1594_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_a_1560_ = lean_ctor_get(v___x_1558_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1562_ = v___x_1558_;
v_isShared_1563_ = v_isSharedCheck_1594_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1594_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v_ifTk_1565_; lean_object* v___x_1566_; lean_object* v_thenTk_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v_elseTk_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1564_ = lean_unsigned_to_nat(0u);
v_ifTk_1565_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1564_);
v___x_1566_ = lean_unsigned_to_nat(5u);
v_thenTk_1567_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1566_);
v___x_1568_ = lean_unsigned_to_nat(6u);
v___x_1569_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1568_);
v___x_1570_ = lean_unsigned_to_nat(7u);
v_elseTk_1571_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1570_);
v___x_1572_ = lean_unsigned_to_nat(8u);
v___x_1573_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1572_);
lean_dec(v_x_1534_);
v___x_1574_ = 0;
v___x_1575_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_1549_, v_a_1554_, v_a_1559_, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_a_1544_);
v___x_1577_ = lean_obj_once(&l_Lean_Fmt_fmtIfLet___closed__3, &l_Lean_Fmt_fmtIfLet___closed__3_once, _init_l_Lean_Fmt_fmtIfLet___closed__3);
v___x_1578_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1576_, v___x_1577_);
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1575_);
v___x_1581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
lean_ctor_set(v___x_1581_, 2, v___x_1579_);
v___x_1582_ = lean_mk_empty_array_with_capacity(v___x_1546_);
v___x_1583_ = lean_array_push(v___x_1582_, v___x_1578_);
v___x_1584_ = lean_array_push(v___x_1583_, v___x_1581_);
v___x_1585_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1584_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Lean_Fmt_fmtIfThenElse___closed__2));
v___x_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_elseTk_1571_);
v___x_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1573_);
v___x_1589_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1589_, 0, v_ifTk_1565_);
lean_ctor_set(v___x_1589_, 1, v___x_1585_);
lean_ctor_set(v___x_1589_, 2, v_thenTk_1567_);
lean_ctor_set(v___x_1589_, 3, v___x_1569_);
lean_ctor_set(v___x_1589_, 4, v___x_1586_);
lean_ctor_set(v___x_1589_, 5, v___x_1587_);
lean_ctor_set(v___x_1589_, 6, v___x_1588_);
v___x_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1590_);
v___x_1592_ = v___x_1562_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1560_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_a_1554_);
lean_dec(v_a_1549_);
lean_dec(v_a_1544_);
lean_dec(v_x_1534_);
v_a_1595_ = lean_ctor_get(v___x_1558_, 0);
v_a_1596_ = lean_ctor_get(v___x_1558_, 1);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1558_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_inc(v_a_1595_);
lean_dec(v___x_1558_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1595_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_a_1549_);
lean_dec(v_a_1544_);
lean_dec(v_x_1534_);
v_a_1604_ = lean_ctor_get(v___x_1553_, 0);
v_a_1605_ = lean_ctor_get(v___x_1553_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1553_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_inc(v_a_1604_);
lean_dec(v___x_1553_);
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
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1604_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec(v_a_1544_);
lean_dec(v_x_1534_);
v_a_1613_ = lean_ctor_get(v___x_1548_, 0);
v_a_1614_ = lean_ctor_get(v___x_1548_, 1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1548_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_inc(v_a_1613_);
lean_dec(v___x_1548_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1613_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_x_1534_);
v_a_1622_ = lean_ctor_get(v___x_1543_, 0);
v_a_1623_ = lean_ctor_get(v___x_1543_, 1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1543_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_inc(v_a_1622_);
lean_dec(v___x_1543_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1622_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIfLet___boxed(lean_object* v_x_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Fmt_fmtIfLet(v_x_1631_, v_a_1632_, v_a_1633_);
lean_dec_ref(v_a_1632_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1(){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1641_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_1642_ = ((lean_object*)(l_Lean_Fmt_fmtIfLet___closed__1));
v___x_1643_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___closed__1));
v___x_1644_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtIfLet___boxed), 3, 0);
v___x_1645_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1641_, v___x_1642_, v___x_1643_, v___x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1___boxed(lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1();
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBoolIfThenElse(lean_object* v_x_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lean_Fmt_fmtBoolIfThenElse___closed__1));
lean_inc(v_x_1651_);
v___x_1655_ = l_Lean_Syntax_isOfKind(v_x_1651_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec(v_x_1651_);
v___x_1656_ = lean_box(0);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v_a_1653_);
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = l_Lean_Syntax_getArg(v_x_1651_, v___x_1658_);
v___x_1660_ = l_Lean_Fmt_fmt(v___x_1659_, v_a_1652_, v_a_1653_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1684_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_a_1662_ = lean_ctor_get(v___x_1660_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1664_ = v___x_1660_;
v_isShared_1665_ = v_isSharedCheck_1684_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1684_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v_ifTk_1667_; lean_object* v___x_1668_; lean_object* v_thenTk_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v_elseTk_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1666_ = lean_unsigned_to_nat(0u);
v_ifTk_1667_ = l_Lean_Syntax_getArg(v_x_1651_, v___x_1666_);
v___x_1668_ = lean_unsigned_to_nat(2u);
v_thenTk_1669_ = l_Lean_Syntax_getArg(v_x_1651_, v___x_1668_);
v___x_1670_ = lean_unsigned_to_nat(3u);
v___x_1671_ = l_Lean_Syntax_getArg(v_x_1651_, v___x_1670_);
v___x_1672_ = lean_unsigned_to_nat(4u);
v_elseTk_1673_ = l_Lean_Syntax_getArg(v_x_1651_, v___x_1672_);
v___x_1674_ = lean_unsigned_to_nat(5u);
v___x_1675_ = l_Lean_Syntax_getArg(v_x_1651_, v___x_1674_);
lean_dec(v_x_1651_);
v___x_1676_ = ((lean_object*)(l_Lean_Fmt_fmtIfThenElse___closed__2));
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_elseTk_1673_);
v___x_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1675_);
v___x_1679_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1679_, 0, v_ifTk_1667_);
lean_ctor_set(v___x_1679_, 1, v_a_1661_);
lean_ctor_set(v___x_1679_, 2, v_thenTk_1669_);
lean_ctor_set(v___x_1679_, 3, v___x_1671_);
lean_ctor_set(v___x_1679_, 4, v___x_1676_);
lean_ctor_set(v___x_1679_, 5, v___x_1677_);
lean_ctor_set(v___x_1679_, 6, v___x_1678_);
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1680_);
v___x_1682_ = v___x_1664_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_a_1662_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_x_1651_);
v_a_1685_ = lean_ctor_get(v___x_1660_, 0);
v_a_1686_ = lean_ctor_get(v___x_1660_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1660_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_inc(v_a_1685_);
lean_dec(v___x_1660_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1685_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBoolIfThenElse___boxed(lean_object* v_x_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_Fmt_fmtBoolIfThenElse(v_x_1694_, v_a_1695_, v_a_1696_);
lean_dec_ref(v_a_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1(){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1704_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_1705_ = ((lean_object*)(l_Lean_Fmt_fmtBoolIfThenElse___closed__1));
v___x_1706_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___closed__1));
v___x_1707_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBoolIfThenElse___boxed), 3, 0);
v___x_1708_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1704_, v___x_1705_, v___x_1706_, v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1___boxed(lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1();
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubtype(lean_object* v_x_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1717_ = ((lean_object*)(l_Lean_Fmt_fmtSubtype___closed__1));
lean_inc(v_x_1714_);
v___x_1718_ = l_Lean_Syntax_isOfKind(v_x_1714_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec(v_x_1714_);
v___x_1719_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_ctor_set(v___x_1720_, 1, v_a_1716_);
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; 
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = l_Lean_Syntax_getArg(v_x_1714_, v___x_1721_);
v___x_1723_ = ((lean_object*)(l_Lean_Fmt_fmtBinderIdent___closed__6));
lean_inc(v___x_1722_);
v___x_1724_ = l_Lean_Syntax_isOfKind(v___x_1722_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v___x_1722_);
lean_dec(v_x_1714_);
v___x_1759_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v_a_1716_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; lean_object* v_lbTk_1762_; lean_object* v_colonTk_x3f_1764_; lean_object* v_type_x3f_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1761_ = lean_unsigned_to_nat(0u);
v_lbTk_1762_ = l_Lean_Syntax_getArg(v_x_1714_, v___x_1761_);
v___x_1792_ = lean_unsigned_to_nat(2u);
v___x_1793_ = l_Lean_Syntax_getArg(v_x_1714_, v___x_1792_);
v___x_1794_ = l_Lean_Syntax_isNone(v___x_1793_);
if (v___x_1794_ == 0)
{
uint8_t v___x_1795_; 
lean_inc(v___x_1793_);
v___x_1795_ = l_Lean_Syntax_matchesNull(v___x_1793_, v___x_1792_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v___x_1793_);
lean_dec(v_lbTk_1762_);
lean_dec(v___x_1722_);
lean_dec(v_x_1714_);
v___x_1796_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v_a_1716_);
return v___x_1797_;
}
else
{
lean_object* v_colonTk_x3f_1798_; lean_object* v_type_x3f_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_colonTk_x3f_1798_ = l_Lean_Syntax_getArg(v___x_1793_, v___x_1761_);
v_type_x3f_1799_ = l_Lean_Syntax_getArg(v___x_1793_, v___x_1721_);
lean_dec(v___x_1793_);
v___x_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1800_, 0, v_colonTk_x3f_1798_);
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_type_x3f_1799_);
v_colonTk_x3f_1764_ = v___x_1800_;
v_type_x3f_1765_ = v___x_1801_;
v___y_1766_ = v_a_1715_;
v___y_1767_ = v_a_1716_;
goto v___jp_1763_;
}
}
else
{
lean_object* v___x_1802_; 
lean_dec(v___x_1793_);
v___x_1802_ = lean_box(0);
v_colonTk_x3f_1764_ = v___x_1802_;
v_type_x3f_1765_ = v___x_1802_;
v___y_1766_ = v_a_1715_;
v___y_1767_ = v_a_1716_;
goto v___jp_1763_;
}
v___jp_1763_:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Fmt_fmt(v_lbTk_1762_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v_a_1770_; lean_object* v___x_1771_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
v_a_1770_ = lean_ctor_get(v___x_1768_, 1);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1768_, 2);
v___x_1771_ = l_Lean_Fmt_fmt(v___x_1722_, v___y_1766_, v_a_1770_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
v_a_1773_ = lean_ctor_get(v___x_1771_, 1);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1771_, 2);
v___x_1774_ = l_Lean_Fmt_fmt_x3f(v_colonTk_x3f_1764_, v___y_1766_, v_a_1773_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v_a_1776_; lean_object* v___x_1777_; lean_object* v_slashTk_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_rbTk_1782_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
v_a_1776_ = lean_ctor_get(v___x_1774_, 1);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1774_, 2);
v___x_1777_ = lean_unsigned_to_nat(3u);
v_slashTk_1778_ = l_Lean_Syntax_getArg(v_x_1714_, v___x_1777_);
v___x_1779_ = lean_unsigned_to_nat(4u);
v___x_1780_ = l_Lean_Syntax_getArg(v_x_1714_, v___x_1779_);
v___x_1781_ = lean_unsigned_to_nat(5u);
v_rbTk_1782_ = l_Lean_Syntax_getArg(v_x_1714_, v___x_1781_);
lean_dec(v_x_1714_);
if (lean_obj_tag(v_type_x3f_1765_) == 0)
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_box(0);
v___y_1726_ = v___x_1780_;
v___y_1727_ = v_slashTk_1778_;
v___y_1728_ = v_rbTk_1782_;
v___y_1729_ = v_a_1769_;
v___y_1730_ = v_a_1772_;
v___y_1731_ = v_a_1775_;
v___y_1732_ = v___y_1766_;
v___y_1733_ = v_a_1776_;
v___y_1734_ = v___x_1783_;
goto v___jp_1725_;
}
else
{
lean_object* v_val_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_val_1784_ = lean_ctor_get(v_type_x3f_1765_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_type_x3f_1765_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v_type_x3f_1765_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_val_1784_);
lean_dec(v_type_x3f_1765_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_val_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
v___y_1726_ = v___x_1780_;
v___y_1727_ = v_slashTk_1778_;
v___y_1728_ = v_rbTk_1782_;
v___y_1729_ = v_a_1769_;
v___y_1730_ = v_a_1772_;
v___y_1731_ = v_a_1775_;
v___y_1732_ = v___y_1766_;
v___y_1733_ = v_a_1776_;
v___y_1734_ = v___x_1789_;
goto v___jp_1725_;
}
}
}
}
else
{
lean_dec(v_a_1772_);
lean_dec(v_a_1769_);
lean_dec(v_type_x3f_1765_);
lean_dec(v_x_1714_);
return v___x_1774_;
}
}
else
{
lean_dec(v_a_1769_);
lean_dec(v_type_x3f_1765_);
lean_dec(v_colonTk_x3f_1764_);
lean_dec(v_x_1714_);
return v___x_1771_;
}
}
else
{
lean_dec(v_type_x3f_1765_);
lean_dec(v_colonTk_x3f_1764_);
lean_dec(v___x_1722_);
lean_dec(v_x_1714_);
return v___x_1768_;
}
}
}
v___jp_1725_:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Fmt_fmt_x3f(v___y_1734_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v_a_1737_; lean_object* v___x_1738_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
v_a_1737_ = lean_ctor_get(v___x_1735_, 1);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1735_, 2);
v___x_1738_ = l_Lean_Fmt_fmt(v___y_1727_, v___y_1732_, v_a_1737_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v_a_1740_; lean_object* v___x_1741_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
v_a_1740_ = lean_ctor_get(v___x_1738_, 1);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1738_, 2);
v___x_1741_ = l_Lean_Fmt_fmt(v___y_1726_, v___y_1732_, v_a_1740_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v_a_1743_; lean_object* v___x_1744_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
v_a_1743_ = lean_ctor_get(v___x_1741_, 1);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1741_, 2);
v___x_1744_ = l_Lean_Fmt_fmt(v___y_1728_, v___y_1732_, v_a_1743_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1758_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_a_1746_ = lean_ctor_get(v___x_1744_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1748_ = v___x_1744_;
v_isShared_1749_ = v_isSharedCheck_1758_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1758_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1750_ = 0;
v___x_1751_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_1751_, 0, v___x_1724_);
lean_ctor_set_uint8(v___x_1751_, 1, v___x_1750_);
lean_ctor_set_uint8(v___x_1751_, 2, v___x_1724_);
lean_ctor_set_uint8(v___x_1751_, 3, v___x_1724_);
v___x_1752_ = l_Lean_Fmt_Layouts_typeAscription(v___y_1730_, v___y_1731_, v_a_1736_, v___x_1751_);
lean_dec_ref_known(v___x_1751_, 0);
v___x_1753_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1753_, 0, v___x_1750_);
lean_ctor_set_uint8(v___x_1753_, 1, v___x_1724_);
v___x_1754_ = l_Lean_Fmt_Layouts_subtype(v___y_1729_, v___x_1752_, v_a_1739_, v_a_1742_, v_a_1745_, v___x_1753_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1754_);
v___x_1756_ = v___x_1748_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_a_1746_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
else
{
lean_dec(v_a_1742_);
lean_dec(v_a_1739_);
lean_dec(v_a_1736_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v___x_1744_;
}
}
else
{
lean_dec(v_a_1739_);
lean_dec(v_a_1736_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
return v___x_1741_;
}
}
else
{
lean_dec(v_a_1736_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec(v___y_1726_);
return v___x_1738_;
}
}
else
{
lean_dec_ref(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec(v___y_1726_);
return v___x_1735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSubtype___boxed(lean_object* v_x_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Fmt_fmtSubtype(v_x_1803_, v_a_1804_, v_a_1805_);
lean_dec_ref(v_a_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1(){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1813_ = l_Lean_Fmt_fmtAttribute;
v___x_1814_ = ((lean_object*)(l_Lean_Fmt_fmtSubtype___closed__1));
v___x_1815_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___closed__1));
v___x_1816_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSubtype___boxed), 3, 0);
v___x_1817_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1813_, v___x_1814_, v___x_1815_, v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1___boxed(lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1();
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithoutExpectedType(lean_object* v_x_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = ((lean_object*)(l_Lean_Fmt_fmtWithoutExpectedType___closed__1));
lean_inc(v_x_1823_);
v___x_1827_ = l_Lean_Syntax_isOfKind(v_x_1823_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec(v_x_1823_);
v___x_1828_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v_a_1825_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; lean_object* v_tk_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1830_ = lean_unsigned_to_nat(0u);
v_tk_1831_ = l_Lean_Syntax_getArg(v_x_1823_, v___x_1830_);
v___x_1832_ = lean_unsigned_to_nat(1u);
v___x_1833_ = l_Lean_Syntax_getArg(v_x_1823_, v___x_1832_);
lean_dec(v_x_1823_);
v___x_1834_ = lean_unsigned_to_nat(2u);
v___x_1835_ = lean_mk_empty_array_with_capacity(v___x_1834_);
v___x_1836_ = lean_array_push(v___x_1835_, v_tk_1831_);
v___x_1837_ = lean_array_push(v___x_1836_, v___x_1833_);
v___x_1838_ = l_Lean_Fmt_fmtAppLike(v___x_1837_, v_a_1824_, v_a_1825_);
return v___x_1838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithoutExpectedType___boxed(lean_object* v_x_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_Fmt_fmtWithoutExpectedType(v_x_1839_, v_a_1840_, v_a_1841_);
lean_dec_ref(v_a_1840_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1(){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1849_ = l_Lean_Fmt_fmtAttribute;
v___x_1850_ = ((lean_object*)(l_Lean_Fmt_fmtWithoutExpectedType___closed__1));
v___x_1851_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___closed__1));
v___x_1852_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtWithoutExpectedType___boxed), 3, 0);
v___x_1853_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1849_, v___x_1850_, v___x_1851_, v___x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1___boxed(lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1();
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtModCast(lean_object* v_x_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = ((lean_object*)(l_Lean_Fmt_fmtModCast___closed__1));
lean_inc(v_x_1860_);
v___x_1864_ = l_Lean_Syntax_isOfKind(v_x_1860_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_dec(v_x_1860_);
v___x_1865_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
lean_ctor_set(v___x_1866_, 1, v_a_1862_);
return v___x_1866_;
}
else
{
lean_object* v___x_1867_; lean_object* v_tk_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1867_ = lean_unsigned_to_nat(0u);
v_tk_1868_ = l_Lean_Syntax_getArg(v_x_1860_, v___x_1867_);
v___x_1869_ = lean_unsigned_to_nat(1u);
v___x_1870_ = l_Lean_Syntax_getArg(v_x_1860_, v___x_1869_);
lean_dec(v_x_1860_);
v___x_1871_ = lean_unsigned_to_nat(2u);
v___x_1872_ = lean_mk_empty_array_with_capacity(v___x_1871_);
v___x_1873_ = lean_array_push(v___x_1872_, v_tk_1868_);
v___x_1874_ = lean_array_push(v___x_1873_, v___x_1870_);
v___x_1875_ = l_Lean_Fmt_fmtAppLike(v___x_1874_, v_a_1861_, v_a_1862_);
return v___x_1875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtModCast___boxed(lean_object* v_x_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_Fmt_fmtModCast(v_x_1876_, v_a_1877_, v_a_1878_);
lean_dec_ref(v_a_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1(){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1886_ = l_Lean_Fmt_fmtAttribute;
v___x_1887_ = ((lean_object*)(l_Lean_Fmt_fmtModCast___closed__1));
v___x_1888_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___closed__1));
v___x_1889_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtModCast___boxed), 3, 0);
v___x_1890_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1886_, v___x_1887_, v___x_1888_, v___x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1___boxed(lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1();
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIncludeStr(lean_object* v_x_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = ((lean_object*)(l_Lean_Fmt_fmtIncludeStr___closed__1));
lean_inc(v_x_1897_);
v___x_1901_ = l_Lean_Syntax_isOfKind(v_x_1897_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec(v_x_1897_);
v___x_1902_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v_a_1899_);
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; lean_object* v_tk_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1904_ = lean_unsigned_to_nat(0u);
v_tk_1905_ = l_Lean_Syntax_getArg(v_x_1897_, v___x_1904_);
v___x_1906_ = lean_unsigned_to_nat(1u);
v___x_1907_ = l_Lean_Syntax_getArg(v_x_1897_, v___x_1906_);
lean_dec(v_x_1897_);
v___x_1908_ = lean_unsigned_to_nat(2u);
v___x_1909_ = lean_mk_empty_array_with_capacity(v___x_1908_);
v___x_1910_ = lean_array_push(v___x_1909_, v_tk_1905_);
v___x_1911_ = lean_array_push(v___x_1910_, v___x_1907_);
v___x_1912_ = l_Lean_Fmt_fmtAppLike(v___x_1911_, v_a_1898_, v_a_1899_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtIncludeStr___boxed(lean_object* v_x_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_Fmt_fmtIncludeStr(v_x_1913_, v_a_1914_, v_a_1915_);
lean_dec_ref(v_a_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1(){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1923_ = l_Lean_Fmt_fmtAttribute;
v___x_1924_ = ((lean_object*)(l_Lean_Fmt_fmtIncludeStr___closed__1));
v___x_1925_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___closed__1));
v___x_1926_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtIncludeStr___boxed), 3, 0);
v___x_1927_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1923_, v___x_1924_, v___x_1925_, v___x_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1___boxed(lean_object* v_a_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1();
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithAnnotateTerm(lean_object* v_x_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1937_ = ((lean_object*)(l_Lean_Fmt_fmtWithAnnotateTerm___closed__1));
lean_inc(v_x_1934_);
v___x_1938_ = l_Lean_Syntax_isOfKind(v_x_1934_, v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_dec(v_x_1934_);
v___x_1939_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v_a_1936_);
return v___x_1940_;
}
else
{
lean_object* v___x_1941_; lean_object* v_withAnnotateTermTk_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v_withAnnotateTermTk_1942_ = l_Lean_Syntax_getArg(v_x_1934_, v___x_1941_);
v___x_1943_ = lean_unsigned_to_nat(1u);
v___x_1944_ = l_Lean_Syntax_getArg(v_x_1934_, v___x_1943_);
v___x_1945_ = lean_unsigned_to_nat(2u);
v___x_1946_ = l_Lean_Syntax_getArg(v_x_1934_, v___x_1945_);
lean_dec(v_x_1934_);
v___x_1947_ = lean_unsigned_to_nat(3u);
v___x_1948_ = lean_mk_empty_array_with_capacity(v___x_1947_);
v___x_1949_ = lean_array_push(v___x_1948_, v_withAnnotateTermTk_1942_);
v___x_1950_ = lean_array_push(v___x_1949_, v___x_1944_);
v___x_1951_ = lean_array_push(v___x_1950_, v___x_1946_);
v___x_1952_ = l_Lean_Fmt_fmtAppLike(v___x_1951_, v_a_1935_, v_a_1936_);
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithAnnotateTerm___boxed(lean_object* v_x_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Fmt_fmtWithAnnotateTerm(v_x_1953_, v_a_1954_, v_a_1955_);
lean_dec_ref(v_a_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1(){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1963_ = l_Lean_Fmt_fmtAttribute;
v___x_1964_ = ((lean_object*)(l_Lean_Fmt_fmtWithAnnotateTerm___closed__1));
v___x_1965_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___closed__1));
v___x_1966_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtWithAnnotateTerm___boxed), 3, 0);
v___x_1967_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1963_, v___x_1964_, v___x_1965_, v___x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1___boxed(lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1();
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtByElab(lean_object* v_x_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1977_ = ((lean_object*)(l_Lean_Fmt_fmtByElab___closed__1));
lean_inc(v_x_1974_);
v___x_1978_ = l_Lean_Syntax_isOfKind(v_x_1974_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec(v_x_1974_);
v___x_1979_ = l_Lean_Fmt_Error_partialFormatter;
v___x_1980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
lean_ctor_set(v___x_1980_, 1, v_a_1976_);
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; lean_object* v_tk_1982_; lean_object* v___x_1983_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v_tk_1982_ = l_Lean_Syntax_getArg(v_x_1974_, v___x_1981_);
v___x_1983_ = l_Lean_Fmt_fmt(v_tk_1982_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v_a_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
v_a_1985_ = lean_ctor_get(v___x_1983_, 1);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1983_, 2);
v___x_1986_ = lean_unsigned_to_nat(1u);
v___x_1987_ = l_Lean_Syntax_getArg(v_x_1974_, v___x_1986_);
lean_dec(v_x_1974_);
v___x_1988_ = l_Lean_Fmt_fmt(v___x_1987_, v_a_1975_, v_a_1985_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1999_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_a_1990_ = lean_ctor_get(v___x_1988_, 1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1992_ = v___x_1988_;
v_isShared_1993_ = v_isSharedCheck_1999_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1999_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1994_ = 1;
v___x_1995_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_1984_, v_a_1989_, v___x_1994_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1995_);
v___x_1997_ = v___x_1992_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_a_1990_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
else
{
lean_dec(v_a_1984_);
return v___x_1988_;
}
}
else
{
lean_dec(v_x_1974_);
return v___x_1983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtByElab___boxed(lean_object* v_x_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Fmt_fmtByElab(v_x_2000_, v_a_2001_, v_a_2002_);
lean_dec_ref(v_a_2001_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1(){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2010_ = l_Lean_Fmt_fmtAttribute;
v___x_2011_ = ((lean_object*)(l_Lean_Fmt_fmtByElab___closed__1));
v___x_2012_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___closed__1));
v___x_2013_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtByElab___boxed), 3, 0);
v___x_2014_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2010_, v___x_2011_, v___x_2012_, v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1___boxed(lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1();
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeprecated(lean_object* v_x_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v___x_2031_; uint8_t v___x_2032_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; 
v___x_2031_ = ((lean_object*)(l_Lean_Fmt_fmtDeprecated___closed__1));
lean_inc(v_x_2028_);
v___x_2032_ = l_Lean_Syntax_isOfKind(v_x_2028_, v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_dec(v_x_2028_);
v___x_2143_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
lean_ctor_set(v___x_2144_, 1, v_a_2030_);
return v___x_2144_;
}
else
{
lean_object* v___x_2145_; lean_object* v_tk_2146_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v_lbTk_x3f_2151_; lean_object* v_sinceTk_x3f_2152_; lean_object* v_colonEqTk_x3f_2153_; lean_object* v_since_x3f_2154_; lean_object* v_rbTk_x3f_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___x_2172_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v_typeChanged_x3f_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v_msg_x3f_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v_id_x3f_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2145_ = lean_unsigned_to_nat(0u);
v_tk_2146_ = l_Lean_Syntax_getArg(v_x_2028_, v___x_2145_);
v___x_2172_ = lean_unsigned_to_nat(1u);
v___x_2239_ = l_Lean_Syntax_getArg(v_x_2028_, v___x_2172_);
v___x_2240_ = l_Lean_Syntax_isNone(v___x_2239_);
if (v___x_2240_ == 0)
{
uint8_t v___x_2241_; 
lean_inc(v___x_2239_);
v___x_2241_ = l_Lean_Syntax_matchesNull(v___x_2239_, v___x_2172_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_dec(v___x_2239_);
lean_dec(v_tk_2146_);
lean_dec(v_x_2028_);
v___x_2242_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v_a_2030_);
return v___x_2243_;
}
else
{
lean_object* v_id_x3f_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v_id_x3f_2244_ = l_Lean_Syntax_getArg(v___x_2239_, v___x_2145_);
lean_dec(v___x_2239_);
v___x_2245_ = ((lean_object*)(l_Lean_Fmt_fmtBinderIdent___closed__6));
lean_inc(v_id_x3f_2244_);
v___x_2246_ = l_Lean_Syntax_isOfKind(v_id_x3f_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec(v_id_x3f_2244_);
lean_dec(v_tk_2146_);
lean_dec(v_x_2028_);
v___x_2247_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v_a_2030_);
return v___x_2248_;
}
else
{
lean_object* v___x_2249_; 
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_id_x3f_2244_);
v_id_x3f_2223_ = v___x_2249_;
v___y_2224_ = v_a_2029_;
v___y_2225_ = v_a_2030_;
goto v___jp_2222_;
}
}
}
else
{
lean_object* v___x_2250_; 
lean_dec(v___x_2239_);
v___x_2250_ = lean_box(0);
v_id_x3f_2223_ = v___x_2250_;
v___y_2224_ = v_a_2029_;
v___y_2225_ = v_a_2030_;
goto v___jp_2222_;
}
v___jp_2147_:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_Fmt_fmt(v_tk_2146_, v___y_2156_, v___y_2157_);
if (lean_obj_tag(v___x_2158_) == 0)
{
if (lean_obj_tag(v___y_2150_) == 0)
{
lean_object* v_a_2159_; lean_object* v_a_2160_; lean_object* v___x_2161_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
v_a_2160_ = lean_ctor_get(v___x_2158_, 1);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2158_, 2);
v___x_2161_ = lean_box(0);
v___y_2118_ = v_colonEqTk_x3f_2153_;
v___y_2119_ = v___y_2148_;
v___y_2120_ = v_sinceTk_x3f_2152_;
v___y_2121_ = v_a_2159_;
v___y_2122_ = v___y_2156_;
v___y_2123_ = v___y_2149_;
v___y_2124_ = v_lbTk_x3f_2151_;
v___y_2125_ = v_since_x3f_2154_;
v___y_2126_ = v_a_2160_;
v___y_2127_ = v_rbTk_x3f_2155_;
v___y_2128_ = v___x_2161_;
goto v___jp_2117_;
}
else
{
lean_object* v_a_2162_; lean_object* v_a_2163_; lean_object* v_val_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
v_a_2162_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2162_);
v_a_2163_ = lean_ctor_get(v___x_2158_, 1);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2158_, 2);
v_val_2164_ = lean_ctor_get(v___y_2150_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___y_2150_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___y_2150_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_val_2164_);
lean_dec(v___y_2150_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_val_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
v___y_2118_ = v_colonEqTk_x3f_2153_;
v___y_2119_ = v___y_2148_;
v___y_2120_ = v_sinceTk_x3f_2152_;
v___y_2121_ = v_a_2162_;
v___y_2122_ = v___y_2156_;
v___y_2123_ = v___y_2149_;
v___y_2124_ = v_lbTk_x3f_2151_;
v___y_2125_ = v_since_x3f_2154_;
v___y_2126_ = v_a_2163_;
v___y_2127_ = v_rbTk_x3f_2155_;
v___y_2128_ = v___x_2169_;
goto v___jp_2117_;
}
}
}
}
else
{
lean_dec(v_rbTk_x3f_2155_);
lean_dec(v_since_x3f_2154_);
lean_dec(v_colonEqTk_x3f_2153_);
lean_dec(v_sinceTk_x3f_2152_);
lean_dec(v_lbTk_x3f_2151_);
lean_dec(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec(v___y_2148_);
return v___x_2158_;
}
}
v___jp_2173_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2181_ = lean_unsigned_to_nat(4u);
v___x_2182_ = l_Lean_Syntax_getArg(v_x_2028_, v___x_2181_);
lean_dec(v_x_2028_);
v___x_2183_ = l_Lean_Syntax_isNone(v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2182_);
v___x_2185_ = l_Lean_Syntax_matchesNull(v___x_2182_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
lean_dec(v___x_2182_);
lean_dec(v_typeChanged_x3f_2178_);
lean_dec(v___y_2177_);
lean_dec(v___y_2175_);
lean_dec(v_tk_2146_);
v___x_2186_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v___y_2180_);
return v___x_2187_;
}
else
{
lean_object* v_since_x3f_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v_since_x3f_2188_ = l_Lean_Syntax_getArg(v___x_2182_, v___y_2174_);
v___x_2189_ = ((lean_object*)(l_Lean_Fmt_fmtDeprecated___closed__3));
lean_inc(v_since_x3f_2188_);
v___x_2190_ = l_Lean_Syntax_isOfKind(v_since_x3f_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec(v_since_x3f_2188_);
lean_dec(v___x_2182_);
lean_dec(v_typeChanged_x3f_2178_);
lean_dec(v___y_2177_);
lean_dec(v___y_2175_);
lean_dec(v_tk_2146_);
v___x_2191_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___y_2180_);
return v___x_2192_;
}
else
{
lean_object* v_lbTk_x3f_2193_; lean_object* v_sinceTk_x3f_2194_; lean_object* v_colonEqTk_x3f_2195_; lean_object* v_rbTk_x3f_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_lbTk_x3f_2193_ = l_Lean_Syntax_getArg(v___x_2182_, v___x_2145_);
v_sinceTk_x3f_2194_ = l_Lean_Syntax_getArg(v___x_2182_, v___x_2172_);
v_colonEqTk_x3f_2195_ = l_Lean_Syntax_getArg(v___x_2182_, v___y_2176_);
v_rbTk_x3f_2196_ = l_Lean_Syntax_getArg(v___x_2182_, v___x_2181_);
lean_dec(v___x_2182_);
v___x_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2197_, 0, v_lbTk_x3f_2193_);
v___x_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2198_, 0, v_sinceTk_x3f_2194_);
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v_colonEqTk_x3f_2195_);
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v_since_x3f_2188_);
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v_rbTk_x3f_2196_);
v___y_2148_ = v___y_2175_;
v___y_2149_ = v_typeChanged_x3f_2178_;
v___y_2150_ = v___y_2177_;
v_lbTk_x3f_2151_ = v___x_2197_;
v_sinceTk_x3f_2152_ = v___x_2198_;
v_colonEqTk_x3f_2153_ = v___x_2199_;
v_since_x3f_2154_ = v___x_2200_;
v_rbTk_x3f_2155_ = v___x_2201_;
v___y_2156_ = v___y_2179_;
v___y_2157_ = v___y_2180_;
goto v___jp_2147_;
}
}
}
else
{
lean_object* v___x_2202_; 
lean_dec(v___x_2182_);
v___x_2202_ = lean_box(0);
v___y_2148_ = v___y_2175_;
v___y_2149_ = v_typeChanged_x3f_2178_;
v___y_2150_ = v___y_2177_;
v_lbTk_x3f_2151_ = v___x_2202_;
v_sinceTk_x3f_2152_ = v___x_2202_;
v_colonEqTk_x3f_2153_ = v___x_2202_;
v_since_x3f_2154_ = v___x_2202_;
v_rbTk_x3f_2155_ = v___x_2202_;
v___y_2156_ = v___y_2179_;
v___y_2157_ = v___y_2180_;
goto v___jp_2147_;
}
}
v___jp_2203_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2209_ = lean_unsigned_to_nat(3u);
v___x_2210_ = l_Lean_Syntax_getArg(v_x_2028_, v___x_2209_);
v___x_2211_ = l_Lean_Syntax_isNone(v___x_2210_);
if (v___x_2211_ == 0)
{
uint8_t v___x_2212_; 
lean_inc(v___x_2210_);
v___x_2212_ = l_Lean_Syntax_matchesNull(v___x_2210_, v___x_2172_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec(v___x_2210_);
lean_dec(v_msg_x3f_2206_);
lean_dec(v___y_2205_);
lean_dec(v_tk_2146_);
lean_dec(v_x_2028_);
v___x_2213_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
lean_ctor_set(v___x_2214_, 1, v___y_2208_);
return v___x_2214_;
}
else
{
lean_object* v_typeChanged_x3f_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v_typeChanged_x3f_2215_ = l_Lean_Syntax_getArg(v___x_2210_, v___x_2145_);
lean_dec(v___x_2210_);
v___x_2216_ = ((lean_object*)(l_Lean_Fmt_fmtDeprecated___closed__5));
lean_inc(v_typeChanged_x3f_2215_);
v___x_2217_ = l_Lean_Syntax_isOfKind(v_typeChanged_x3f_2215_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v_typeChanged_x3f_2215_);
lean_dec(v_msg_x3f_2206_);
lean_dec(v___y_2205_);
lean_dec(v_tk_2146_);
lean_dec(v_x_2028_);
v___x_2218_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v___y_2208_);
return v___x_2219_;
}
else
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2220_, 0, v_typeChanged_x3f_2215_);
v___y_2174_ = v___x_2209_;
v___y_2175_ = v_msg_x3f_2206_;
v___y_2176_ = v___y_2204_;
v___y_2177_ = v___y_2205_;
v_typeChanged_x3f_2178_ = v___x_2220_;
v___y_2179_ = v___y_2207_;
v___y_2180_ = v___y_2208_;
goto v___jp_2173_;
}
}
}
else
{
lean_object* v___x_2221_; 
lean_dec(v___x_2210_);
v___x_2221_ = lean_box(0);
v___y_2174_ = v___x_2209_;
v___y_2175_ = v_msg_x3f_2206_;
v___y_2176_ = v___y_2204_;
v___y_2177_ = v___y_2205_;
v_typeChanged_x3f_2178_ = v___x_2221_;
v___y_2179_ = v___y_2207_;
v___y_2180_ = v___y_2208_;
goto v___jp_2173_;
}
}
v___jp_2222_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2226_ = lean_unsigned_to_nat(2u);
v___x_2227_ = l_Lean_Syntax_getArg(v_x_2028_, v___x_2226_);
v___x_2228_ = l_Lean_Syntax_isNone(v___x_2227_);
if (v___x_2228_ == 0)
{
uint8_t v___x_2229_; 
lean_inc(v___x_2227_);
v___x_2229_ = l_Lean_Syntax_matchesNull(v___x_2227_, v___x_2172_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v___x_2227_);
lean_dec(v_id_x3f_2223_);
lean_dec(v_tk_2146_);
lean_dec(v_x_2028_);
v___x_2230_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v___y_2225_);
return v___x_2231_;
}
else
{
lean_object* v_msg_x3f_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; 
v_msg_x3f_2232_ = l_Lean_Syntax_getArg(v___x_2227_, v___x_2145_);
lean_dec(v___x_2227_);
v___x_2233_ = ((lean_object*)(l_Lean_Fmt_fmtDeprecated___closed__3));
lean_inc(v_msg_x3f_2232_);
v___x_2234_ = l_Lean_Syntax_isOfKind(v_msg_x3f_2232_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_dec(v_msg_x3f_2232_);
lean_dec(v_id_x3f_2223_);
lean_dec(v_tk_2146_);
lean_dec(v_x_2028_);
v___x_2235_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set(v___x_2236_, 1, v___y_2225_);
return v___x_2236_;
}
else
{
lean_object* v___x_2237_; 
v___x_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2237_, 0, v_msg_x3f_2232_);
v___y_2204_ = v___x_2226_;
v___y_2205_ = v_id_x3f_2223_;
v_msg_x3f_2206_ = v___x_2237_;
v___y_2207_ = v___y_2224_;
v___y_2208_ = v___y_2225_;
goto v___jp_2203_;
}
}
}
else
{
lean_object* v___x_2238_; 
lean_dec(v___x_2227_);
v___x_2238_ = lean_box(0);
v___y_2204_ = v___x_2226_;
v___y_2205_ = v_id_x3f_2223_;
v_msg_x3f_2206_ = v___x_2238_;
v___y_2207_ = v___y_2224_;
v___y_2208_ = v___y_2225_;
goto v___jp_2203_;
}
}
}
v___jp_2033_:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v___y_2040_, v___y_2038_, v___y_2035_, v___y_2044_, v___y_2043_, v___y_2037_, v___y_2039_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2064_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_a_2047_ = lean_ctor_get(v___x_2045_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2049_ = v___x_2045_;
v_isShared_2050_ = v_isSharedCheck_2064_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2064_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2051_ = lean_unsigned_to_nat(5u);
v___x_2052_ = lean_mk_empty_array_with_capacity(v___x_2051_);
v___x_2053_ = lean_array_push(v___x_2052_, v___y_2036_);
v___x_2054_ = lean_array_push(v___x_2053_, v___y_2034_);
v___x_2055_ = lean_array_push(v___x_2054_, v___y_2041_);
v___x_2056_ = lean_array_push(v___x_2055_, v___y_2042_);
v___x_2057_ = lean_array_push(v___x_2056_, v_a_2046_);
v___x_2058_ = 0;
v___x_2059_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2059_, 0, v___x_2032_);
lean_ctor_set_uint8(v___x_2059_, 1, v___x_2058_);
lean_ctor_set_uint8(v___x_2059_, 2, v___x_2058_);
lean_ctor_set_uint8(v___x_2059_, 3, v___x_2058_);
v___x_2060_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2057_, v___x_2059_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2060_);
v___x_2062_ = v___x_2049_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_a_2047_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
else
{
lean_dec_ref(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v___y_2036_);
lean_dec_ref(v___y_2034_);
return v___x_2045_;
}
}
v___jp_2065_:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Fmt_fmt_x3f(v___y_2076_, v___y_2071_, v___y_2070_);
if (lean_obj_tag(v___x_2077_) == 0)
{
if (lean_obj_tag(v___y_2074_) == 0)
{
lean_object* v_a_2078_; lean_object* v_a_2079_; lean_object* v___x_2080_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
v_a_2079_ = lean_ctor_get(v___x_2077_, 1);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2077_, 2);
v___x_2080_ = lean_box(0);
v___y_2034_ = v___y_2066_;
v___y_2035_ = v___y_2067_;
v___y_2036_ = v___y_2069_;
v___y_2037_ = v___y_2071_;
v___y_2038_ = v___y_2068_;
v___y_2039_ = v_a_2079_;
v___y_2040_ = v___y_2072_;
v___y_2041_ = v___y_2073_;
v___y_2042_ = v_a_2078_;
v___y_2043_ = v___y_2075_;
v___y_2044_ = v___x_2080_;
goto v___jp_2033_;
}
else
{
lean_object* v_a_2081_; lean_object* v_a_2082_; lean_object* v_val_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
v_a_2081_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2081_);
v_a_2082_ = lean_ctor_get(v___x_2077_, 1);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2077_, 2);
v_val_2083_ = lean_ctor_get(v___y_2074_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___y_2074_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___y_2074_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_val_2083_);
lean_dec(v___y_2074_);
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
v___y_2034_ = v___y_2066_;
v___y_2035_ = v___y_2067_;
v___y_2036_ = v___y_2069_;
v___y_2037_ = v___y_2071_;
v___y_2038_ = v___y_2068_;
v___y_2039_ = v_a_2082_;
v___y_2040_ = v___y_2072_;
v___y_2041_ = v___y_2073_;
v___y_2042_ = v_a_2081_;
v___y_2043_ = v___y_2075_;
v___y_2044_ = v___x_2088_;
goto v___jp_2033_;
}
}
}
}
else
{
lean_dec(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
return v___x_2077_;
}
}
v___jp_2091_:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_Fmt_fmt_x3f(v___y_2102_, v___y_2096_, v___y_2099_);
if (lean_obj_tag(v___x_2103_) == 0)
{
if (lean_obj_tag(v___y_2097_) == 0)
{
lean_object* v_a_2104_; lean_object* v_a_2105_; lean_object* v___x_2106_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
v_a_2105_ = lean_ctor_get(v___x_2103_, 1);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2103_, 2);
v___x_2106_ = lean_box(0);
v___y_2066_ = v___y_2092_;
v___y_2067_ = v___y_2093_;
v___y_2068_ = v___y_2095_;
v___y_2069_ = v___y_2094_;
v___y_2070_ = v_a_2105_;
v___y_2071_ = v___y_2096_;
v___y_2072_ = v___y_2098_;
v___y_2073_ = v_a_2104_;
v___y_2074_ = v___y_2100_;
v___y_2075_ = v___y_2101_;
v___y_2076_ = v___x_2106_;
goto v___jp_2065_;
}
else
{
lean_object* v_a_2107_; lean_object* v_a_2108_; lean_object* v_val_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
v_a_2107_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2107_);
v_a_2108_ = lean_ctor_get(v___x_2103_, 1);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2103_, 2);
v_val_2109_ = lean_ctor_get(v___y_2097_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___y_2097_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___y_2097_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_val_2109_);
lean_dec(v___y_2097_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_val_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
v___y_2066_ = v___y_2092_;
v___y_2067_ = v___y_2093_;
v___y_2068_ = v___y_2095_;
v___y_2069_ = v___y_2094_;
v___y_2070_ = v_a_2108_;
v___y_2071_ = v___y_2096_;
v___y_2072_ = v___y_2098_;
v___y_2073_ = v_a_2107_;
v___y_2074_ = v___y_2100_;
v___y_2075_ = v___y_2101_;
v___y_2076_ = v___x_2114_;
goto v___jp_2065_;
}
}
}
}
else
{
lean_dec(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
return v___x_2103_;
}
}
v___jp_2117_:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_Fmt_fmt_x3f(v___y_2128_, v___y_2122_, v___y_2126_);
if (lean_obj_tag(v___x_2129_) == 0)
{
if (lean_obj_tag(v___y_2119_) == 0)
{
lean_object* v_a_2130_; lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
v_a_2131_ = lean_ctor_get(v___x_2129_, 1);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2129_, 2);
v___x_2132_ = lean_box(0);
v___y_2092_ = v_a_2130_;
v___y_2093_ = v___y_2118_;
v___y_2094_ = v___y_2121_;
v___y_2095_ = v___y_2120_;
v___y_2096_ = v___y_2122_;
v___y_2097_ = v___y_2123_;
v___y_2098_ = v___y_2124_;
v___y_2099_ = v_a_2131_;
v___y_2100_ = v___y_2125_;
v___y_2101_ = v___y_2127_;
v___y_2102_ = v___x_2132_;
goto v___jp_2091_;
}
else
{
lean_object* v_a_2133_; lean_object* v_a_2134_; lean_object* v_val_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
v_a_2133_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2133_);
v_a_2134_ = lean_ctor_get(v___x_2129_, 1);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2129_, 2);
v_val_2135_ = lean_ctor_get(v___y_2119_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___y_2119_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___y_2119_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_val_2135_);
lean_dec(v___y_2119_);
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
v___y_2092_ = v_a_2133_;
v___y_2093_ = v___y_2118_;
v___y_2094_ = v___y_2121_;
v___y_2095_ = v___y_2120_;
v___y_2096_ = v___y_2122_;
v___y_2097_ = v___y_2123_;
v___y_2098_ = v___y_2124_;
v___y_2099_ = v_a_2134_;
v___y_2100_ = v___y_2125_;
v___y_2101_ = v___y_2127_;
v___y_2102_ = v___x_2140_;
goto v___jp_2091_;
}
}
}
}
else
{
lean_dec(v___y_2127_);
lean_dec(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec(v___y_2118_);
return v___x_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeprecated___boxed(lean_object* v_x_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Fmt_fmtDeprecated(v_x_2251_, v_a_2252_, v_a_2253_);
lean_dec_ref(v_a_2252_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1(){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2261_ = l_Lean_Fmt_fmtAttribute;
v___x_2262_ = ((lean_object*)(l_Lean_Fmt_fmtDeprecated___closed__1));
v___x_2263_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___closed__1));
v___x_2264_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDeprecated___boxed), 3, 0);
v___x_2265_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2261_, v___x_2262_, v___x_2263_, v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1___boxed(lean_object* v_a_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1();
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeprecatedArg(lean_object* v_x_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = ((lean_object*)(l_Lean_Fmt_fmtDeprecatedArg___closed__1));
lean_inc(v_x_2272_);
v___x_2276_ = l_Lean_Syntax_isOfKind(v_x_2272_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_dec(v_x_2272_);
v___x_2277_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v_a_2274_);
return v___x_2278_;
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; 
v___x_2279_ = lean_unsigned_to_nat(1u);
v___x_2280_ = l_Lean_Syntax_getArg(v_x_2272_, v___x_2279_);
v___x_2281_ = ((lean_object*)(l_Lean_Fmt_fmtBinderIdent___closed__6));
lean_inc(v___x_2280_);
v___x_2282_ = l_Lean_Syntax_isOfKind(v___x_2280_, v___x_2281_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_dec(v___x_2280_);
lean_dec(v_x_2272_);
v___x_2367_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set(v___x_2368_, 1, v_a_2274_);
return v___x_2368_;
}
else
{
lean_object* v___x_2369_; lean_object* v_tk_2370_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v_lbTk_x3f_2374_; lean_object* v_sinceTk_x3f_2375_; lean_object* v_colonEqTk_x3f_2376_; lean_object* v_since_x3f_2377_; lean_object* v_rbTk_x3f_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___x_2398_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v_msg_x3f_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v_new_x3f_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2369_ = lean_unsigned_to_nat(0u);
v_tk_2370_ = l_Lean_Syntax_getArg(v_x_2272_, v___x_2369_);
v___x_2398_ = lean_unsigned_to_nat(2u);
v___x_2444_ = l_Lean_Syntax_getArg(v_x_2272_, v___x_2398_);
v___x_2445_ = l_Lean_Syntax_isNone(v___x_2444_);
if (v___x_2445_ == 0)
{
uint8_t v___x_2446_; 
lean_inc(v___x_2444_);
v___x_2446_ = l_Lean_Syntax_matchesNull(v___x_2444_, v___x_2279_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec(v___x_2444_);
lean_dec(v_tk_2370_);
lean_dec(v___x_2280_);
lean_dec(v_x_2272_);
v___x_2447_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v_a_2274_);
return v___x_2448_;
}
else
{
lean_object* v_new_x3f_2449_; uint8_t v___x_2450_; 
v_new_x3f_2449_ = l_Lean_Syntax_getArg(v___x_2444_, v___x_2369_);
lean_dec(v___x_2444_);
lean_inc(v_new_x3f_2449_);
v___x_2450_ = l_Lean_Syntax_isOfKind(v_new_x3f_2449_, v___x_2281_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
lean_dec(v_new_x3f_2449_);
lean_dec(v_tk_2370_);
lean_dec(v___x_2280_);
lean_dec(v_x_2272_);
v___x_2451_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
lean_ctor_set(v___x_2452_, 1, v_a_2274_);
return v___x_2452_;
}
else
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_new_x3f_2449_);
v_new_x3f_2428_ = v___x_2453_;
v___y_2429_ = v_a_2273_;
v___y_2430_ = v_a_2274_;
goto v___jp_2427_;
}
}
}
else
{
lean_object* v___x_2454_; 
lean_dec(v___x_2444_);
v___x_2454_ = lean_box(0);
v_new_x3f_2428_ = v___x_2454_;
v___y_2429_ = v_a_2273_;
v___y_2430_ = v_a_2274_;
goto v___jp_2427_;
}
v___jp_2371_:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_Fmt_fmt(v_tk_2370_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v_a_2383_; lean_object* v___x_2384_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
v_a_2383_ = lean_ctor_get(v___x_2381_, 1);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2381_, 2);
v___x_2384_ = l_Lean_Fmt_fmt(v___x_2280_, v___y_2379_, v_a_2383_);
if (lean_obj_tag(v___x_2384_) == 0)
{
if (lean_obj_tag(v___y_2372_) == 0)
{
lean_object* v_a_2385_; lean_object* v_a_2386_; lean_object* v___x_2387_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
v_a_2386_ = lean_ctor_get(v___x_2384_, 1);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2384_, 2);
v___x_2387_ = lean_box(0);
v___y_2342_ = v_lbTk_x3f_2374_;
v___y_2343_ = v_a_2385_;
v___y_2344_ = v_a_2382_;
v___y_2345_ = v___y_2379_;
v___y_2346_ = v_since_x3f_2377_;
v___y_2347_ = v_colonEqTk_x3f_2376_;
v___y_2348_ = v_a_2386_;
v___y_2349_ = v___y_2373_;
v___y_2350_ = v_rbTk_x3f_2378_;
v___y_2351_ = v_sinceTk_x3f_2375_;
v___y_2352_ = v___x_2387_;
goto v___jp_2341_;
}
else
{
lean_object* v_a_2388_; lean_object* v_a_2389_; lean_object* v_val_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
v_a_2388_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2388_);
v_a_2389_ = lean_ctor_get(v___x_2384_, 1);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2384_, 2);
v_val_2390_ = lean_ctor_get(v___y_2372_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___y_2372_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___y_2372_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_val_2390_);
lean_dec(v___y_2372_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_val_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
v___y_2342_ = v_lbTk_x3f_2374_;
v___y_2343_ = v_a_2388_;
v___y_2344_ = v_a_2382_;
v___y_2345_ = v___y_2379_;
v___y_2346_ = v_since_x3f_2377_;
v___y_2347_ = v_colonEqTk_x3f_2376_;
v___y_2348_ = v_a_2389_;
v___y_2349_ = v___y_2373_;
v___y_2350_ = v_rbTk_x3f_2378_;
v___y_2351_ = v_sinceTk_x3f_2375_;
v___y_2352_ = v___x_2395_;
goto v___jp_2341_;
}
}
}
}
else
{
lean_dec(v_a_2382_);
lean_dec(v_rbTk_x3f_2378_);
lean_dec(v_since_x3f_2377_);
lean_dec(v_colonEqTk_x3f_2376_);
lean_dec(v_sinceTk_x3f_2375_);
lean_dec(v_lbTk_x3f_2374_);
lean_dec(v___y_2373_);
lean_dec(v___y_2372_);
return v___x_2384_;
}
}
else
{
lean_dec(v_rbTk_x3f_2378_);
lean_dec(v_since_x3f_2377_);
lean_dec(v_colonEqTk_x3f_2376_);
lean_dec(v_sinceTk_x3f_2375_);
lean_dec(v_lbTk_x3f_2374_);
lean_dec(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec(v___x_2280_);
return v___x_2381_;
}
}
v___jp_2399_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2405_ = lean_unsigned_to_nat(4u);
v___x_2406_ = l_Lean_Syntax_getArg(v_x_2272_, v___x_2405_);
lean_dec(v_x_2272_);
v___x_2407_ = l_Lean_Syntax_isNone(v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2406_);
v___x_2409_ = l_Lean_Syntax_matchesNull(v___x_2406_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_dec(v___x_2406_);
lean_dec(v_msg_x3f_2402_);
lean_dec(v___y_2400_);
lean_dec(v_tk_2370_);
lean_dec(v___x_2280_);
v___x_2410_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v___y_2404_);
return v___x_2411_;
}
else
{
lean_object* v_since_x3f_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v_since_x3f_2412_ = l_Lean_Syntax_getArg(v___x_2406_, v___y_2401_);
v___x_2413_ = ((lean_object*)(l_Lean_Fmt_fmtDeprecated___closed__3));
lean_inc(v_since_x3f_2412_);
v___x_2414_ = l_Lean_Syntax_isOfKind(v_since_x3f_2412_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
lean_dec(v_since_x3f_2412_);
lean_dec(v___x_2406_);
lean_dec(v_msg_x3f_2402_);
lean_dec(v___y_2400_);
lean_dec(v_tk_2370_);
lean_dec(v___x_2280_);
v___x_2415_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v___y_2404_);
return v___x_2416_;
}
else
{
lean_object* v_lbTk_x3f_2417_; lean_object* v_sinceTk_x3f_2418_; lean_object* v_colonEqTk_x3f_2419_; lean_object* v_rbTk_x3f_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_lbTk_x3f_2417_ = l_Lean_Syntax_getArg(v___x_2406_, v___x_2369_);
v_sinceTk_x3f_2418_ = l_Lean_Syntax_getArg(v___x_2406_, v___x_2279_);
v_colonEqTk_x3f_2419_ = l_Lean_Syntax_getArg(v___x_2406_, v___x_2398_);
v_rbTk_x3f_2420_ = l_Lean_Syntax_getArg(v___x_2406_, v___x_2405_);
lean_dec(v___x_2406_);
v___x_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_lbTk_x3f_2417_);
v___x_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2422_, 0, v_sinceTk_x3f_2418_);
v___x_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2423_, 0, v_colonEqTk_x3f_2419_);
v___x_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2424_, 0, v_since_x3f_2412_);
v___x_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_rbTk_x3f_2420_);
v___y_2372_ = v___y_2400_;
v___y_2373_ = v_msg_x3f_2402_;
v_lbTk_x3f_2374_ = v___x_2421_;
v_sinceTk_x3f_2375_ = v___x_2422_;
v_colonEqTk_x3f_2376_ = v___x_2423_;
v_since_x3f_2377_ = v___x_2424_;
v_rbTk_x3f_2378_ = v___x_2425_;
v___y_2379_ = v___y_2403_;
v___y_2380_ = v___y_2404_;
goto v___jp_2371_;
}
}
}
else
{
lean_object* v___x_2426_; 
lean_dec(v___x_2406_);
v___x_2426_ = lean_box(0);
v___y_2372_ = v___y_2400_;
v___y_2373_ = v_msg_x3f_2402_;
v_lbTk_x3f_2374_ = v___x_2426_;
v_sinceTk_x3f_2375_ = v___x_2426_;
v_colonEqTk_x3f_2376_ = v___x_2426_;
v_since_x3f_2377_ = v___x_2426_;
v_rbTk_x3f_2378_ = v___x_2426_;
v___y_2379_ = v___y_2403_;
v___y_2380_ = v___y_2404_;
goto v___jp_2371_;
}
}
v___jp_2427_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2431_ = lean_unsigned_to_nat(3u);
v___x_2432_ = l_Lean_Syntax_getArg(v_x_2272_, v___x_2431_);
v___x_2433_ = l_Lean_Syntax_isNone(v___x_2432_);
if (v___x_2433_ == 0)
{
uint8_t v___x_2434_; 
lean_inc(v___x_2432_);
v___x_2434_ = l_Lean_Syntax_matchesNull(v___x_2432_, v___x_2279_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec(v___x_2432_);
lean_dec(v_new_x3f_2428_);
lean_dec(v_tk_2370_);
lean_dec(v___x_2280_);
lean_dec(v_x_2272_);
v___x_2435_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v___y_2430_);
return v___x_2436_;
}
else
{
lean_object* v_msg_x3f_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v_msg_x3f_2437_ = l_Lean_Syntax_getArg(v___x_2432_, v___x_2369_);
lean_dec(v___x_2432_);
v___x_2438_ = ((lean_object*)(l_Lean_Fmt_fmtDeprecated___closed__3));
lean_inc(v_msg_x3f_2437_);
v___x_2439_ = l_Lean_Syntax_isOfKind(v_msg_x3f_2437_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
lean_dec(v_msg_x3f_2437_);
lean_dec(v_new_x3f_2428_);
lean_dec(v_tk_2370_);
lean_dec(v___x_2280_);
lean_dec(v_x_2272_);
v___x_2440_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
lean_ctor_set(v___x_2441_, 1, v___y_2430_);
return v___x_2441_;
}
else
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2442_, 0, v_msg_x3f_2437_);
v___y_2400_ = v_new_x3f_2428_;
v___y_2401_ = v___x_2431_;
v_msg_x3f_2402_ = v___x_2442_;
v___y_2403_ = v___y_2429_;
v___y_2404_ = v___y_2430_;
goto v___jp_2399_;
}
}
}
else
{
lean_object* v___x_2443_; 
lean_dec(v___x_2432_);
v___x_2443_ = lean_box(0);
v___y_2400_ = v_new_x3f_2428_;
v___y_2401_ = v___x_2431_;
v_msg_x3f_2402_ = v___x_2443_;
v___y_2403_ = v___y_2429_;
v___y_2404_ = v___y_2430_;
goto v___jp_2399_;
}
}
}
v___jp_2283_:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v___y_2284_, v___y_2293_, v___y_2291_, v___y_2294_, v___y_2292_, v___y_2288_, v___y_2290_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2314_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_a_2297_ = lean_ctor_get(v___x_2295_, 1);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2299_ = v___x_2295_;
v_isShared_2300_ = v_isSharedCheck_2314_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2314_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2301_ = lean_unsigned_to_nat(5u);
v___x_2302_ = lean_mk_empty_array_with_capacity(v___x_2301_);
v___x_2303_ = lean_array_push(v___x_2302_, v___y_2287_);
v___x_2304_ = lean_array_push(v___x_2303_, v___y_2285_);
v___x_2305_ = lean_array_push(v___x_2304_, v___y_2286_);
v___x_2306_ = lean_array_push(v___x_2305_, v___y_2289_);
v___x_2307_ = lean_array_push(v___x_2306_, v_a_2296_);
v___x_2308_ = 0;
v___x_2309_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2309_, 0, v___x_2282_);
lean_ctor_set_uint8(v___x_2309_, 1, v___x_2308_);
lean_ctor_set_uint8(v___x_2309_, 2, v___x_2308_);
lean_ctor_set_uint8(v___x_2309_, 3, v___x_2308_);
v___x_2310_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2307_, v___x_2309_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2310_);
v___x_2312_ = v___x_2299_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_a_2297_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
else
{
lean_dec_ref(v___y_2289_);
lean_dec_ref(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec_ref(v___y_2285_);
return v___x_2295_;
}
}
v___jp_2315_:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_Fmt_fmt_x3f(v___y_2326_, v___y_2321_, v___y_2320_);
if (lean_obj_tag(v___x_2327_) == 0)
{
if (lean_obj_tag(v___y_2322_) == 0)
{
lean_object* v_a_2328_; lean_object* v_a_2329_; lean_object* v___x_2330_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
v_a_2329_ = lean_ctor_get(v___x_2327_, 1);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2327_, 2);
v___x_2330_ = lean_box(0);
v___y_2284_ = v___y_2316_;
v___y_2285_ = v___y_2317_;
v___y_2286_ = v___y_2319_;
v___y_2287_ = v___y_2318_;
v___y_2288_ = v___y_2321_;
v___y_2289_ = v_a_2328_;
v___y_2290_ = v_a_2329_;
v___y_2291_ = v___y_2323_;
v___y_2292_ = v___y_2325_;
v___y_2293_ = v___y_2324_;
v___y_2294_ = v___x_2330_;
goto v___jp_2283_;
}
else
{
lean_object* v_a_2331_; lean_object* v_a_2332_; lean_object* v_val_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
v_a_2331_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2331_);
v_a_2332_ = lean_ctor_get(v___x_2327_, 1);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2327_, 2);
v_val_2333_ = lean_ctor_get(v___y_2322_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___y_2322_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___y_2322_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_val_2333_);
lean_dec(v___y_2322_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_val_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
v___y_2284_ = v___y_2316_;
v___y_2285_ = v___y_2317_;
v___y_2286_ = v___y_2319_;
v___y_2287_ = v___y_2318_;
v___y_2288_ = v___y_2321_;
v___y_2289_ = v_a_2331_;
v___y_2290_ = v_a_2332_;
v___y_2291_ = v___y_2323_;
v___y_2292_ = v___y_2325_;
v___y_2293_ = v___y_2324_;
v___y_2294_ = v___x_2338_;
goto v___jp_2283_;
}
}
}
}
else
{
lean_dec(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
return v___x_2327_;
}
}
v___jp_2341_:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Fmt_fmt_x3f(v___y_2352_, v___y_2345_, v___y_2348_);
if (lean_obj_tag(v___x_2353_) == 0)
{
if (lean_obj_tag(v___y_2349_) == 0)
{
lean_object* v_a_2354_; lean_object* v_a_2355_; lean_object* v___x_2356_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
v_a_2355_ = lean_ctor_get(v___x_2353_, 1);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2353_, 2);
v___x_2356_ = lean_box(0);
v___y_2316_ = v___y_2342_;
v___y_2317_ = v___y_2343_;
v___y_2318_ = v___y_2344_;
v___y_2319_ = v_a_2354_;
v___y_2320_ = v_a_2355_;
v___y_2321_ = v___y_2345_;
v___y_2322_ = v___y_2346_;
v___y_2323_ = v___y_2347_;
v___y_2324_ = v___y_2351_;
v___y_2325_ = v___y_2350_;
v___y_2326_ = v___x_2356_;
goto v___jp_2315_;
}
else
{
lean_object* v_a_2357_; lean_object* v_a_2358_; lean_object* v_val_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
v_a_2357_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2357_);
v_a_2358_ = lean_ctor_get(v___x_2353_, 1);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2353_, 2);
v_val_2359_ = lean_ctor_get(v___y_2349_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___y_2349_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___y_2349_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_val_2359_);
lean_dec(v___y_2349_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_val_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
v___y_2316_ = v___y_2342_;
v___y_2317_ = v___y_2343_;
v___y_2318_ = v___y_2344_;
v___y_2319_ = v_a_2357_;
v___y_2320_ = v_a_2358_;
v___y_2321_ = v___y_2345_;
v___y_2322_ = v___y_2346_;
v___y_2323_ = v___y_2347_;
v___y_2324_ = v___y_2351_;
v___y_2325_ = v___y_2350_;
v___y_2326_ = v___x_2364_;
goto v___jp_2315_;
}
}
}
}
else
{
lean_dec(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
return v___x_2353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDeprecatedArg___boxed(lean_object* v_x_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_Fmt_fmtDeprecatedArg(v_x_2455_, v_a_2456_, v_a_2457_);
lean_dec_ref(v_a_2456_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1(){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2465_ = l_Lean_Fmt_fmtAttribute;
v___x_2466_ = ((lean_object*)(l_Lean_Fmt_fmtDeprecatedArg___closed__1));
v___x_2467_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___closed__1));
v___x_2468_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDeprecatedArg___boxed), 3, 0);
v___x_2469_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2465_, v___x_2466_, v___x_2467_, v___x_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1___boxed(lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1();
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSuggestFor(lean_object* v_x_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___x_2479_ = ((lean_object*)(l_Lean_Fmt_fmtSuggestFor___closed__1));
lean_inc(v_x_2476_);
v___x_2480_ = l_Lean_Syntax_isOfKind(v_x_2476_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_dec(v_x_2476_);
v___x_2481_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v_a_2478_);
return v___x_2482_;
}
else
{
lean_object* v___x_2483_; lean_object* v_tk_2484_; lean_object* v___x_2485_; 
v___x_2483_ = lean_unsigned_to_nat(0u);
v_tk_2484_ = l_Lean_Syntax_getArg(v_x_2476_, v___x_2483_);
v___x_2485_ = l_Lean_Fmt_fmt(v_tk_2484_, v_a_2477_, v_a_2478_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v_a_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v_ids_2490_; lean_object* v___x_2491_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
v_a_2487_ = lean_ctor_get(v___x_2485_, 1);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2485_, 2);
v___x_2488_ = lean_unsigned_to_nat(1u);
v___x_2489_ = l_Lean_Syntax_getArg(v_x_2476_, v___x_2488_);
lean_dec(v_x_2476_);
v_ids_2490_ = l_Lean_Syntax_getArgs(v___x_2489_);
lean_dec(v___x_2489_);
v___x_2491_ = l_Lean_Fmt_fmtArray___redArg(v_ids_2490_, v_a_2477_, v_a_2487_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2506_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_a_2493_ = lean_ctor_get(v___x_2491_, 1);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2495_ = v___x_2491_;
v_isShared_2496_ = v_isSharedCheck_2506_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2506_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2497_ = lean_mk_empty_array_with_capacity(v___x_2488_);
v___x_2498_ = lean_array_push(v___x_2497_, v_a_2486_);
v___x_2499_ = l_Array_append___redArg(v___x_2498_, v_a_2492_);
lean_dec(v_a_2492_);
v___x_2500_ = 0;
v___x_2501_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2501_, 0, v___x_2480_);
lean_ctor_set_uint8(v___x_2501_, 1, v___x_2500_);
lean_ctor_set_uint8(v___x_2501_, 2, v___x_2500_);
lean_ctor_set_uint8(v___x_2501_, 3, v___x_2500_);
v___x_2502_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2499_, v___x_2501_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2502_);
v___x_2504_ = v___x_2495_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_a_2493_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_a_2486_);
v_a_2507_ = lean_ctor_get(v___x_2491_, 0);
v_a_2508_ = lean_ctor_get(v___x_2491_, 1);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2491_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_inc(v_a_2507_);
lean_dec(v___x_2491_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2507_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_dec(v_x_2476_);
return v___x_2485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSuggestFor___boxed(lean_object* v_x_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_Fmt_fmtSuggestFor(v_x_2516_, v_a_2517_, v_a_2518_);
lean_dec_ref(v_a_2517_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1(){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2526_ = l_Lean_Fmt_fmtAttribute;
v___x_2527_ = ((lean_object*)(l_Lean_Fmt_fmtSuggestFor___closed__1));
v___x_2528_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___closed__1));
v___x_2529_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSuggestFor___boxed), 3, 0);
v___x_2530_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2526_, v___x_2527_, v___x_2528_, v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1___boxed(lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1();
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnivOutParams(lean_object* v_x_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = ((lean_object*)(l_Lean_Fmt_fmtUnivOutParams___closed__1));
lean_inc(v_x_2537_);
v___x_2541_ = l_Lean_Syntax_isOfKind(v_x_2537_, v___x_2540_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_dec(v_x_2537_);
v___x_2542_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v_a_2539_);
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; lean_object* v_tk_2545_; lean_object* v___x_2546_; 
v___x_2544_ = lean_unsigned_to_nat(0u);
v_tk_2545_ = l_Lean_Syntax_getArg(v_x_2537_, v___x_2544_);
v___x_2546_ = l_Lean_Fmt_fmt(v_tk_2545_, v_a_2538_, v_a_2539_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v_a_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v_ids_2551_; lean_object* v___x_2552_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
v_a_2548_ = lean_ctor_get(v___x_2546_, 1);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2546_, 2);
v___x_2549_ = lean_unsigned_to_nat(1u);
v___x_2550_ = l_Lean_Syntax_getArg(v_x_2537_, v___x_2549_);
lean_dec(v_x_2537_);
v_ids_2551_ = l_Lean_Syntax_getArgs(v___x_2550_);
lean_dec(v___x_2550_);
v___x_2552_ = l_Lean_Fmt_fmtArray___redArg(v_ids_2551_, v_a_2538_, v_a_2548_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2567_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_a_2554_ = lean_ctor_get(v___x_2552_, 1);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2556_ = v___x_2552_;
v_isShared_2557_ = v_isSharedCheck_2567_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2567_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
v___x_2558_ = lean_mk_empty_array_with_capacity(v___x_2549_);
v___x_2559_ = lean_array_push(v___x_2558_, v_a_2547_);
v___x_2560_ = l_Array_append___redArg(v___x_2559_, v_a_2553_);
lean_dec(v_a_2553_);
v___x_2561_ = 0;
v___x_2562_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2562_, 0, v___x_2541_);
lean_ctor_set_uint8(v___x_2562_, 1, v___x_2561_);
lean_ctor_set_uint8(v___x_2562_, 2, v___x_2561_);
lean_ctor_set_uint8(v___x_2562_, 3, v___x_2561_);
v___x_2563_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2560_, v___x_2562_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2563_);
v___x_2565_ = v___x_2556_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_a_2554_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v_a_2547_);
v_a_2568_ = lean_ctor_get(v___x_2552_, 0);
v_a_2569_ = lean_ctor_get(v___x_2552_, 1);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2552_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_inc(v_a_2568_);
lean_dec(v___x_2552_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2568_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_dec(v_x_2537_);
return v___x_2546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnivOutParams___boxed(lean_object* v_x_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_Fmt_fmtUnivOutParams(v_x_2577_, v_a_2578_, v_a_2579_);
lean_dec_ref(v_a_2578_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1(){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2587_ = l_Lean_Fmt_fmtAttribute;
v___x_2588_ = ((lean_object*)(l_Lean_Fmt_fmtUnivOutParams___closed__1));
v___x_2589_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___closed__1));
v___x_2590_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtUnivOutParams___boxed), 3, 0);
v___x_2591_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2587_, v___x_2588_, v___x_2589_, v___x_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1___boxed(lean_object* v_a_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1();
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCommandCodeAction(lean_object* v_x_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2601_ = ((lean_object*)(l_Lean_Fmt_fmtCommandCodeAction___closed__1));
lean_inc(v_x_2598_);
v___x_2602_ = l_Lean_Syntax_isOfKind(v_x_2598_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec(v_x_2598_);
v___x_2603_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_ctor_set(v___x_2604_, 1, v_a_2600_);
return v___x_2604_;
}
else
{
lean_object* v___x_2605_; lean_object* v_tk_2606_; lean_object* v___x_2607_; 
v___x_2605_ = lean_unsigned_to_nat(0u);
v_tk_2606_ = l_Lean_Syntax_getArg(v_x_2598_, v___x_2605_);
v___x_2607_ = l_Lean_Fmt_fmt(v_tk_2606_, v_a_2599_, v_a_2600_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v_a_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v_ids_2612_; lean_object* v___x_2613_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
v_a_2609_ = lean_ctor_get(v___x_2607_, 1);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2607_, 2);
v___x_2610_ = lean_unsigned_to_nat(1u);
v___x_2611_ = l_Lean_Syntax_getArg(v_x_2598_, v___x_2610_);
lean_dec(v_x_2598_);
v_ids_2612_ = l_Lean_Syntax_getArgs(v___x_2611_);
lean_dec(v___x_2611_);
v___x_2613_ = l_Lean_Fmt_fmtArray___redArg(v_ids_2612_, v_a_2599_, v_a_2609_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2628_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_a_2615_ = lean_ctor_get(v___x_2613_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2617_ = v___x_2613_;
v_isShared_2618_ = v_isSharedCheck_2628_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2628_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2619_ = lean_mk_empty_array_with_capacity(v___x_2610_);
v___x_2620_ = lean_array_push(v___x_2619_, v_a_2608_);
v___x_2621_ = l_Array_append___redArg(v___x_2620_, v_a_2614_);
lean_dec(v_a_2614_);
v___x_2622_ = 0;
v___x_2623_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2623_, 0, v___x_2602_);
lean_ctor_set_uint8(v___x_2623_, 1, v___x_2622_);
lean_ctor_set_uint8(v___x_2623_, 2, v___x_2622_);
lean_ctor_set_uint8(v___x_2623_, 3, v___x_2622_);
v___x_2624_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2621_, v___x_2623_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2624_);
v___x_2626_ = v___x_2617_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_a_2615_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_a_2608_);
v_a_2629_ = lean_ctor_get(v___x_2613_, 0);
v_a_2630_ = lean_ctor_get(v___x_2613_, 1);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2613_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_inc(v_a_2629_);
lean_dec(v___x_2613_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2629_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_dec(v_x_2598_);
return v___x_2607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCommandCodeAction___boxed(lean_object* v_x_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_Fmt_fmtCommandCodeAction(v_x_2638_, v_a_2639_, v_a_2640_);
lean_dec_ref(v_a_2639_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1(){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2648_ = l_Lean_Fmt_fmtAttribute;
v___x_2649_ = ((lean_object*)(l_Lean_Fmt_fmtCommandCodeAction___closed__1));
v___x_2650_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___closed__1));
v___x_2651_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCommandCodeAction___boxed), 3, 0);
v___x_2652_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2648_, v___x_2649_, v___x_2650_, v___x_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1___boxed(lean_object* v_a_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1();
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCommandCodeAction(lean_object* v_x_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2662_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinCommandCodeAction___closed__1));
lean_inc(v_x_2659_);
v___x_2663_ = l_Lean_Syntax_isOfKind(v_x_2659_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_dec(v_x_2659_);
v___x_2664_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
lean_ctor_set(v___x_2665_, 1, v_a_2661_);
return v___x_2665_;
}
else
{
lean_object* v___x_2666_; lean_object* v_tk_2667_; lean_object* v___x_2668_; 
v___x_2666_ = lean_unsigned_to_nat(0u);
v_tk_2667_ = l_Lean_Syntax_getArg(v_x_2659_, v___x_2666_);
v___x_2668_ = l_Lean_Fmt_fmt(v_tk_2667_, v_a_2660_, v_a_2661_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v_a_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v_ids_2673_; lean_object* v___x_2674_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
v_a_2670_ = lean_ctor_get(v___x_2668_, 1);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2668_, 2);
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_2672_ = l_Lean_Syntax_getArg(v_x_2659_, v___x_2671_);
lean_dec(v_x_2659_);
v_ids_2673_ = l_Lean_Syntax_getArgs(v___x_2672_);
lean_dec(v___x_2672_);
v___x_2674_ = l_Lean_Fmt_fmtArray___redArg(v_ids_2673_, v_a_2660_, v_a_2670_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2689_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
v_a_2676_ = lean_ctor_get(v___x_2674_, 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2678_ = v___x_2674_;
v_isShared_2679_ = v_isSharedCheck_2689_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_inc(v_a_2675_);
lean_dec(v___x_2674_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2689_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2680_ = lean_mk_empty_array_with_capacity(v___x_2671_);
v___x_2681_ = lean_array_push(v___x_2680_, v_a_2669_);
v___x_2682_ = l_Array_append___redArg(v___x_2681_, v_a_2675_);
lean_dec(v_a_2675_);
v___x_2683_ = 0;
v___x_2684_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2684_, 0, v___x_2663_);
lean_ctor_set_uint8(v___x_2684_, 1, v___x_2683_);
lean_ctor_set_uint8(v___x_2684_, 2, v___x_2683_);
lean_ctor_set_uint8(v___x_2684_, 3, v___x_2683_);
v___x_2685_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_2682_, v___x_2684_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2685_);
v___x_2687_ = v___x_2678_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_a_2676_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_a_2669_);
v_a_2690_ = lean_ctor_get(v___x_2674_, 0);
v_a_2691_ = lean_ctor_get(v___x_2674_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2674_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_inc(v_a_2690_);
lean_dec(v___x_2674_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2690_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
else
{
lean_dec(v_x_2659_);
return v___x_2668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBuiltinCommandCodeAction___boxed(lean_object* v_x_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_Fmt_fmtBuiltinCommandCodeAction(v_x_2699_, v_a_2700_, v_a_2701_);
lean_dec_ref(v_a_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1(){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2709_ = l_Lean_Fmt_fmtAttribute;
v___x_2710_ = ((lean_object*)(l_Lean_Fmt_fmtBuiltinCommandCodeAction___closed__1));
v___x_2711_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___closed__1));
v___x_2712_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtBuiltinCommandCodeAction___boxed), 3, 0);
v___x_2713_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2709_, v___x_2710_, v___x_2711_, v___x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1___boxed(lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1();
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunDoSeqCmd(lean_object* v_tk_2716_, lean_object* v_doSeq_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_Fmt_fmt(v_tk_2716_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v_a_2722_; lean_object* v___x_2723_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
v_a_2722_ = lean_ctor_get(v___x_2720_, 1);
lean_inc(v_a_2722_);
lean_dec_ref_known(v___x_2720_, 2);
v___x_2723_ = l_Lean_Fmt_fmt(v_doSeq_2717_, v_a_2718_, v_a_2722_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2734_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_a_2725_ = lean_ctor_get(v___x_2723_, 1);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2727_ = v___x_2723_;
v_isShared_2728_ = v_isSharedCheck_2734_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2734_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
uint8_t v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2729_ = 1;
v___x_2730_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_a_2721_, v_a_2724_, v___x_2729_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2730_);
v___x_2732_ = v___x_2727_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_a_2725_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
else
{
lean_dec(v_a_2721_);
return v___x_2723_;
}
}
else
{
lean_dec(v_doSeq_2717_);
return v___x_2720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunDoSeqCmd___boxed(lean_object* v_tk_2735_, lean_object* v_doSeq_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Fmt_fmtRunDoSeqCmd(v_tk_2735_, v_doSeq_2736_, v_a_2737_, v_a_2738_);
lean_dec_ref(v_a_2737_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunCmd(lean_object* v_x_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___x_2747_; uint8_t v___x_2748_; 
v___x_2747_ = ((lean_object*)(l_Lean_Fmt_fmtRunCmd___closed__1));
lean_inc(v_x_2744_);
v___x_2748_ = l_Lean_Syntax_isOfKind(v_x_2744_, v___x_2747_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_dec(v_x_2744_);
v___x_2749_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
lean_ctor_set(v___x_2750_, 1, v_a_2746_);
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; lean_object* v_tk_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2751_ = lean_unsigned_to_nat(0u);
v_tk_2752_ = l_Lean_Syntax_getArg(v_x_2744_, v___x_2751_);
v___x_2753_ = lean_unsigned_to_nat(1u);
v___x_2754_ = l_Lean_Syntax_getArg(v_x_2744_, v___x_2753_);
lean_dec(v_x_2744_);
v___x_2755_ = l_Lean_Fmt_fmtRunDoSeqCmd(v_tk_2752_, v___x_2754_, v_a_2745_, v_a_2746_);
return v___x_2755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunCmd___boxed(lean_object* v_x_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Fmt_fmtRunCmd(v_x_2756_, v_a_2757_, v_a_2758_);
lean_dec_ref(v_a_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1(){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2766_ = l_Lean_Fmt_fmtAttribute;
v___x_2767_ = ((lean_object*)(l_Lean_Fmt_fmtRunCmd___closed__1));
v___x_2768_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___closed__1));
v___x_2769_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRunCmd___boxed), 3, 0);
v___x_2770_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2766_, v___x_2767_, v___x_2768_, v___x_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1___boxed(lean_object* v_a_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1();
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunElab(lean_object* v_x_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2780_; uint8_t v___x_2781_; 
v___x_2780_ = ((lean_object*)(l_Lean_Fmt_fmtRunElab___closed__1));
lean_inc(v_x_2777_);
v___x_2781_ = l_Lean_Syntax_isOfKind(v_x_2777_, v___x_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_dec(v_x_2777_);
v___x_2782_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v_a_2779_);
return v___x_2783_;
}
else
{
lean_object* v___x_2784_; lean_object* v_tk_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2784_ = lean_unsigned_to_nat(0u);
v_tk_2785_ = l_Lean_Syntax_getArg(v_x_2777_, v___x_2784_);
v___x_2786_ = lean_unsigned_to_nat(1u);
v___x_2787_ = l_Lean_Syntax_getArg(v_x_2777_, v___x_2786_);
lean_dec(v_x_2777_);
v___x_2788_ = l_Lean_Fmt_fmtRunDoSeqCmd(v_tk_2785_, v___x_2787_, v_a_2778_, v_a_2779_);
return v___x_2788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunElab___boxed(lean_object* v_x_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_Fmt_fmtRunElab(v_x_2789_, v_a_2790_, v_a_2791_);
lean_dec_ref(v_a_2790_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1(){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2799_ = l_Lean_Fmt_fmtAttribute;
v___x_2800_ = ((lean_object*)(l_Lean_Fmt_fmtRunElab___closed__1));
v___x_2801_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___closed__1));
v___x_2802_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRunElab___boxed), 3, 0);
v___x_2803_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2799_, v___x_2800_, v___x_2801_, v___x_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1___boxed(lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1();
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunMeta(lean_object* v_x_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2813_ = ((lean_object*)(l_Lean_Fmt_fmtRunMeta___closed__1));
lean_inc(v_x_2810_);
v___x_2814_ = l_Lean_Syntax_isOfKind(v_x_2810_, v___x_2813_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_dec(v_x_2810_);
v___x_2815_ = l_Lean_Fmt_Error_partialFormatter;
v___x_2816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
lean_ctor_set(v___x_2816_, 1, v_a_2812_);
return v___x_2816_;
}
else
{
lean_object* v___x_2817_; lean_object* v_tk_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2817_ = lean_unsigned_to_nat(0u);
v_tk_2818_ = l_Lean_Syntax_getArg(v_x_2810_, v___x_2817_);
v___x_2819_ = lean_unsigned_to_nat(1u);
v___x_2820_ = l_Lean_Syntax_getArg(v_x_2810_, v___x_2819_);
lean_dec(v_x_2810_);
v___x_2821_ = l_Lean_Fmt_fmtRunDoSeqCmd(v_tk_2818_, v___x_2820_, v_a_2811_, v_a_2812_);
return v___x_2821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRunMeta___boxed(lean_object* v_x_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Fmt_fmtRunMeta(v_x_2822_, v_a_2823_, v_a_2824_);
lean_dec_ref(v_a_2823_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1(){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2832_ = l_Lean_Fmt_fmtAttribute;
v___x_2833_ = ((lean_object*)(l_Lean_Fmt_fmtRunMeta___closed__1));
v___x_2834_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___closed__1));
v___x_2835_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRunMeta___boxed), 3, 0);
v___x_2836_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2832_, v___x_2833_, v___x_2834_, v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1___boxed(lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1();
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__1(size_t v_sz_2839_, size_t v_i_2840_, lean_object* v_bs_2841_){
_start:
{
uint8_t v___x_2842_; 
v___x_2842_ = lean_usize_dec_lt(v_i_2840_, v_sz_2839_);
if (v___x_2842_ == 0)
{
return v_bs_2841_;
}
else
{
lean_object* v_v_2843_; lean_object* v_snd_2844_; lean_object* v_snd_2845_; lean_object* v_snd_2846_; lean_object* v_snd_2847_; lean_object* v___x_2848_; lean_object* v_bs_x27_2849_; size_t v___x_2850_; size_t v___x_2851_; lean_object* v___x_2852_; 
v_v_2843_ = lean_array_uget_borrowed(v_bs_2841_, v_i_2840_);
v_snd_2844_ = lean_ctor_get(v_v_2843_, 1);
v_snd_2845_ = lean_ctor_get(v_snd_2844_, 1);
v_snd_2846_ = lean_ctor_get(v_snd_2845_, 1);
v_snd_2847_ = lean_ctor_get(v_snd_2846_, 1);
lean_inc(v_snd_2847_);
v___x_2848_ = lean_unsigned_to_nat(0u);
v_bs_x27_2849_ = lean_array_uset(v_bs_2841_, v_i_2840_, v___x_2848_);
v___x_2850_ = ((size_t)1ULL);
v___x_2851_ = lean_usize_add(v_i_2840_, v___x_2850_);
v___x_2852_ = lean_array_uset(v_bs_x27_2849_, v_i_2840_, v_snd_2847_);
v_i_2840_ = v___x_2851_;
v_bs_2841_ = v___x_2852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__1___boxed(lean_object* v_sz_2854_, lean_object* v_i_2855_, lean_object* v_bs_2856_){
_start:
{
size_t v_sz_boxed_2857_; size_t v_i_boxed_2858_; lean_object* v_res_2859_; 
v_sz_boxed_2857_ = lean_unbox_usize(v_sz_2854_);
lean_dec(v_sz_2854_);
v_i_boxed_2858_ = lean_unbox_usize(v_i_2855_);
lean_dec(v_i_2855_);
v_res_2859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__1(v_sz_boxed_2857_, v_i_boxed_2858_, v_bs_2856_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__5(size_t v_sz_2860_, size_t v_i_2861_, lean_object* v_bs_2862_){
_start:
{
uint8_t v___x_2863_; 
v___x_2863_ = lean_usize_dec_lt(v_i_2861_, v_sz_2860_);
if (v___x_2863_ == 0)
{
return v_bs_2862_;
}
else
{
lean_object* v_v_2864_; lean_object* v_fst_2865_; lean_object* v___x_2866_; lean_object* v_bs_x27_2867_; size_t v___x_2868_; size_t v___x_2869_; lean_object* v___x_2870_; 
v_v_2864_ = lean_array_uget_borrowed(v_bs_2862_, v_i_2861_);
v_fst_2865_ = lean_ctor_get(v_v_2864_, 0);
lean_inc(v_fst_2865_);
v___x_2866_ = lean_unsigned_to_nat(0u);
v_bs_x27_2867_ = lean_array_uset(v_bs_2862_, v_i_2861_, v___x_2866_);
v___x_2868_ = ((size_t)1ULL);
v___x_2869_ = lean_usize_add(v_i_2861_, v___x_2868_);
v___x_2870_ = lean_array_uset(v_bs_x27_2867_, v_i_2861_, v_fst_2865_);
v_i_2861_ = v___x_2869_;
v_bs_2862_ = v___x_2870_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__5___boxed(lean_object* v_sz_2872_, lean_object* v_i_2873_, lean_object* v_bs_2874_){
_start:
{
size_t v_sz_boxed_2875_; size_t v_i_boxed_2876_; lean_object* v_res_2877_; 
v_sz_boxed_2875_ = lean_unbox_usize(v_sz_2872_);
lean_dec(v_sz_2872_);
v_i_boxed_2876_ = lean_unbox_usize(v_i_2873_);
lean_dec(v_i_2873_);
v_res_2877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__5(v_sz_boxed_2875_, v_i_boxed_2876_, v_bs_2874_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__2(size_t v_sz_2878_, size_t v_i_2879_, lean_object* v_bs_2880_){
_start:
{
uint8_t v___x_2881_; 
v___x_2881_ = lean_usize_dec_lt(v_i_2879_, v_sz_2878_);
if (v___x_2881_ == 0)
{
return v_bs_2880_;
}
else
{
lean_object* v_v_2882_; lean_object* v_snd_2883_; lean_object* v_snd_2884_; lean_object* v_snd_2885_; lean_object* v_fst_2886_; lean_object* v___x_2887_; lean_object* v_bs_x27_2888_; size_t v___x_2889_; size_t v___x_2890_; lean_object* v___x_2891_; 
v_v_2882_ = lean_array_uget_borrowed(v_bs_2880_, v_i_2879_);
v_snd_2883_ = lean_ctor_get(v_v_2882_, 1);
v_snd_2884_ = lean_ctor_get(v_snd_2883_, 1);
v_snd_2885_ = lean_ctor_get(v_snd_2884_, 1);
v_fst_2886_ = lean_ctor_get(v_snd_2885_, 0);
lean_inc(v_fst_2886_);
v___x_2887_ = lean_unsigned_to_nat(0u);
v_bs_x27_2888_ = lean_array_uset(v_bs_2880_, v_i_2879_, v___x_2887_);
v___x_2889_ = ((size_t)1ULL);
v___x_2890_ = lean_usize_add(v_i_2879_, v___x_2889_);
v___x_2891_ = lean_array_uset(v_bs_x27_2888_, v_i_2879_, v_fst_2886_);
v_i_2879_ = v___x_2890_;
v_bs_2880_ = v___x_2891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__2___boxed(lean_object* v_sz_2893_, lean_object* v_i_2894_, lean_object* v_bs_2895_){
_start:
{
size_t v_sz_boxed_2896_; size_t v_i_boxed_2897_; lean_object* v_res_2898_; 
v_sz_boxed_2896_ = lean_unbox_usize(v_sz_2893_);
lean_dec(v_sz_2893_);
v_i_boxed_2897_ = lean_unbox_usize(v_i_2894_);
lean_dec(v_i_2894_);
v_res_2898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__2(v_sz_boxed_2896_, v_i_boxed_2897_, v_bs_2895_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__4(size_t v_sz_2899_, size_t v_i_2900_, lean_object* v_bs_2901_){
_start:
{
uint8_t v___x_2902_; 
v___x_2902_ = lean_usize_dec_lt(v_i_2900_, v_sz_2899_);
if (v___x_2902_ == 0)
{
return v_bs_2901_;
}
else
{
lean_object* v_v_2903_; lean_object* v_snd_2904_; lean_object* v_fst_2905_; lean_object* v___x_2906_; lean_object* v_bs_x27_2907_; size_t v___x_2908_; size_t v___x_2909_; lean_object* v___x_2910_; 
v_v_2903_ = lean_array_uget_borrowed(v_bs_2901_, v_i_2900_);
v_snd_2904_ = lean_ctor_get(v_v_2903_, 1);
v_fst_2905_ = lean_ctor_get(v_snd_2904_, 0);
lean_inc(v_fst_2905_);
v___x_2906_ = lean_unsigned_to_nat(0u);
v_bs_x27_2907_ = lean_array_uset(v_bs_2901_, v_i_2900_, v___x_2906_);
v___x_2908_ = ((size_t)1ULL);
v___x_2909_ = lean_usize_add(v_i_2900_, v___x_2908_);
v___x_2910_ = lean_array_uset(v_bs_x27_2907_, v_i_2900_, v_fst_2905_);
v_i_2900_ = v___x_2909_;
v_bs_2901_ = v___x_2910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__4___boxed(lean_object* v_sz_2912_, lean_object* v_i_2913_, lean_object* v_bs_2914_){
_start:
{
size_t v_sz_boxed_2915_; size_t v_i_boxed_2916_; lean_object* v_res_2917_; 
v_sz_boxed_2915_ = lean_unbox_usize(v_sz_2912_);
lean_dec(v_sz_2912_);
v_i_boxed_2916_ = lean_unbox_usize(v_i_2913_);
lean_dec(v_i_2913_);
v_res_2917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__4(v_sz_boxed_2915_, v_i_boxed_2916_, v_bs_2914_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__3(size_t v_sz_2918_, size_t v_i_2919_, lean_object* v_bs_2920_){
_start:
{
uint8_t v___x_2921_; 
v___x_2921_ = lean_usize_dec_lt(v_i_2919_, v_sz_2918_);
if (v___x_2921_ == 0)
{
return v_bs_2920_;
}
else
{
lean_object* v_v_2922_; lean_object* v_snd_2923_; lean_object* v_snd_2924_; lean_object* v_fst_2925_; lean_object* v___x_2926_; lean_object* v_bs_x27_2927_; size_t v___x_2928_; size_t v___x_2929_; lean_object* v___x_2930_; 
v_v_2922_ = lean_array_uget_borrowed(v_bs_2920_, v_i_2919_);
v_snd_2923_ = lean_ctor_get(v_v_2922_, 1);
v_snd_2924_ = lean_ctor_get(v_snd_2923_, 1);
v_fst_2925_ = lean_ctor_get(v_snd_2924_, 0);
lean_inc(v_fst_2925_);
v___x_2926_ = lean_unsigned_to_nat(0u);
v_bs_x27_2927_ = lean_array_uset(v_bs_2920_, v_i_2919_, v___x_2926_);
v___x_2928_ = ((size_t)1ULL);
v___x_2929_ = lean_usize_add(v_i_2919_, v___x_2928_);
v___x_2930_ = lean_array_uset(v_bs_x27_2927_, v_i_2919_, v_fst_2925_);
v_i_2919_ = v___x_2929_;
v_bs_2920_ = v___x_2930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__3___boxed(lean_object* v_sz_2932_, lean_object* v_i_2933_, lean_object* v_bs_2934_){
_start:
{
size_t v_sz_boxed_2935_; size_t v_i_boxed_2936_; lean_object* v_res_2937_; 
v_sz_boxed_2935_ = lean_unbox_usize(v_sz_2932_);
lean_dec(v_sz_2932_);
v_i_boxed_2936_ = lean_unbox_usize(v_i_2933_);
lean_dec(v_i_2933_);
v_res_2937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__3(v_sz_boxed_2935_, v_i_boxed_2936_, v_bs_2934_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0(size_t v_sz_2941_, size_t v_i_2942_, lean_object* v_bs_2943_){
_start:
{
uint8_t v___x_2944_; 
v___x_2944_ = lean_usize_dec_lt(v_i_2942_, v_sz_2941_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v_bs_2943_);
return v___x_2945_;
}
else
{
lean_object* v_v_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v_v_2946_ = lean_array_uget(v_bs_2943_, v_i_2942_);
v___x_2947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0___closed__1));
lean_inc(v_v_2946_);
v___x_2948_ = l_Lean_Syntax_isOfKind(v_v_2946_, v___x_2947_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
lean_dec(v_v_2946_);
lean_dec_ref(v_bs_2943_);
v___x_2949_ = lean_box(0);
return v___x_2949_;
}
else
{
lean_object* v___x_2950_; lean_object* v_ids_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2950_ = lean_unsigned_to_nat(1u);
v_ids_2951_ = l_Lean_Syntax_getArg(v_v_2946_, v___x_2950_);
v___x_2952_ = ((lean_object*)(l_Lean_Fmt_fmtBinderIdent___closed__6));
lean_inc(v_ids_2951_);
v___x_2953_ = l_Lean_Syntax_isOfKind(v_ids_2951_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; 
lean_dec(v_ids_2951_);
lean_dec(v_v_2946_);
lean_dec_ref(v_bs_2943_);
v___x_2954_ = lean_box(0);
return v___x_2954_;
}
else
{
lean_object* v___x_2955_; lean_object* v_bs_x27_2956_; lean_object* v_lbTks_2957_; lean_object* v___x_2958_; lean_object* v_colonEqTks_2959_; lean_object* v___x_2960_; lean_object* v_ts_2961_; lean_object* v___x_2962_; lean_object* v_rbTks_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; size_t v___x_2968_; size_t v___x_2969_; lean_object* v___x_2970_; 
v___x_2955_ = lean_unsigned_to_nat(0u);
v_bs_x27_2956_ = lean_array_uset(v_bs_2943_, v_i_2942_, v___x_2955_);
v_lbTks_2957_ = l_Lean_Syntax_getArg(v_v_2946_, v___x_2955_);
v___x_2958_ = lean_unsigned_to_nat(2u);
v_colonEqTks_2959_ = l_Lean_Syntax_getArg(v_v_2946_, v___x_2958_);
v___x_2960_ = lean_unsigned_to_nat(3u);
v_ts_2961_ = l_Lean_Syntax_getArg(v_v_2946_, v___x_2960_);
v___x_2962_ = lean_unsigned_to_nat(4u);
v_rbTks_2963_ = l_Lean_Syntax_getArg(v_v_2946_, v___x_2962_);
lean_dec(v_v_2946_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_ts_2961_);
lean_ctor_set(v___x_2964_, 1, v_rbTks_2963_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v_colonEqTks_2959_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v_ids_2951_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v_lbTks_2957_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = ((size_t)1ULL);
v___x_2969_ = lean_usize_add(v_i_2942_, v___x_2968_);
v___x_2970_ = lean_array_uset(v_bs_x27_2956_, v_i_2942_, v___x_2967_);
v_i_2942_ = v___x_2969_;
v_bs_2943_ = v___x_2970_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0___boxed(lean_object* v_sz_2972_, lean_object* v_i_2973_, lean_object* v_bs_2974_){
_start:
{
size_t v_sz_boxed_2975_; size_t v_i_boxed_2976_; lean_object* v_res_2977_; 
v_sz_boxed_2975_ = lean_unbox_usize(v_sz_2972_);
lean_dec(v_sz_2972_);
v_i_boxed_2976_ = lean_unbox_usize(v_i_2973_);
lean_dec(v_i_2973_);
v_res_2977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0(v_sz_boxed_2975_, v_i_boxed_2976_, v_bs_2974_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtReduceConfig_spec__6(lean_object* v_as_2978_, size_t v_sz_2979_, size_t v_i_2980_, lean_object* v_b_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
uint8_t v___x_2984_; 
v___x_2984_ = lean_usize_dec_lt(v_i_2980_, v_sz_2979_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v_b_2981_);
lean_ctor_set(v___x_2985_, 1, v___y_2983_);
return v___x_2985_;
}
else
{
lean_object* v_snd_2986_; lean_object* v_snd_2987_; lean_object* v_snd_2988_; lean_object* v_snd_2989_; lean_object* v_fst_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3158_; 
v_snd_2986_ = lean_ctor_get(v_b_2981_, 1);
lean_inc(v_snd_2986_);
v_snd_2987_ = lean_ctor_get(v_snd_2986_, 1);
lean_inc(v_snd_2987_);
v_snd_2988_ = lean_ctor_get(v_snd_2987_, 1);
lean_inc(v_snd_2988_);
v_snd_2989_ = lean_ctor_get(v_snd_2988_, 1);
lean_inc(v_snd_2989_);
v_fst_2990_ = lean_ctor_get(v_b_2981_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_b_2981_);
if (v_isSharedCheck_3158_ == 0)
{
lean_object* v_unused_3159_; 
v_unused_3159_ = lean_ctor_get(v_b_2981_, 1);
lean_dec(v_unused_3159_);
v___x_2992_ = v_b_2981_;
v_isShared_2993_ = v_isSharedCheck_3158_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_fst_2990_);
lean_dec(v_b_2981_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3158_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v_fst_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3156_; 
v_fst_2994_ = lean_ctor_get(v_snd_2986_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_snd_2986_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; 
v_unused_3157_ = lean_ctor_get(v_snd_2986_, 1);
lean_dec(v_unused_3157_);
v___x_2996_ = v_snd_2986_;
v_isShared_2997_ = v_isSharedCheck_3156_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_fst_2994_);
lean_dec(v_snd_2986_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3156_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v_fst_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3154_; 
v_fst_2998_ = lean_ctor_get(v_snd_2987_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_snd_2987_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; 
v_unused_3155_ = lean_ctor_get(v_snd_2987_, 1);
lean_dec(v_unused_3155_);
v___x_3000_ = v_snd_2987_;
v_isShared_3001_ = v_isSharedCheck_3154_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_fst_2998_);
lean_dec(v_snd_2987_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3154_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v_fst_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3152_; 
v_fst_3002_ = lean_ctor_get(v_snd_2988_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_snd_2988_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; 
v_unused_3153_ = lean_ctor_get(v_snd_2988_, 1);
lean_dec(v_unused_3153_);
v___x_3004_ = v_snd_2988_;
v_isShared_3005_ = v_isSharedCheck_3152_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_fst_3002_);
lean_dec(v_snd_2988_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3152_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v_array_3006_; lean_object* v_start_3007_; lean_object* v_stop_3008_; uint8_t v___x_3009_; 
v_array_3006_ = lean_ctor_get(v_snd_2989_, 0);
v_start_3007_ = lean_ctor_get(v_snd_2989_, 1);
v_stop_3008_ = lean_ctor_get(v_snd_2989_, 2);
v___x_3009_ = lean_nat_dec_lt(v_start_3007_, v_stop_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3011_; 
if (v_isShared_3005_ == 0)
{
v___x_3011_ = v___x_3004_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_fst_3002_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_snd_2989_);
v___x_3011_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3013_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v___x_3011_);
v___x_3013_ = v___x_3000_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_fst_2998_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3015_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 1, v___x_3013_);
v___x_3015_ = v___x_2996_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_fst_2994_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3017_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_3015_);
v___x_3017_ = v___x_2992_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_fst_2990_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v___x_3015_);
v___x_3017_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___y_2983_);
return v___x_3018_;
}
}
}
}
}
else
{
lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3148_; 
lean_inc(v_stop_3008_);
lean_inc(v_start_3007_);
lean_inc_ref(v_array_3006_);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_snd_2989_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; lean_object* v_unused_3150_; lean_object* v_unused_3151_; 
v_unused_3149_ = lean_ctor_get(v_snd_2989_, 2);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v_snd_2989_, 1);
lean_dec(v_unused_3150_);
v_unused_3151_ = lean_ctor_get(v_snd_2989_, 0);
lean_dec(v_unused_3151_);
v___x_3024_ = v_snd_2989_;
v_isShared_3025_ = v_isSharedCheck_3148_;
goto v_resetjp_3023_;
}
else
{
lean_dec(v_snd_2989_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3148_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v_array_3026_; lean_object* v_start_3027_; lean_object* v_stop_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3033_; 
v_array_3026_ = lean_ctor_get(v_fst_3002_, 0);
v_start_3027_ = lean_ctor_get(v_fst_3002_, 1);
v_stop_3028_ = lean_ctor_get(v_fst_3002_, 2);
v___x_3029_ = lean_array_fget(v_array_3006_, v_start_3007_);
v___x_3030_ = lean_unsigned_to_nat(1u);
v___x_3031_ = lean_nat_add(v_start_3007_, v___x_3030_);
lean_dec(v_start_3007_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 1, v___x_3031_);
v___x_3033_ = v___x_3024_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_array_3006_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_stop_3008_);
v___x_3033_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
uint8_t v___x_3034_; 
v___x_3034_ = lean_nat_dec_lt(v_start_3027_, v_stop_3028_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3036_; 
lean_dec(v___x_3029_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 1, v___x_3033_);
v___x_3036_ = v___x_3004_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_fst_3002_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v___x_3033_);
v___x_3036_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3038_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v___x_3036_);
v___x_3038_ = v___x_3000_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_fst_2998_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3040_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 1, v___x_3038_);
v___x_3040_ = v___x_2996_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_fst_2994_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3042_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_3040_);
v___x_3042_ = v___x_2992_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_fst_2990_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
lean_ctor_set(v___x_3043_, 1, v___y_2983_);
return v___x_3043_;
}
}
}
}
}
else
{
lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3143_; 
lean_inc(v_stop_3028_);
lean_inc(v_start_3027_);
lean_inc_ref(v_array_3026_);
v_isSharedCheck_3143_ = !lean_is_exclusive(v_fst_3002_);
if (v_isSharedCheck_3143_ == 0)
{
lean_object* v_unused_3144_; lean_object* v_unused_3145_; lean_object* v_unused_3146_; 
v_unused_3144_ = lean_ctor_get(v_fst_3002_, 2);
lean_dec(v_unused_3144_);
v_unused_3145_ = lean_ctor_get(v_fst_3002_, 1);
lean_dec(v_unused_3145_);
v_unused_3146_ = lean_ctor_get(v_fst_3002_, 0);
lean_dec(v_unused_3146_);
v___x_3049_ = v_fst_3002_;
v_isShared_3050_ = v_isSharedCheck_3143_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v_fst_3002_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3143_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_array_3051_; lean_object* v_start_3052_; lean_object* v_stop_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v_array_3051_ = lean_ctor_get(v_fst_2998_, 0);
v_start_3052_ = lean_ctor_get(v_fst_2998_, 1);
v_stop_3053_ = lean_ctor_get(v_fst_2998_, 2);
v___x_3054_ = lean_array_fget(v_array_3026_, v_start_3027_);
v___x_3055_ = lean_nat_add(v_start_3027_, v___x_3030_);
lean_dec(v_start_3027_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 1, v___x_3055_);
v___x_3057_ = v___x_3049_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_array_3026_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v_stop_3028_);
v___x_3057_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_nat_dec_lt(v_start_3052_, v_stop_3053_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3060_; 
lean_dec(v___x_3054_);
lean_dec(v___x_3029_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 1, v___x_3033_);
lean_ctor_set(v___x_3004_, 0, v___x_3057_);
v___x_3060_ = v___x_3004_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v___x_3033_);
v___x_3060_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3062_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v___x_3060_);
v___x_3062_ = v___x_3000_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_fst_2998_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3064_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 1, v___x_3062_);
v___x_3064_ = v___x_2996_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_fst_2994_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3066_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_3064_);
v___x_3066_ = v___x_2992_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_fst_2990_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3067_; 
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v___y_2983_);
return v___x_3067_;
}
}
}
}
}
else
{
lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3138_; 
lean_inc(v_stop_3053_);
lean_inc(v_start_3052_);
lean_inc_ref(v_array_3051_);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_fst_2998_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; lean_object* v_unused_3140_; lean_object* v_unused_3141_; 
v_unused_3139_ = lean_ctor_get(v_fst_2998_, 2);
lean_dec(v_unused_3139_);
v_unused_3140_ = lean_ctor_get(v_fst_2998_, 1);
lean_dec(v_unused_3140_);
v_unused_3141_ = lean_ctor_get(v_fst_2998_, 0);
lean_dec(v_unused_3141_);
v___x_3073_ = v_fst_2998_;
v_isShared_3074_ = v_isSharedCheck_3138_;
goto v_resetjp_3072_;
}
else
{
lean_dec(v_fst_2998_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3138_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v_array_3075_; lean_object* v_start_3076_; lean_object* v_stop_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3081_; 
v_array_3075_ = lean_ctor_get(v_fst_2994_, 0);
v_start_3076_ = lean_ctor_get(v_fst_2994_, 1);
v_stop_3077_ = lean_ctor_get(v_fst_2994_, 2);
v___x_3078_ = lean_array_fget(v_array_3051_, v_start_3052_);
v___x_3079_ = lean_nat_add(v_start_3052_, v___x_3030_);
lean_dec(v_start_3052_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 1, v___x_3079_);
v___x_3081_ = v___x_3073_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_array_3051_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_stop_3053_);
v___x_3081_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
uint8_t v___x_3082_; 
v___x_3082_ = lean_nat_dec_lt(v_start_3076_, v_stop_3077_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3084_; 
lean_dec(v___x_3078_);
lean_dec(v___x_3054_);
lean_dec(v___x_3029_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 1, v___x_3033_);
lean_ctor_set(v___x_3004_, 0, v___x_3057_);
v___x_3084_ = v___x_3004_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___x_3033_);
v___x_3084_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3086_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v___x_3084_);
lean_ctor_set(v___x_3000_, 0, v___x_3081_);
v___x_3086_ = v___x_3000_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3081_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3088_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 1, v___x_3086_);
v___x_3088_ = v___x_2996_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_fst_2994_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3090_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_3088_);
v___x_3090_ = v___x_2992_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_fst_2990_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3088_);
v___x_3090_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3091_; 
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
lean_ctor_set(v___x_3091_, 1, v___y_2983_);
return v___x_3091_;
}
}
}
}
}
else
{
lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3133_; 
lean_inc(v_stop_3077_);
lean_inc(v_start_3076_);
lean_inc_ref(v_array_3075_);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_fst_2994_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; lean_object* v_unused_3135_; lean_object* v_unused_3136_; 
v_unused_3134_ = lean_ctor_get(v_fst_2994_, 2);
lean_dec(v_unused_3134_);
v_unused_3135_ = lean_ctor_get(v_fst_2994_, 1);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v_fst_2994_, 0);
lean_dec(v_unused_3136_);
v___x_3097_ = v_fst_2994_;
v_isShared_3098_ = v_isSharedCheck_3133_;
goto v_resetjp_3096_;
}
else
{
lean_dec(v_fst_2994_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3133_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v_a_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v_a_3099_ = lean_array_uget_borrowed(v_as_2978_, v_i_2980_);
v___x_3100_ = lean_array_fget_borrowed(v_array_3075_, v_start_3076_);
lean_inc(v___x_3100_);
lean_inc(v_a_3099_);
v___x_3101_ = l_Lean_Fmt_fmtNamedArgumentTerm(v_a_3099_, v___x_3100_, v___x_3078_, v___x_3054_, v___x_3029_, v___y_2982_, v___y_2983_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v_a_3103_; lean_object* v___x_3104_; lean_object* v___x_3106_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
v_a_3103_ = lean_ctor_get(v___x_3101_, 1);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3101_, 2);
v___x_3104_ = lean_nat_add(v_start_3076_, v___x_3030_);
lean_dec(v_start_3076_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3104_);
v___x_3106_ = v___x_3097_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_array_3075_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_stop_3077_);
v___x_3106_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3107_ = lean_array_push(v_fst_2990_, v_a_3102_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 1, v___x_3033_);
lean_ctor_set(v___x_3004_, 0, v___x_3057_);
v___x_3109_ = v___x_3004_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_3033_);
v___x_3109_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3111_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v___x_3109_);
lean_ctor_set(v___x_3000_, 0, v___x_3081_);
v___x_3111_ = v___x_3000_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3081_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v___x_3109_);
v___x_3111_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3113_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 1, v___x_3111_);
lean_ctor_set(v___x_2996_, 0, v___x_3106_);
v___x_3113_ = v___x_2996_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3115_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_3113_);
lean_ctor_set(v___x_2992_, 0, v___x_3107_);
v___x_3115_ = v___x_2992_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
size_t v___x_3116_; size_t v___x_3117_; 
v___x_3116_ = ((size_t)1ULL);
v___x_3117_ = lean_usize_add(v_i_2980_, v___x_3116_);
v_i_2980_ = v___x_3117_;
v_b_2981_ = v___x_3115_;
v___y_2983_ = v_a_3103_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_del_object(v___x_3097_);
lean_dec_ref(v___x_3081_);
lean_dec(v_stop_3077_);
lean_dec(v_start_3076_);
lean_dec_ref(v_array_3075_);
lean_dec_ref(v___x_3057_);
lean_dec_ref(v___x_3033_);
lean_del_object(v___x_3004_);
lean_del_object(v___x_3000_);
lean_del_object(v___x_2996_);
lean_del_object(v___x_2992_);
lean_dec(v_fst_2990_);
v_a_3124_ = lean_ctor_get(v___x_3101_, 0);
v_a_3125_ = lean_ctor_get(v___x_3101_, 1);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3101_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_inc(v_a_3124_);
lean_dec(v___x_3101_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3124_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtReduceConfig_spec__6___boxed(lean_object* v_as_3160_, lean_object* v_sz_3161_, lean_object* v_i_3162_, lean_object* v_b_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
size_t v_sz_boxed_3166_; size_t v_i_boxed_3167_; lean_object* v_res_3168_; 
v_sz_boxed_3166_ = lean_unbox_usize(v_sz_3161_);
lean_dec(v_sz_3161_);
v_i_boxed_3167_ = lean_unbox_usize(v_i_3162_);
lean_dec(v_i_3162_);
v_res_3168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtReduceConfig_spec__6(v_as_3160_, v_sz_boxed_3166_, v_i_boxed_3167_, v_b_3163_, v___y_3164_, v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec_ref(v_as_3160_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReduceConfig(lean_object* v_c_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_){
_start:
{
lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3176_ = ((lean_object*)(l_Lean_Fmt_fmtReduceConfig___closed__1));
lean_inc(v_c_3173_);
v___x_3177_ = l_Lean_Syntax_isOfKind(v_c_3173_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_dec(v_c_3173_);
v___x_3178_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v_a_3175_);
return v___x_3179_;
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; size_t v_sz_3183_; size_t v___x_3184_; lean_object* v___x_3185_; 
v___x_3180_ = lean_unsigned_to_nat(0u);
v___x_3181_ = l_Lean_Syntax_getArg(v_c_3173_, v___x_3180_);
lean_dec(v_c_3173_);
v___x_3182_ = l_Lean_Syntax_getArgs(v___x_3181_);
lean_dec(v___x_3181_);
v_sz_3183_ = lean_array_size(v___x_3182_);
v___x_3184_ = ((size_t)0ULL);
v___x_3185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__0(v_sz_3183_, v___x_3184_, v___x_3182_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v_a_3175_);
return v___x_3187_;
}
else
{
lean_object* v_val_3188_; size_t v_sz_3189_; lean_object* v_rbTks_3190_; lean_object* v_ts_3191_; lean_object* v_colonEqTks_3192_; lean_object* v_ids_3193_; lean_object* v_lbTks_3194_; lean_object* v_args_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; size_t v_sz_3208_; lean_object* v___x_3209_; 
v_val_3188_ = lean_ctor_get(v___x_3185_, 0);
lean_inc_n(v_val_3188_, 5);
lean_dec_ref_known(v___x_3185_, 1);
v_sz_3189_ = lean_array_size(v_val_3188_);
v_rbTks_3190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__1(v_sz_3189_, v___x_3184_, v_val_3188_);
v_ts_3191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__2(v_sz_3189_, v___x_3184_, v_val_3188_);
v_colonEqTks_3192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__3(v_sz_3189_, v___x_3184_, v_val_3188_);
v_ids_3193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__4(v_sz_3189_, v___x_3184_, v_val_3188_);
v_lbTks_3194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtReduceConfig_spec__5(v_sz_3189_, v___x_3184_, v_val_3188_);
v_args_3195_ = ((lean_object*)(l_Lean_Fmt_fmtPipeOperator___closed__0));
v___x_3196_ = lean_array_get_size(v_ids_3193_);
v___x_3197_ = l_Array_toSubarray___redArg(v_ids_3193_, v___x_3180_, v___x_3196_);
v___x_3198_ = lean_array_get_size(v_colonEqTks_3192_);
v___x_3199_ = l_Array_toSubarray___redArg(v_colonEqTks_3192_, v___x_3180_, v___x_3198_);
v___x_3200_ = lean_array_get_size(v_ts_3191_);
v___x_3201_ = l_Array_toSubarray___redArg(v_ts_3191_, v___x_3180_, v___x_3200_);
v___x_3202_ = lean_array_get_size(v_rbTks_3190_);
v___x_3203_ = l_Array_toSubarray___redArg(v_rbTks_3190_, v___x_3180_, v___x_3202_);
v___x_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3201_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3199_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3197_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3207_, 0, v_args_3195_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v_sz_3208_ = lean_array_size(v_lbTks_3194_);
v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_fmtReduceConfig_spec__6(v_lbTks_3194_, v_sz_3208_, v___x_3184_, v___x_3207_, v_a_3174_, v_a_3175_);
lean_dec_ref(v_lbTks_3194_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3219_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
v_a_3211_ = lean_ctor_get(v___x_3209_, 1);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3213_ = v___x_3209_;
v_isShared_3214_ = v_isSharedCheck_3219_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_inc(v_a_3210_);
lean_dec(v___x_3209_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3219_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v_fst_3215_; lean_object* v___x_3217_; 
v_fst_3215_ = lean_ctor_get(v_a_3210_, 0);
lean_inc(v_fst_3215_);
lean_dec(v_a_3210_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v_fst_3215_);
v___x_3217_ = v___x_3213_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_fst_3215_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_a_3211_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
else
{
lean_object* v_a_3220_; lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
v_a_3220_ = lean_ctor_get(v___x_3209_, 0);
v_a_3221_ = lean_ctor_get(v___x_3209_, 1);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3209_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_inc(v_a_3220_);
lean_dec(v___x_3209_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3220_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReduceConfig___boxed(lean_object* v_c_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_Fmt_fmtReduceConfig(v_c_3229_, v_a_3230_, v_a_3231_);
lean_dec_ref(v_a_3230_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReduceCmd(lean_object* v_x_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v___x_3240_; uint8_t v___x_3241_; 
v___x_3240_ = ((lean_object*)(l_Lean_Fmt_fmtReduceCmd___closed__1));
lean_inc(v_x_3237_);
v___x_3241_ = l_Lean_Syntax_isOfKind(v_x_3237_, v___x_3240_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
lean_dec(v_x_3237_);
v___x_3242_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3242_);
lean_ctor_set(v___x_3243_, 1, v_a_3239_);
return v___x_3243_;
}
else
{
lean_object* v___x_3244_; lean_object* v_config_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v___x_3244_ = lean_unsigned_to_nat(1u);
v_config_3245_ = l_Lean_Syntax_getArg(v_x_3237_, v___x_3244_);
v___x_3246_ = ((lean_object*)(l_Lean_Fmt_fmtReduceConfig___closed__1));
lean_inc(v_config_3245_);
v___x_3247_ = l_Lean_Syntax_isOfKind(v_config_3245_, v___x_3246_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
lean_dec(v_config_3245_);
lean_dec(v_x_3237_);
v___x_3248_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
lean_ctor_set(v___x_3249_, 1, v_a_3239_);
return v___x_3249_;
}
else
{
lean_object* v___x_3250_; lean_object* v_tk_3251_; lean_object* v___x_3252_; 
v___x_3250_ = lean_unsigned_to_nat(0u);
v_tk_3251_ = l_Lean_Syntax_getArg(v_x_3237_, v___x_3250_);
v___x_3252_ = l_Lean_Fmt_fmt(v_tk_3251_, v_a_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v_a_3254_; lean_object* v___x_3255_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
v_a_3254_ = lean_ctor_get(v___x_3252_, 1);
lean_inc(v_a_3254_);
lean_dec_ref_known(v___x_3252_, 2);
v___x_3255_ = l_Lean_Fmt_fmtReduceConfig(v_config_3245_, v_a_3238_, v_a_3254_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v_a_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
v_a_3257_ = lean_ctor_get(v___x_3255_, 1);
lean_inc(v_a_3257_);
lean_dec_ref_known(v___x_3255_, 2);
v___x_3258_ = lean_unsigned_to_nat(2u);
v___x_3259_ = l_Lean_Syntax_getArg(v_x_3237_, v___x_3258_);
lean_dec(v_x_3237_);
v___x_3260_ = 0;
v___x_3261_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3261_, 0, v___x_3247_);
lean_ctor_set_uint8(v___x_3261_, 1, v___x_3260_);
lean_ctor_set_uint8(v___x_3261_, 2, v___x_3260_);
lean_ctor_set_uint8(v___x_3261_, 3, v___x_3260_);
v___x_3262_ = l_Lean_Fmt_fmt(v___x_3259_, v_a_3238_, v_a_3257_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3279_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
v_a_3264_ = lean_ctor_get(v___x_3262_, 1);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3266_ = v___x_3262_;
v_isShared_3267_ = v_isSharedCheck_3279_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_inc(v_a_3263_);
lean_dec(v___x_3262_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3279_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3277_; 
v___x_3268_ = lean_mk_empty_array_with_capacity(v___x_3244_);
v___x_3269_ = lean_array_push(v___x_3268_, v_a_3253_);
v___x_3270_ = l_Array_append___redArg(v___x_3269_, v_a_3256_);
lean_dec(v_a_3256_);
lean_inc_ref(v___x_3261_);
v___x_3271_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3270_, v___x_3261_);
v___x_3272_ = lean_mk_empty_array_with_capacity(v___x_3258_);
v___x_3273_ = lean_array_push(v___x_3272_, v___x_3271_);
v___x_3274_ = lean_array_push(v___x_3273_, v_a_3263_);
v___x_3275_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3274_, v___x_3261_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3275_);
v___x_3277_ = v___x_3266_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3275_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_a_3264_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
else
{
lean_dec_ref_known(v___x_3261_, 0);
lean_dec(v_a_3256_);
lean_dec(v_a_3253_);
return v___x_3262_;
}
}
else
{
lean_object* v_a_3280_; lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec(v_a_3253_);
lean_dec(v_x_3237_);
v_a_3280_ = lean_ctor_get(v___x_3255_, 0);
v_a_3281_ = lean_ctor_get(v___x_3255_, 1);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3255_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_inc(v_a_3280_);
lean_dec(v___x_3255_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3280_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
else
{
lean_dec(v_config_3245_);
lean_dec(v_x_3237_);
return v___x_3252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtReduceCmd___boxed(lean_object* v_x_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l_Lean_Fmt_fmtReduceCmd(v_x_3289_, v_a_3290_, v_a_3291_);
lean_dec_ref(v_a_3290_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1(){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3299_ = l_Lean_Fmt_fmtAttribute;
v___x_3300_ = ((lean_object*)(l_Lean_Fmt_fmtReduceCmd___closed__1));
v___x_3301_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___closed__1));
v___x_3302_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtReduceCmd___boxed), 3, 0);
v___x_3303_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3299_, v___x_3300_, v___x_3301_, v___x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1___boxed(lean_object* v_a_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1();
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSetLibrarySuggestions(lean_object* v_x_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v___x_3313_; uint8_t v___x_3314_; 
v___x_3313_ = ((lean_object*)(l_Lean_Fmt_fmtSetLibrarySuggestions___closed__1));
lean_inc(v_x_3310_);
v___x_3314_ = l_Lean_Syntax_isOfKind(v_x_3310_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec(v_x_3310_);
v___x_3315_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
lean_ctor_set(v___x_3316_, 1, v_a_3312_);
return v___x_3316_;
}
else
{
lean_object* v___x_3317_; lean_object* v_tk_3318_; lean_object* v___x_3319_; 
v___x_3317_ = lean_unsigned_to_nat(0u);
v_tk_3318_ = l_Lean_Syntax_getArg(v_x_3310_, v___x_3317_);
v___x_3319_ = l_Lean_Fmt_fmt(v_tk_3318_, v_a_3311_, v_a_3312_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v_a_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
v_a_3321_ = lean_ctor_get(v___x_3319_, 1);
lean_inc(v_a_3321_);
lean_dec_ref_known(v___x_3319_, 2);
v___x_3322_ = lean_unsigned_to_nat(1u);
v___x_3323_ = l_Lean_Syntax_getArg(v_x_3310_, v___x_3322_);
lean_dec(v_x_3310_);
v___x_3324_ = l_Lean_Fmt_fmt(v___x_3323_, v_a_3311_, v_a_3321_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3340_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
v_a_3326_ = lean_ctor_get(v___x_3324_, 1);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3328_ = v___x_3324_;
v_isShared_3329_ = v_isSharedCheck_3340_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_inc(v_a_3325_);
lean_dec(v___x_3324_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3340_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3338_; 
v___x_3330_ = lean_unsigned_to_nat(2u);
v___x_3331_ = lean_mk_empty_array_with_capacity(v___x_3330_);
v___x_3332_ = lean_array_push(v___x_3331_, v_a_3320_);
v___x_3333_ = lean_array_push(v___x_3332_, v_a_3325_);
v___x_3334_ = 0;
v___x_3335_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3335_, 0, v___x_3314_);
lean_ctor_set_uint8(v___x_3335_, 1, v___x_3334_);
lean_ctor_set_uint8(v___x_3335_, 2, v___x_3334_);
lean_ctor_set_uint8(v___x_3335_, 3, v___x_3334_);
v___x_3336_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3333_, v___x_3335_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3336_);
v___x_3338_ = v___x_3328_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_a_3326_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
else
{
lean_dec(v_a_3320_);
return v___x_3324_;
}
}
else
{
lean_dec(v_x_3310_);
return v___x_3319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSetLibrarySuggestions___boxed(lean_object* v_x_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_Fmt_fmtSetLibrarySuggestions(v_x_3341_, v_a_3342_, v_a_3343_);
lean_dec_ref(v_a_3342_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1(){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3351_ = l_Lean_Fmt_fmtAttribute;
v___x_3352_ = ((lean_object*)(l_Lean_Fmt_fmtSetLibrarySuggestions___closed__1));
v___x_3353_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___closed__1));
v___x_3354_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSetLibrarySuggestions___boxed), 3, 0);
v___x_3355_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3351_, v___x_3352_, v___x_3353_, v___x_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1___boxed(lean_object* v_a_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1();
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDiscrTreeKeyCmd(lean_object* v_x_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_){
_start:
{
lean_object* v___x_3366_; uint8_t v___x_3367_; 
v___x_3366_ = ((lean_object*)(l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__1));
lean_inc(v_x_3363_);
v___x_3367_ = l_Lean_Syntax_isOfKind(v_x_3363_, v___x_3366_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec(v_x_3363_);
v___x_3368_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
lean_ctor_set(v___x_3369_, 1, v_a_3365_);
return v___x_3369_;
}
else
{
lean_object* v___x_3370_; lean_object* v_tk_3371_; lean_object* v___x_3372_; 
v___x_3370_ = lean_unsigned_to_nat(0u);
v_tk_3371_ = l_Lean_Syntax_getArg(v_x_3363_, v___x_3370_);
v___x_3372_ = l_Lean_Fmt_fmt(v_tk_3371_, v_a_3364_, v_a_3365_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v_a_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
v_a_3374_ = lean_ctor_get(v___x_3372_, 1);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___x_3372_, 2);
v___x_3375_ = lean_unsigned_to_nat(1u);
v___x_3376_ = l_Lean_Syntax_getArg(v_x_3363_, v___x_3375_);
lean_dec(v_x_3363_);
v___x_3377_ = l_Lean_Fmt_fmt(v___x_3376_, v_a_3364_, v_a_3374_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3393_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
v_a_3379_ = lean_ctor_get(v___x_3377_, 1);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3381_ = v___x_3377_;
v_isShared_3382_ = v_isSharedCheck_3393_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_inc(v_a_3378_);
lean_dec(v___x_3377_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3393_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3383_ = lean_unsigned_to_nat(2u);
v___x_3384_ = lean_mk_empty_array_with_capacity(v___x_3383_);
v___x_3385_ = lean_array_push(v___x_3384_, v_a_3373_);
v___x_3386_ = lean_array_push(v___x_3385_, v_a_3378_);
v___x_3387_ = 0;
v___x_3388_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3388_, 0, v___x_3367_);
lean_ctor_set_uint8(v___x_3388_, 1, v___x_3387_);
lean_ctor_set_uint8(v___x_3388_, 2, v___x_3387_);
lean_ctor_set_uint8(v___x_3388_, 3, v___x_3387_);
v___x_3389_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3386_, v___x_3388_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v___x_3389_);
v___x_3391_ = v___x_3381_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_a_3379_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
else
{
lean_dec(v_a_3373_);
return v___x_3377_;
}
}
else
{
lean_dec(v_x_3363_);
return v___x_3372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDiscrTreeKeyCmd___boxed(lean_object* v_x_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_Fmt_fmtDiscrTreeKeyCmd(v_x_3394_, v_a_3395_, v_a_3396_);
lean_dec_ref(v_a_3395_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1(){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3404_ = l_Lean_Fmt_fmtAttribute;
v___x_3405_ = ((lean_object*)(l_Lean_Fmt_fmtDiscrTreeKeyCmd___closed__1));
v___x_3406_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___closed__1));
v___x_3407_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDiscrTreeKeyCmd___boxed), 3, 0);
v___x_3408_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3404_, v___x_3405_, v___x_3406_, v___x_3407_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1___boxed(lean_object* v_a_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1();
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd(lean_object* v_x_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3419_ = ((lean_object*)(l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__1));
lean_inc(v_x_3416_);
v___x_3420_ = l_Lean_Syntax_isOfKind(v_x_3416_, v___x_3419_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
lean_dec(v_x_3416_);
v___x_3421_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v_a_3418_);
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v_tk_3424_; lean_object* v___x_3425_; 
v___x_3423_ = lean_unsigned_to_nat(0u);
v_tk_3424_ = l_Lean_Syntax_getArg(v_x_3416_, v___x_3423_);
v___x_3425_ = l_Lean_Fmt_fmt(v_tk_3424_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v_a_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
v_a_3427_ = lean_ctor_get(v___x_3425_, 1);
lean_inc(v_a_3427_);
lean_dec_ref_known(v___x_3425_, 2);
v___x_3428_ = lean_unsigned_to_nat(1u);
v___x_3429_ = l_Lean_Syntax_getArg(v_x_3416_, v___x_3428_);
lean_dec(v_x_3416_);
v___x_3430_ = l_Lean_Fmt_fmt(v___x_3429_, v_a_3417_, v_a_3427_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3446_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
v_a_3432_ = lean_ctor_get(v___x_3430_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3434_ = v___x_3430_;
v_isShared_3435_ = v_isSharedCheck_3446_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_inc(v_a_3431_);
lean_dec(v___x_3430_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3446_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; uint8_t v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3436_ = lean_unsigned_to_nat(2u);
v___x_3437_ = lean_mk_empty_array_with_capacity(v___x_3436_);
v___x_3438_ = lean_array_push(v___x_3437_, v_a_3426_);
v___x_3439_ = lean_array_push(v___x_3438_, v_a_3431_);
v___x_3440_ = 0;
v___x_3441_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3441_, 0, v___x_3420_);
lean_ctor_set_uint8(v___x_3441_, 1, v___x_3440_);
lean_ctor_set_uint8(v___x_3441_, 2, v___x_3440_);
lean_ctor_set_uint8(v___x_3441_, 3, v___x_3440_);
v___x_3442_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3439_, v___x_3441_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v___x_3442_);
v___x_3444_ = v___x_3434_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v_a_3432_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
else
{
lean_dec(v_a_3426_);
return v___x_3430_;
}
}
else
{
lean_dec(v_x_3416_);
return v___x_3425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___boxed(lean_object* v_x_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd(v_x_3447_, v_a_3448_, v_a_3449_);
lean_dec_ref(v_a_3448_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1(){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3457_ = l_Lean_Fmt_fmtAttribute;
v___x_3458_ = ((lean_object*)(l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___closed__1));
v___x_3459_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___closed__1));
v___x_3460_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDiscrTreeSimpKeyCmd___boxed), 3, 0);
v___x_3461_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3457_, v___x_3458_, v___x_3459_, v___x_3460_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1___boxed(lean_object* v_a_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1();
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeal(lean_object* v_x_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3472_ = ((lean_object*)(l_Lean_Fmt_fmtSeal___closed__1));
lean_inc(v_x_3469_);
v___x_3473_ = l_Lean_Syntax_isOfKind(v_x_3469_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_dec(v_x_3469_);
v___x_3474_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v_a_3471_);
return v___x_3475_;
}
else
{
lean_object* v___x_3476_; lean_object* v_tk_3477_; lean_object* v___x_3478_; 
v___x_3476_ = lean_unsigned_to_nat(0u);
v_tk_3477_ = l_Lean_Syntax_getArg(v_x_3469_, v___x_3476_);
v___x_3478_ = l_Lean_Fmt_fmt(v_tk_3477_, v_a_3470_, v_a_3471_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v_a_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v_ids_3483_; lean_object* v___x_3484_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
v_a_3480_ = lean_ctor_get(v___x_3478_, 1);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3478_, 2);
v___x_3481_ = lean_unsigned_to_nat(1u);
v___x_3482_ = l_Lean_Syntax_getArg(v_x_3469_, v___x_3481_);
lean_dec(v_x_3469_);
v_ids_3483_ = l_Lean_Syntax_getArgs(v___x_3482_);
lean_dec(v___x_3482_);
v___x_3484_ = l_Lean_Fmt_fmtArray___redArg(v_ids_3483_, v_a_3470_, v_a_3480_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3485_; lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3499_; 
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
v_a_3486_ = lean_ctor_get(v___x_3484_, 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3488_ = v___x_3484_;
v_isShared_3489_ = v_isSharedCheck_3499_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_inc(v_a_3485_);
lean_dec(v___x_3484_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3499_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3490_ = lean_mk_empty_array_with_capacity(v___x_3481_);
v___x_3491_ = lean_array_push(v___x_3490_, v_a_3479_);
v___x_3492_ = l_Array_append___redArg(v___x_3491_, v_a_3485_);
lean_dec(v_a_3485_);
v___x_3493_ = 0;
v___x_3494_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3494_, 0, v___x_3473_);
lean_ctor_set_uint8(v___x_3494_, 1, v___x_3493_);
lean_ctor_set_uint8(v___x_3494_, 2, v___x_3493_);
lean_ctor_set_uint8(v___x_3494_, 3, v___x_3493_);
v___x_3495_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3492_, v___x_3494_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3495_);
v___x_3497_ = v___x_3488_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_a_3486_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec(v_a_3479_);
v_a_3500_ = lean_ctor_get(v___x_3484_, 0);
v_a_3501_ = lean_ctor_get(v___x_3484_, 1);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3484_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_inc(v_a_3500_);
lean_dec(v___x_3484_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3500_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
else
{
lean_dec(v_x_3469_);
return v___x_3478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSeal___boxed(lean_object* v_x_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_Fmt_fmtSeal(v_x_3509_, v_a_3510_, v_a_3511_);
lean_dec_ref(v_a_3510_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1(){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3519_ = l_Lean_Fmt_fmtAttribute;
v___x_3520_ = ((lean_object*)(l_Lean_Fmt_fmtSeal___closed__1));
v___x_3521_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___closed__1));
v___x_3522_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtSeal___boxed), 3, 0);
v___x_3523_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3519_, v___x_3520_, v___x_3521_, v___x_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1___boxed(lean_object* v_a_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1();
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnseal(lean_object* v_x_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v___x_3534_; uint8_t v___x_3535_; 
v___x_3534_ = ((lean_object*)(l_Lean_Fmt_fmtUnseal___closed__1));
lean_inc(v_x_3531_);
v___x_3535_ = l_Lean_Syntax_isOfKind(v_x_3531_, v___x_3534_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_dec(v_x_3531_);
v___x_3536_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
lean_ctor_set(v___x_3537_, 1, v_a_3533_);
return v___x_3537_;
}
else
{
lean_object* v___x_3538_; lean_object* v_tk_3539_; lean_object* v___x_3540_; 
v___x_3538_ = lean_unsigned_to_nat(0u);
v_tk_3539_ = l_Lean_Syntax_getArg(v_x_3531_, v___x_3538_);
v___x_3540_ = l_Lean_Fmt_fmt(v_tk_3539_, v_a_3532_, v_a_3533_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v_a_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v_ids_3545_; lean_object* v___x_3546_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
v_a_3542_ = lean_ctor_get(v___x_3540_, 1);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3540_, 2);
v___x_3543_ = lean_unsigned_to_nat(1u);
v___x_3544_ = l_Lean_Syntax_getArg(v_x_3531_, v___x_3543_);
lean_dec(v_x_3531_);
v_ids_3545_ = l_Lean_Syntax_getArgs(v___x_3544_);
lean_dec(v___x_3544_);
v___x_3546_ = l_Lean_Fmt_fmtArray___redArg(v_ids_3545_, v_a_3532_, v_a_3542_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3561_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
v_a_3548_ = lean_ctor_get(v___x_3546_, 1);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3550_ = v___x_3546_;
v_isShared_3551_ = v_isSharedCheck_3561_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_inc(v_a_3547_);
lean_dec(v___x_3546_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3561_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3552_ = lean_mk_empty_array_with_capacity(v___x_3543_);
v___x_3553_ = lean_array_push(v___x_3552_, v_a_3541_);
v___x_3554_ = l_Array_append___redArg(v___x_3553_, v_a_3547_);
lean_dec(v_a_3547_);
v___x_3555_ = 0;
v___x_3556_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3556_, 0, v___x_3535_);
lean_ctor_set_uint8(v___x_3556_, 1, v___x_3555_);
lean_ctor_set_uint8(v___x_3556_, 2, v___x_3555_);
lean_ctor_set_uint8(v___x_3556_, 3, v___x_3555_);
v___x_3557_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3554_, v___x_3556_);
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 0, v___x_3557_);
v___x_3559_ = v___x_3550_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_a_3548_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec(v_a_3541_);
v_a_3562_ = lean_ctor_get(v___x_3546_, 0);
v_a_3563_ = lean_ctor_get(v___x_3546_, 1);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3546_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_inc(v_a_3562_);
lean_dec(v___x_3546_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3562_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_dec(v_x_3531_);
return v___x_3540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtUnseal___boxed(lean_object* v_x_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_Fmt_fmtUnseal(v_x_3571_, v_a_3572_, v_a_3573_);
lean_dec_ref(v_a_3572_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1(){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3581_ = l_Lean_Fmt_fmtAttribute;
v___x_3582_ = ((lean_object*)(l_Lean_Fmt_fmtUnseal___closed__1));
v___x_3583_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___closed__1));
v___x_3584_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtUnseal___boxed), 3, 0);
v___x_3585_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3581_, v___x_3582_, v___x_3583_, v___x_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1___boxed(lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1();
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeCmd(lean_object* v_x_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v___x_3596_; uint8_t v___x_3597_; 
v___x_3596_ = ((lean_object*)(l_Lean_Fmt_fmtTimeCmd___closed__1));
lean_inc(v_x_3593_);
v___x_3597_ = l_Lean_Syntax_isOfKind(v_x_3593_, v___x_3596_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_dec(v_x_3593_);
v___x_3598_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
lean_ctor_set(v___x_3599_, 1, v_a_3595_);
return v___x_3599_;
}
else
{
lean_object* v___x_3600_; lean_object* v_tk_3601_; lean_object* v___x_3602_; 
v___x_3600_ = lean_unsigned_to_nat(0u);
v_tk_3601_ = l_Lean_Syntax_getArg(v_x_3593_, v___x_3600_);
v___x_3602_ = l_Lean_Fmt_fmt(v_tk_3601_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v_a_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
v_a_3604_ = lean_ctor_get(v___x_3602_, 1);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3602_, 2);
v___x_3605_ = lean_unsigned_to_nat(1u);
v___x_3606_ = l_Lean_Syntax_getArg(v_x_3593_, v___x_3605_);
lean_dec(v_x_3593_);
v___x_3607_ = l_Lean_Fmt_fmt(v___x_3606_, v_a_3594_, v_a_3604_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3621_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_a_3609_ = lean_ctor_get(v___x_3607_, 1);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3611_ = v___x_3607_;
v_isShared_3612_ = v_isSharedCheck_3621_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3621_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3619_; 
v___x_3613_ = lean_unsigned_to_nat(2u);
v___x_3614_ = lean_mk_empty_array_with_capacity(v___x_3613_);
v___x_3615_ = lean_array_push(v___x_3614_, v_a_3603_);
v___x_3616_ = lean_array_push(v___x_3615_, v_a_3608_);
v___x_3617_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3616_);
lean_dec_ref(v___x_3616_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 0, v___x_3617_);
v___x_3619_ = v___x_3611_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_a_3609_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
else
{
lean_dec(v_a_3603_);
return v___x_3607_;
}
}
else
{
lean_dec(v_x_3593_);
return v___x_3602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTimeCmd___boxed(lean_object* v_x_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Lean_Fmt_fmtTimeCmd(v_x_3622_, v_a_3623_, v_a_3624_);
lean_dec_ref(v_a_3623_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1(){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3632_ = l_Lean_Fmt_fmtAttribute;
v___x_3633_ = ((lean_object*)(l_Lean_Fmt_fmtTimeCmd___closed__1));
v___x_3634_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___closed__1));
v___x_3635_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTimeCmd___boxed), 3, 0);
v___x_3636_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3632_, v___x_3633_, v___x_3634_, v___x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1___boxed(lean_object* v_a_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1();
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckTactic(lean_object* v_x_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3647_ = ((lean_object*)(l_Lean_Fmt_fmtCheckTactic___closed__1));
lean_inc(v_x_3644_);
v___x_3648_ = l_Lean_Syntax_isOfKind(v_x_3644_, v___x_3647_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
lean_dec(v_x_3644_);
v___x_3649_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
lean_ctor_set(v___x_3650_, 1, v_a_3646_);
return v___x_3650_;
}
else
{
lean_object* v___x_3651_; lean_object* v_tk_3652_; lean_object* v___x_3653_; 
v___x_3651_ = lean_unsigned_to_nat(0u);
v_tk_3652_ = l_Lean_Syntax_getArg(v_x_3644_, v___x_3651_);
v___x_3653_ = l_Lean_Fmt_fmt(v_tk_3652_, v_a_3645_, v_a_3646_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v_a_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
v_a_3655_ = lean_ctor_get(v___x_3653_, 1);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3653_, 2);
v___x_3656_ = lean_unsigned_to_nat(1u);
v___x_3657_ = l_Lean_Syntax_getArg(v_x_3644_, v___x_3656_);
v___x_3658_ = l_Lean_Fmt_fmt(v___x_3657_, v_a_3645_, v_a_3655_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v_a_3660_; lean_object* v___x_3661_; lean_object* v_arrowTk_3662_; lean_object* v___x_3663_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
v_a_3660_ = lean_ctor_get(v___x_3658_, 1);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3658_, 2);
v___x_3661_ = lean_unsigned_to_nat(2u);
v_arrowTk_3662_ = l_Lean_Syntax_getArg(v_x_3644_, v___x_3661_);
v___x_3663_ = l_Lean_Fmt_fmt(v_arrowTk_3662_, v_a_3645_, v_a_3660_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v_a_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
v_a_3665_ = lean_ctor_get(v___x_3663_, 1);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3663_, 2);
v___x_3666_ = lean_unsigned_to_nat(3u);
v___x_3667_ = l_Lean_Syntax_getArg(v_x_3644_, v___x_3666_);
v___x_3668_ = l_Lean_Fmt_fmt(v___x_3667_, v_a_3645_, v_a_3665_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v_a_3670_; lean_object* v___x_3671_; lean_object* v_byTk_3672_; lean_object* v___x_3673_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
v_a_3670_ = lean_ctor_get(v___x_3668_, 1);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3668_, 2);
v___x_3671_ = lean_unsigned_to_nat(4u);
v_byTk_3672_ = l_Lean_Syntax_getArg(v_x_3644_, v___x_3671_);
v___x_3673_ = l_Lean_Fmt_fmt(v_byTk_3672_, v_a_3645_, v_a_3670_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v_a_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
v_a_3675_ = lean_ctor_get(v___x_3673_, 1);
lean_inc(v_a_3675_);
lean_dec_ref_known(v___x_3673_, 2);
v___x_3676_ = lean_unsigned_to_nat(5u);
v___x_3677_ = l_Lean_Syntax_getArg(v_x_3644_, v___x_3676_);
lean_dec(v_x_3644_);
v___x_3678_ = l_Lean_Fmt_fmt(v___x_3677_, v_a_3645_, v_a_3675_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3701_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
v_a_3680_ = lean_ctor_get(v___x_3678_, 1);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3682_ = v___x_3678_;
v_isShared_3683_ = v_isSharedCheck_3701_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_inc(v_a_3679_);
lean_dec(v___x_3678_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3701_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3699_; 
v___x_3684_ = lean_mk_empty_array_with_capacity(v___x_3666_);
v___x_3685_ = lean_array_push(v___x_3684_, v_a_3659_);
v___x_3686_ = lean_array_push(v___x_3685_, v_a_3664_);
v___x_3687_ = lean_array_push(v___x_3686_, v_a_3669_);
v___x_3688_ = 0;
v___x_3689_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_3689_, 0, v___x_3648_);
lean_ctor_set_uint8(v___x_3689_, 1, v___x_3688_);
lean_ctor_set_uint8(v___x_3689_, 2, v___x_3648_);
lean_ctor_set_uint8(v___x_3689_, 3, v___x_3688_);
lean_ctor_set_uint8(v___x_3689_, 4, v___x_3688_);
v___x_3690_ = l_Lean_Fmt_Layouts_infixOperator(v___x_3687_, v___x_3689_);
lean_dec_ref_known(v___x_3689_, 0);
v___x_3691_ = lean_mk_empty_array_with_capacity(v___x_3661_);
v___x_3692_ = lean_array_push(v___x_3691_, v_a_3654_);
v___x_3693_ = lean_array_push(v___x_3692_, v___x_3690_);
v___x_3694_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3694_, 0, v___x_3648_);
lean_ctor_set_uint8(v___x_3694_, 1, v___x_3688_);
lean_ctor_set_uint8(v___x_3694_, 2, v___x_3688_);
lean_ctor_set_uint8(v___x_3694_, 3, v___x_3688_);
v___x_3695_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3693_, v___x_3694_);
v___x_3696_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3696_, 0, v___x_3648_);
lean_ctor_set_uint8(v___x_3696_, 1, v___x_3648_);
v___x_3697_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_3695_, v_a_3674_, v_a_3679_, v___x_3696_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 0, v___x_3697_);
v___x_3699_ = v___x_3682_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3697_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_a_3680_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
else
{
lean_dec(v_a_3674_);
lean_dec(v_a_3669_);
lean_dec(v_a_3664_);
lean_dec(v_a_3659_);
lean_dec(v_a_3654_);
return v___x_3678_;
}
}
else
{
lean_dec(v_a_3669_);
lean_dec(v_a_3664_);
lean_dec(v_a_3659_);
lean_dec(v_a_3654_);
lean_dec(v_x_3644_);
return v___x_3673_;
}
}
else
{
lean_dec(v_a_3664_);
lean_dec(v_a_3659_);
lean_dec(v_a_3654_);
lean_dec(v_x_3644_);
return v___x_3668_;
}
}
else
{
lean_dec(v_a_3659_);
lean_dec(v_a_3654_);
lean_dec(v_x_3644_);
return v___x_3663_;
}
}
else
{
lean_dec(v_a_3654_);
lean_dec(v_x_3644_);
return v___x_3658_;
}
}
else
{
lean_dec(v_x_3644_);
return v___x_3653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckTactic___boxed(lean_object* v_x_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_Fmt_fmtCheckTactic(v_x_3702_, v_a_3703_, v_a_3704_);
lean_dec_ref(v_a_3703_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1(){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3712_ = l_Lean_Fmt_fmtAttribute;
v___x_3713_ = ((lean_object*)(l_Lean_Fmt_fmtCheckTactic___closed__1));
v___x_3714_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___closed__1));
v___x_3715_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCheckTactic___boxed), 3, 0);
v___x_3716_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3712_, v___x_3713_, v___x_3714_, v___x_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1___boxed(lean_object* v_a_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1();
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckTacticFailure(lean_object* v_x_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v___x_3727_; uint8_t v___x_3728_; 
v___x_3727_ = ((lean_object*)(l_Lean_Fmt_fmtCheckTacticFailure___closed__1));
lean_inc(v_x_3724_);
v___x_3728_ = l_Lean_Syntax_isOfKind(v_x_3724_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_dec(v_x_3724_);
v___x_3729_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
lean_ctor_set(v___x_3730_, 1, v_a_3726_);
return v___x_3730_;
}
else
{
lean_object* v___x_3731_; lean_object* v_tk_3732_; lean_object* v___x_3733_; 
v___x_3731_ = lean_unsigned_to_nat(0u);
v_tk_3732_ = l_Lean_Syntax_getArg(v_x_3724_, v___x_3731_);
v___x_3733_ = l_Lean_Fmt_fmt(v_tk_3732_, v_a_3725_, v_a_3726_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v_a_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
v_a_3735_ = lean_ctor_get(v___x_3733_, 1);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___x_3733_, 2);
v___x_3736_ = lean_unsigned_to_nat(1u);
v___x_3737_ = l_Lean_Syntax_getArg(v_x_3724_, v___x_3736_);
v___x_3738_ = l_Lean_Fmt_fmt(v___x_3737_, v_a_3725_, v_a_3735_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v_a_3740_; lean_object* v___x_3741_; lean_object* v_byTk_3742_; uint8_t v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3739_);
v_a_3740_ = lean_ctor_get(v___x_3738_, 1);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___x_3738_, 2);
v___x_3741_ = lean_unsigned_to_nat(2u);
v_byTk_3742_ = l_Lean_Syntax_getArg(v_x_3724_, v___x_3741_);
v___x_3743_ = 0;
v___x_3744_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3744_, 0, v___x_3728_);
lean_ctor_set_uint8(v___x_3744_, 1, v___x_3743_);
lean_ctor_set_uint8(v___x_3744_, 2, v___x_3743_);
lean_ctor_set_uint8(v___x_3744_, 3, v___x_3743_);
v___x_3745_ = l_Lean_Fmt_fmt(v_byTk_3742_, v_a_3725_, v_a_3740_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v_a_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
v_a_3747_ = lean_ctor_get(v___x_3745_, 1);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3745_, 2);
v___x_3748_ = lean_unsigned_to_nat(3u);
v___x_3749_ = l_Lean_Syntax_getArg(v_x_3724_, v___x_3748_);
lean_dec(v_x_3724_);
v___x_3750_ = l_Lean_Fmt_fmt(v___x_3749_, v_a_3725_, v_a_3747_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3765_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
v_a_3752_ = lean_ctor_get(v___x_3750_, 1);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3754_ = v___x_3750_;
v_isShared_3755_ = v_isSharedCheck_3765_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_inc(v_a_3751_);
lean_dec(v___x_3750_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3765_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3763_; 
v___x_3756_ = lean_mk_empty_array_with_capacity(v___x_3741_);
v___x_3757_ = lean_array_push(v___x_3756_, v_a_3734_);
v___x_3758_ = lean_array_push(v___x_3757_, v_a_3739_);
v___x_3759_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3758_, v___x_3744_);
v___x_3760_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3760_, 0, v___x_3728_);
lean_ctor_set_uint8(v___x_3760_, 1, v___x_3728_);
v___x_3761_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_3759_, v_a_3746_, v_a_3751_, v___x_3760_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v___x_3761_);
v___x_3763_ = v___x_3754_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3761_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_a_3752_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
else
{
lean_dec(v_a_3746_);
lean_dec_ref_known(v___x_3744_, 0);
lean_dec(v_a_3739_);
lean_dec(v_a_3734_);
return v___x_3750_;
}
}
else
{
lean_dec_ref_known(v___x_3744_, 0);
lean_dec(v_a_3739_);
lean_dec(v_a_3734_);
lean_dec(v_x_3724_);
return v___x_3745_;
}
}
else
{
lean_dec(v_a_3734_);
lean_dec(v_x_3724_);
return v___x_3738_;
}
}
else
{
lean_dec(v_x_3724_);
return v___x_3733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckTacticFailure___boxed(lean_object* v_x_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Fmt_fmtCheckTacticFailure(v_x_3766_, v_a_3767_, v_a_3768_);
lean_dec_ref(v_a_3767_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1(){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3776_ = l_Lean_Fmt_fmtAttribute;
v___x_3777_ = ((lean_object*)(l_Lean_Fmt_fmtCheckTacticFailure___closed__1));
v___x_3778_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___closed__1));
v___x_3779_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCheckTacticFailure___boxed), 3, 0);
v___x_3780_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3776_, v___x_3777_, v___x_3778_, v___x_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1___boxed(lean_object* v_a_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1();
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckSimp(lean_object* v_x_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3791_ = ((lean_object*)(l_Lean_Fmt_fmtCheckSimp___closed__1));
lean_inc(v_x_3788_);
v___x_3792_ = l_Lean_Syntax_isOfKind(v_x_3788_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
lean_dec(v_x_3788_);
v___x_3793_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
lean_ctor_set(v___x_3794_, 1, v_a_3790_);
return v___x_3794_;
}
else
{
lean_object* v___x_3795_; lean_object* v_tk_3796_; lean_object* v___x_3797_; 
v___x_3795_ = lean_unsigned_to_nat(0u);
v_tk_3796_ = l_Lean_Syntax_getArg(v_x_3788_, v___x_3795_);
v___x_3797_ = l_Lean_Fmt_fmt(v_tk_3796_, v_a_3789_, v_a_3790_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v_a_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
v_a_3799_ = lean_ctor_get(v___x_3797_, 1);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3797_, 2);
v___x_3800_ = lean_unsigned_to_nat(1u);
v___x_3801_ = l_Lean_Syntax_getArg(v_x_3788_, v___x_3800_);
v___x_3802_ = l_Lean_Fmt_fmt(v___x_3801_, v_a_3789_, v_a_3799_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v_a_3804_; lean_object* v___x_3805_; lean_object* v_arrowTk_3806_; lean_object* v___x_3807_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
v_a_3804_ = lean_ctor_get(v___x_3802_, 1);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3802_, 2);
v___x_3805_ = lean_unsigned_to_nat(2u);
v_arrowTk_3806_ = l_Lean_Syntax_getArg(v_x_3788_, v___x_3805_);
v___x_3807_ = l_Lean_Fmt_fmt(v_arrowTk_3806_, v_a_3789_, v_a_3804_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v_a_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_a_3808_);
v_a_3809_ = lean_ctor_get(v___x_3807_, 1);
lean_inc(v_a_3809_);
lean_dec_ref_known(v___x_3807_, 2);
v___x_3810_ = lean_unsigned_to_nat(3u);
v___x_3811_ = l_Lean_Syntax_getArg(v_x_3788_, v___x_3810_);
lean_dec(v_x_3788_);
v___x_3812_ = l_Lean_Fmt_fmt(v___x_3811_, v_a_3789_, v_a_3809_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3833_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
v_a_3814_ = lean_ctor_get(v___x_3812_, 1);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3816_ = v___x_3812_;
v_isShared_3817_ = v_isSharedCheck_3833_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_inc(v_a_3813_);
lean_dec(v___x_3812_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3833_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3831_; 
v___x_3818_ = lean_mk_empty_array_with_capacity(v___x_3810_);
v___x_3819_ = lean_array_push(v___x_3818_, v_a_3803_);
v___x_3820_ = lean_array_push(v___x_3819_, v_a_3808_);
v___x_3821_ = lean_array_push(v___x_3820_, v_a_3813_);
v___x_3822_ = 0;
v___x_3823_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_3823_, 0, v___x_3792_);
lean_ctor_set_uint8(v___x_3823_, 1, v___x_3822_);
lean_ctor_set_uint8(v___x_3823_, 2, v___x_3792_);
lean_ctor_set_uint8(v___x_3823_, 3, v___x_3822_);
lean_ctor_set_uint8(v___x_3823_, 4, v___x_3822_);
v___x_3824_ = l_Lean_Fmt_Layouts_infixOperator(v___x_3821_, v___x_3823_);
lean_dec_ref_known(v___x_3823_, 0);
v___x_3825_ = lean_mk_empty_array_with_capacity(v___x_3805_);
v___x_3826_ = lean_array_push(v___x_3825_, v_a_3798_);
v___x_3827_ = lean_array_push(v___x_3826_, v___x_3824_);
v___x_3828_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3828_, 0, v___x_3792_);
lean_ctor_set_uint8(v___x_3828_, 1, v___x_3822_);
lean_ctor_set_uint8(v___x_3828_, 2, v___x_3822_);
lean_ctor_set_uint8(v___x_3828_, 3, v___x_3822_);
v___x_3829_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3827_, v___x_3828_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 0, v___x_3829_);
v___x_3831_ = v___x_3816_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3829_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_a_3814_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
else
{
lean_dec(v_a_3808_);
lean_dec(v_a_3803_);
lean_dec(v_a_3798_);
return v___x_3812_;
}
}
else
{
lean_dec(v_a_3803_);
lean_dec(v_a_3798_);
lean_dec(v_x_3788_);
return v___x_3807_;
}
}
else
{
lean_dec(v_a_3798_);
lean_dec(v_x_3788_);
return v___x_3802_;
}
}
else
{
lean_dec(v_x_3788_);
return v___x_3797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckSimp___boxed(lean_object* v_x_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Fmt_fmtCheckSimp(v_x_3834_, v_a_3835_, v_a_3836_);
lean_dec_ref(v_a_3835_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1(){
_start:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3844_ = l_Lean_Fmt_fmtAttribute;
v___x_3845_ = ((lean_object*)(l_Lean_Fmt_fmtCheckSimp___closed__1));
v___x_3846_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___closed__1));
v___x_3847_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCheckSimp___boxed), 3, 0);
v___x_3848_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3844_, v___x_3845_, v___x_3846_, v___x_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1___boxed(lean_object* v_a_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1();
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckSimpFailure(lean_object* v_x_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_){
_start:
{
lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3859_ = ((lean_object*)(l_Lean_Fmt_fmtCheckSimpFailure___closed__1));
lean_inc(v_x_3856_);
v___x_3860_ = l_Lean_Syntax_isOfKind(v_x_3856_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_dec(v_x_3856_);
v___x_3861_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
lean_ctor_set(v___x_3862_, 1, v_a_3858_);
return v___x_3862_;
}
else
{
lean_object* v___x_3863_; lean_object* v_tk_3864_; lean_object* v___x_3865_; 
v___x_3863_ = lean_unsigned_to_nat(0u);
v_tk_3864_ = l_Lean_Syntax_getArg(v_x_3856_, v___x_3863_);
v___x_3865_ = l_Lean_Fmt_fmt(v_tk_3864_, v_a_3857_, v_a_3858_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v_a_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
v_a_3867_ = lean_ctor_get(v___x_3865_, 1);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3865_, 2);
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = l_Lean_Syntax_getArg(v_x_3856_, v___x_3868_);
v___x_3870_ = l_Lean_Fmt_fmt(v___x_3869_, v_a_3857_, v_a_3867_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v_a_3872_; lean_object* v___x_3873_; lean_object* v_failTk_3874_; lean_object* v___x_3875_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
v_a_3872_ = lean_ctor_get(v___x_3870_, 1);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3870_, 2);
v___x_3873_ = lean_unsigned_to_nat(2u);
v_failTk_3874_ = l_Lean_Syntax_getArg(v_x_3856_, v___x_3873_);
lean_dec(v_x_3856_);
v___x_3875_ = l_Lean_Fmt_fmt(v_failTk_3874_, v_a_3857_, v_a_3872_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3892_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
v_a_3877_ = lean_ctor_get(v___x_3875_, 1);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3879_ = v___x_3875_;
v_isShared_3880_ = v_isSharedCheck_3892_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_inc(v_a_3876_);
lean_dec(v___x_3875_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3892_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
uint8_t v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; uint8_t v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3890_; 
v___x_3881_ = 1;
v___x_3882_ = l_Lean_Fmt_Layouts_postfixOperator(v_a_3871_, v_a_3876_, v___x_3881_);
v___x_3883_ = lean_mk_empty_array_with_capacity(v___x_3873_);
v___x_3884_ = lean_array_push(v___x_3883_, v_a_3866_);
v___x_3885_ = lean_array_push(v___x_3884_, v___x_3882_);
v___x_3886_ = 0;
v___x_3887_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3887_, 0, v___x_3860_);
lean_ctor_set_uint8(v___x_3887_, 1, v___x_3886_);
lean_ctor_set_uint8(v___x_3887_, 2, v___x_3886_);
lean_ctor_set_uint8(v___x_3887_, 3, v___x_3886_);
v___x_3888_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3885_, v___x_3887_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 0, v___x_3888_);
v___x_3890_ = v___x_3879_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3888_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_a_3877_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
else
{
lean_dec(v_a_3871_);
lean_dec(v_a_3866_);
return v___x_3875_;
}
}
else
{
lean_dec(v_a_3866_);
lean_dec(v_x_3856_);
return v___x_3870_;
}
}
else
{
lean_dec(v_x_3856_);
return v___x_3865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtCheckSimpFailure___boxed(lean_object* v_x_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_Fmt_fmtCheckSimpFailure(v_x_3893_, v_a_3894_, v_a_3895_);
lean_dec_ref(v_a_3894_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1(){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3903_ = l_Lean_Fmt_fmtAttribute;
v___x_3904_ = ((lean_object*)(l_Lean_Fmt_fmtCheckSimpFailure___closed__1));
v___x_3905_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___closed__1));
v___x_3906_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtCheckSimpFailure___boxed), 3, 0);
v___x_3907_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3903_, v___x_3904_, v___x_3905_, v___x_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1___boxed(lean_object* v_a_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1();
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsFilter(lean_object* v_x_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_){
_start:
{
lean_object* v___x_3925_; uint8_t v___x_3926_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v_action_x3f_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; 
v___x_3925_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsFilter___closed__1));
lean_inc(v_x_3922_);
v___x_3926_ = l_Lean_Syntax_isOfKind(v_x_3922_, v___x_3925_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
lean_dec(v_x_3922_);
v___x_3971_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
lean_ctor_set(v___x_3972_, 1, v_a_3924_);
return v___x_3972_;
}
else
{
lean_object* v___x_3973_; lean_object* v___x_3974_; uint8_t v___x_3975_; 
v___x_3973_ = lean_unsigned_to_nat(0u);
v___x_3974_ = l_Lean_Syntax_getArg(v_x_3922_, v___x_3973_);
v___x_3975_ = l_Lean_Syntax_isNone(v___x_3974_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3976_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_3974_);
v___x_3977_ = l_Lean_Syntax_matchesNull(v___x_3974_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
lean_dec(v___x_3974_);
lean_dec(v_x_3922_);
v___x_3978_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
lean_ctor_set(v___x_3979_, 1, v_a_3924_);
return v___x_3979_;
}
else
{
lean_object* v_action_x3f_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; 
v_action_x3f_3980_ = l_Lean_Syntax_getArg(v___x_3974_, v___x_3973_);
lean_dec(v___x_3974_);
v___x_3981_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsFilter___closed__5));
lean_inc(v_action_x3f_3980_);
v___x_3982_ = l_Lean_Syntax_isOfKind(v_action_x3f_3980_, v___x_3981_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
lean_dec(v_action_x3f_3980_);
lean_dec(v_x_3922_);
v___x_3983_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3983_);
lean_ctor_set(v___x_3984_, 1, v_a_3924_);
return v___x_3984_;
}
else
{
lean_object* v___x_3985_; 
v___x_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3985_, 0, v_action_x3f_3980_);
v_action_x3f_3953_ = v___x_3985_;
v___y_3954_ = v_a_3923_;
v___y_3955_ = v_a_3924_;
goto v___jp_3952_;
}
}
}
else
{
lean_object* v___x_3986_; 
lean_dec(v___x_3974_);
v___x_3986_ = lean_box(0);
v_action_x3f_3953_ = v___x_3986_;
v___y_3954_ = v_a_3923_;
v___y_3955_ = v_a_3924_;
goto v___jp_3952_;
}
}
v___jp_3927_:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_Fmt_fmt_x3f(v___y_3931_, v___y_3930_, v___y_3928_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; lean_object* v_a_3934_; lean_object* v___x_3935_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_a_3933_);
v_a_3934_ = lean_ctor_get(v___x_3932_, 1);
lean_inc(v_a_3934_);
lean_dec_ref_known(v___x_3932_, 2);
v___x_3935_ = l_Lean_Fmt_fmt(v___y_3929_, v___y_3930_, v_a_3934_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3951_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
v_a_3937_ = lean_ctor_get(v___x_3935_, 1);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3939_ = v___x_3935_;
v_isShared_3940_ = v_isSharedCheck_3951_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_inc(v_a_3936_);
lean_dec(v___x_3935_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3951_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3949_; 
v___x_3941_ = lean_unsigned_to_nat(2u);
v___x_3942_ = lean_mk_empty_array_with_capacity(v___x_3941_);
v___x_3943_ = lean_array_push(v___x_3942_, v_a_3933_);
v___x_3944_ = lean_array_push(v___x_3943_, v_a_3936_);
v___x_3945_ = 0;
v___x_3946_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3946_, 0, v___x_3926_);
lean_ctor_set_uint8(v___x_3946_, 1, v___x_3945_);
lean_ctor_set_uint8(v___x_3946_, 2, v___x_3945_);
lean_ctor_set_uint8(v___x_3946_, 3, v___x_3945_);
v___x_3947_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_3944_, v___x_3946_);
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 0, v___x_3947_);
v___x_3949_ = v___x_3939_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3947_);
lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_a_3937_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
else
{
lean_dec(v_a_3933_);
return v___x_3935_;
}
}
else
{
lean_dec(v___y_3929_);
return v___x_3932_;
}
}
v___jp_3952_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; 
v___x_3956_ = lean_unsigned_to_nat(1u);
v___x_3957_ = l_Lean_Syntax_getArg(v_x_3922_, v___x_3956_);
lean_dec(v_x_3922_);
v___x_3958_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsFilter___closed__3));
lean_inc(v___x_3957_);
v___x_3959_ = l_Lean_Syntax_isOfKind(v___x_3957_, v___x_3958_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
lean_dec(v___x_3957_);
lean_dec(v_action_x3f_3953_);
v___x_3960_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
lean_ctor_set(v___x_3961_, 1, v___y_3955_);
return v___x_3961_;
}
else
{
if (lean_obj_tag(v_action_x3f_3953_) == 0)
{
lean_object* v___x_3962_; 
v___x_3962_ = lean_box(0);
v___y_3928_ = v___y_3955_;
v___y_3929_ = v___x_3957_;
v___y_3930_ = v___y_3954_;
v___y_3931_ = v___x_3962_;
goto v___jp_3927_;
}
else
{
lean_object* v_val_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
v_val_3963_ = lean_ctor_get(v_action_x3f_3953_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_action_x3f_3953_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v_action_x3f_3953_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_val_3963_);
lean_dec(v_action_x3f_3953_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_val_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
v___y_3928_ = v___y_3955_;
v___y_3929_ = v___x_3957_;
v___y_3930_ = v___y_3954_;
v___y_3931_ = v___x_3968_;
goto v___jp_3927_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsFilter___boxed(lean_object* v_x_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_Fmt_fmtGuardMsgsFilter(v_x_3987_, v_a_3988_, v_a_3989_);
lean_dec_ref(v_a_3988_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1(){
_start:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3997_ = l_Lean_Fmt_fmtAttribute;
v___x_3998_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsFilter___closed__1));
v___x_3999_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___closed__1));
v___x_4000_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardMsgsFilter___boxed), 3, 0);
v___x_4001_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3997_, v___x_3998_, v___x_3999_, v___x_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1___boxed(lean_object* v_a_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1();
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsWhitespace(lean_object* v_x_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v___x_4015_; uint8_t v___x_4016_; 
v___x_4015_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__1));
lean_inc(v_x_4012_);
v___x_4016_ = l_Lean_Syntax_isOfKind(v_x_4012_, v___x_4015_);
if (v___x_4016_ == 0)
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_dec(v_x_4012_);
v___x_4017_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
lean_ctor_set(v___x_4018_, 1, v_a_4014_);
return v___x_4018_;
}
else
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; uint8_t v___x_4022_; 
v___x_4019_ = lean_unsigned_to_nat(2u);
v___x_4020_ = l_Lean_Syntax_getArg(v_x_4012_, v___x_4019_);
v___x_4021_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__3));
lean_inc(v___x_4020_);
v___x_4022_ = l_Lean_Syntax_isOfKind(v___x_4020_, v___x_4021_);
if (v___x_4022_ == 0)
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
lean_dec(v___x_4020_);
lean_dec(v_x_4012_);
v___x_4023_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
lean_ctor_set(v___x_4024_, 1, v_a_4014_);
return v___x_4024_;
}
else
{
lean_object* v___x_4025_; lean_object* v_tk_4026_; lean_object* v___x_4027_; 
v___x_4025_ = lean_unsigned_to_nat(0u);
v_tk_4026_ = l_Lean_Syntax_getArg(v_x_4012_, v___x_4025_);
v___x_4027_ = l_Lean_Fmt_fmt(v_tk_4026_, v_a_4013_, v_a_4014_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v_a_4029_; lean_object* v___x_4030_; lean_object* v_colonEqTk_4031_; lean_object* v___x_4032_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
v_a_4029_ = lean_ctor_get(v___x_4027_, 1);
lean_inc(v_a_4029_);
lean_dec_ref_known(v___x_4027_, 2);
v___x_4030_ = lean_unsigned_to_nat(1u);
v_colonEqTk_4031_ = l_Lean_Syntax_getArg(v_x_4012_, v___x_4030_);
lean_dec(v_x_4012_);
v___x_4032_ = l_Lean_Fmt_fmt(v_colonEqTk_4031_, v_a_4013_, v_a_4029_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v_a_4034_; lean_object* v___x_4035_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
v_a_4034_ = lean_ctor_get(v___x_4032_, 1);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4032_, 2);
v___x_4035_ = l_Lean_Fmt_fmt(v___x_4020_, v_a_4013_, v_a_4034_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4046_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_a_4037_ = lean_ctor_get(v___x_4035_, 1);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4039_ = v___x_4035_;
v_isShared_4040_ = v_isSharedCheck_4046_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4046_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
uint8_t v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4044_; 
v___x_4041_ = 0;
v___x_4042_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_4028_, v_a_4033_, v_a_4036_, v___x_4041_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v___x_4042_);
v___x_4044_ = v___x_4039_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4042_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v_a_4037_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
else
{
lean_dec(v_a_4033_);
lean_dec(v_a_4028_);
return v___x_4035_;
}
}
else
{
lean_dec(v_a_4028_);
lean_dec(v___x_4020_);
return v___x_4032_;
}
}
else
{
lean_dec(v___x_4020_);
lean_dec(v_x_4012_);
return v___x_4027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsWhitespace___boxed(lean_object* v_x_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_Fmt_fmtGuardMsgsWhitespace(v_x_4047_, v_a_4048_, v_a_4049_);
lean_dec_ref(v_a_4048_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1(){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4057_ = l_Lean_Fmt_fmtAttribute;
v___x_4058_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsWhitespace___closed__1));
v___x_4059_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___closed__1));
v___x_4060_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardMsgsWhitespace___boxed), 3, 0);
v___x_4061_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4057_, v___x_4058_, v___x_4059_, v___x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1___boxed(lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1();
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsOrdering(lean_object* v_x_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v___x_4075_; uint8_t v___x_4076_; 
v___x_4075_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsOrdering___closed__1));
lean_inc(v_x_4072_);
v___x_4076_ = l_Lean_Syntax_isOfKind(v_x_4072_, v___x_4075_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
lean_dec(v_x_4072_);
v___x_4077_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
lean_ctor_set(v___x_4078_, 1, v_a_4074_);
return v___x_4078_;
}
else
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; 
v___x_4079_ = lean_unsigned_to_nat(2u);
v___x_4080_ = l_Lean_Syntax_getArg(v_x_4072_, v___x_4079_);
v___x_4081_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsOrdering___closed__3));
lean_inc(v___x_4080_);
v___x_4082_ = l_Lean_Syntax_isOfKind(v___x_4080_, v___x_4081_);
if (v___x_4082_ == 0)
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_dec(v___x_4080_);
lean_dec(v_x_4072_);
v___x_4083_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
lean_ctor_set(v___x_4084_, 1, v_a_4074_);
return v___x_4084_;
}
else
{
lean_object* v___x_4085_; lean_object* v_tk_4086_; lean_object* v___x_4087_; 
v___x_4085_ = lean_unsigned_to_nat(0u);
v_tk_4086_ = l_Lean_Syntax_getArg(v_x_4072_, v___x_4085_);
v___x_4087_ = l_Lean_Fmt_fmt(v_tk_4086_, v_a_4073_, v_a_4074_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v_a_4089_; lean_object* v___x_4090_; lean_object* v_colonEqTk_4091_; lean_object* v___x_4092_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
lean_inc(v_a_4088_);
v_a_4089_ = lean_ctor_get(v___x_4087_, 1);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___x_4087_, 2);
v___x_4090_ = lean_unsigned_to_nat(1u);
v_colonEqTk_4091_ = l_Lean_Syntax_getArg(v_x_4072_, v___x_4090_);
lean_dec(v_x_4072_);
v___x_4092_ = l_Lean_Fmt_fmt(v_colonEqTk_4091_, v_a_4073_, v_a_4089_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v_a_4094_; lean_object* v___x_4095_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
v_a_4094_ = lean_ctor_get(v___x_4092_, 1);
lean_inc(v_a_4094_);
lean_dec_ref_known(v___x_4092_, 2);
v___x_4095_ = l_Lean_Fmt_fmt(v___x_4080_, v_a_4073_, v_a_4094_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4106_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
v_a_4097_ = lean_ctor_get(v___x_4095_, 1);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4099_ = v___x_4095_;
v_isShared_4100_ = v_isSharedCheck_4106_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_inc(v_a_4096_);
lean_dec(v___x_4095_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4106_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
uint8_t v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4104_; 
v___x_4101_ = 0;
v___x_4102_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_4088_, v_a_4093_, v_a_4096_, v___x_4101_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v___x_4102_);
v___x_4104_ = v___x_4099_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v_a_4097_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
else
{
lean_dec(v_a_4093_);
lean_dec(v_a_4088_);
return v___x_4095_;
}
}
else
{
lean_dec(v_a_4088_);
lean_dec(v___x_4080_);
return v___x_4092_;
}
}
else
{
lean_dec(v___x_4080_);
lean_dec(v_x_4072_);
return v___x_4087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsOrdering___boxed(lean_object* v_x_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Lean_Fmt_fmtGuardMsgsOrdering(v_x_4107_, v_a_4108_, v_a_4109_);
lean_dec_ref(v_a_4108_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1(){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4117_ = l_Lean_Fmt_fmtAttribute;
v___x_4118_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsOrdering___closed__1));
v___x_4119_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___closed__1));
v___x_4120_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardMsgsOrdering___boxed), 3, 0);
v___x_4121_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4117_, v___x_4118_, v___x_4119_, v___x_4120_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1___boxed(lean_object* v_a_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1();
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsPositions(lean_object* v_x_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v___x_4135_; uint8_t v___x_4136_; 
v___x_4135_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsPositions___closed__1));
lean_inc(v_x_4132_);
v___x_4136_ = l_Lean_Syntax_isOfKind(v_x_4132_, v___x_4135_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_dec(v_x_4132_);
v___x_4137_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
lean_ctor_set(v___x_4138_, 1, v_a_4134_);
return v___x_4138_;
}
else
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; uint8_t v___x_4142_; 
v___x_4139_ = lean_unsigned_to_nat(2u);
v___x_4140_ = l_Lean_Syntax_getArg(v_x_4132_, v___x_4139_);
v___x_4141_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsPositions___closed__3));
lean_inc(v___x_4140_);
v___x_4142_ = l_Lean_Syntax_isOfKind(v___x_4140_, v___x_4141_);
if (v___x_4142_ == 0)
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
lean_dec(v___x_4140_);
lean_dec(v_x_4132_);
v___x_4143_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
lean_ctor_set(v___x_4144_, 1, v_a_4134_);
return v___x_4144_;
}
else
{
lean_object* v___x_4145_; lean_object* v_tk_4146_; lean_object* v___x_4147_; 
v___x_4145_ = lean_unsigned_to_nat(0u);
v_tk_4146_ = l_Lean_Syntax_getArg(v_x_4132_, v___x_4145_);
v___x_4147_ = l_Lean_Fmt_fmt(v_tk_4146_, v_a_4133_, v_a_4134_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; lean_object* v_a_4149_; lean_object* v___x_4150_; lean_object* v_colonEqTk_4151_; lean_object* v___x_4152_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
v_a_4149_ = lean_ctor_get(v___x_4147_, 1);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4147_, 2);
v___x_4150_ = lean_unsigned_to_nat(1u);
v_colonEqTk_4151_ = l_Lean_Syntax_getArg(v_x_4132_, v___x_4150_);
lean_dec(v_x_4132_);
v___x_4152_ = l_Lean_Fmt_fmt(v_colonEqTk_4151_, v_a_4133_, v_a_4149_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v_a_4154_; lean_object* v___x_4155_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
v_a_4154_ = lean_ctor_get(v___x_4152_, 1);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4152_, 2);
v___x_4155_ = l_Lean_Fmt_fmt(v___x_4140_, v_a_4133_, v_a_4154_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4166_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
v_a_4157_ = lean_ctor_get(v___x_4155_, 1);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4159_ = v___x_4155_;
v_isShared_4160_ = v_isSharedCheck_4166_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_inc(v_a_4156_);
lean_dec(v___x_4155_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4166_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
uint8_t v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4164_; 
v___x_4161_ = 0;
v___x_4162_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_4148_, v_a_4153_, v_a_4156_, v___x_4161_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 0, v___x_4162_);
v___x_4164_ = v___x_4159_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4162_);
lean_ctor_set(v_reuseFailAlloc_4165_, 1, v_a_4157_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
else
{
lean_dec(v_a_4153_);
lean_dec(v_a_4148_);
return v___x_4155_;
}
}
else
{
lean_dec(v_a_4148_);
lean_dec(v___x_4140_);
return v___x_4152_;
}
}
else
{
lean_dec(v___x_4140_);
lean_dec(v_x_4132_);
return v___x_4147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsPositions___boxed(lean_object* v_x_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_Fmt_fmtGuardMsgsPositions(v_x_4167_, v_a_4168_, v_a_4169_);
lean_dec_ref(v_a_4168_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1(){
_start:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4177_ = l_Lean_Fmt_fmtAttribute;
v___x_4178_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsPositions___closed__1));
v___x_4179_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___closed__1));
v___x_4180_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardMsgsPositions___boxed), 3, 0);
v___x_4181_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4177_, v___x_4178_, v___x_4179_, v___x_4180_);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1___boxed(lean_object* v_a_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1();
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSubstring(lean_object* v_x_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_){
_start:
{
lean_object* v___x_4191_; uint8_t v___x_4192_; 
v___x_4191_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsSubstring___closed__1));
lean_inc(v_x_4188_);
v___x_4192_ = l_Lean_Syntax_isOfKind(v_x_4188_, v___x_4191_);
if (v___x_4192_ == 0)
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_dec(v_x_4188_);
v___x_4193_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
lean_ctor_set(v___x_4194_, 1, v_a_4190_);
return v___x_4194_;
}
else
{
lean_object* v___x_4195_; lean_object* v_tk_4196_; lean_object* v___x_4197_; 
v___x_4195_ = lean_unsigned_to_nat(0u);
v_tk_4196_ = l_Lean_Syntax_getArg(v_x_4188_, v___x_4195_);
v___x_4197_ = l_Lean_Fmt_fmt(v_tk_4196_, v_a_4189_, v_a_4190_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v_a_4199_; lean_object* v___x_4200_; lean_object* v_colonEqTk_4201_; lean_object* v___x_4202_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
v_a_4199_ = lean_ctor_get(v___x_4197_, 1);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4197_, 2);
v___x_4200_ = lean_unsigned_to_nat(1u);
v_colonEqTk_4201_ = l_Lean_Syntax_getArg(v_x_4188_, v___x_4200_);
v___x_4202_ = l_Lean_Fmt_fmt(v_colonEqTk_4201_, v_a_4189_, v_a_4199_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v_a_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
v_a_4204_ = lean_ctor_get(v___x_4202_, 1);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4202_, 2);
v___x_4205_ = lean_unsigned_to_nat(2u);
v___x_4206_ = l_Lean_Syntax_getArg(v_x_4188_, v___x_4205_);
lean_dec(v_x_4188_);
v___x_4207_ = l_Lean_Fmt_fmt(v___x_4206_, v_a_4189_, v_a_4204_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4218_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
v_a_4209_ = lean_ctor_get(v___x_4207_, 1);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4211_ = v___x_4207_;
v_isShared_4212_ = v_isSharedCheck_4218_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_inc(v_a_4208_);
lean_dec(v___x_4207_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4218_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
uint8_t v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4216_; 
v___x_4213_ = 0;
v___x_4214_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_a_4198_, v_a_4203_, v_a_4208_, v___x_4213_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 0, v___x_4214_);
v___x_4216_ = v___x_4211_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_a_4209_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
else
{
lean_dec(v_a_4203_);
lean_dec(v_a_4198_);
return v___x_4207_;
}
}
else
{
lean_dec(v_a_4198_);
lean_dec(v_x_4188_);
return v___x_4202_;
}
}
else
{
lean_dec(v_x_4188_);
return v___x_4197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSubstring___boxed(lean_object* v_x_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Fmt_fmtGuardMsgsSubstring(v_x_4219_, v_a_4220_, v_a_4221_);
lean_dec_ref(v_a_4220_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1(){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4229_ = l_Lean_Fmt_fmtAttribute;
v___x_4230_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsSubstring___closed__1));
v___x_4231_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___closed__1));
v___x_4232_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardMsgsSubstring___boxed), 3, 0);
v___x_4233_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4229_, v___x_4230_, v___x_4231_, v___x_4232_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1___boxed(lean_object* v_a_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1();
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSpecElt(lean_object* v_stx_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = lean_unsigned_to_nat(0u);
v___x_4240_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_4236_, v___x_4239_, v_a_4238_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v_a_4242_; lean_object* v___x_4243_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
v_a_4242_ = lean_ctor_get(v___x_4240_, 1);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4240_, 2);
v___x_4243_ = l_Lean_Fmt_fmt(v_a_4241_, v_a_4237_, v_a_4242_);
return v___x_4243_;
}
else
{
lean_object* v_a_4244_; lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
v_a_4244_ = lean_ctor_get(v___x_4240_, 0);
v_a_4245_ = lean_ctor_get(v___x_4240_, 1);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4240_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_inc(v_a_4244_);
lean_dec(v___x_4240_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4244_);
lean_ctor_set(v_reuseFailAlloc_4251_, 1, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSpecElt___boxed(lean_object* v_stx_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_Fmt_fmtGuardMsgsSpecElt(v_stx_4253_, v_a_4254_, v_a_4255_);
lean_dec_ref(v_a_4254_);
lean_dec(v_stx_4253_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1(){
_start:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4267_ = l_Lean_Fmt_fmtAttribute;
v___x_4268_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__1));
v___x_4269_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___closed__3));
v___x_4270_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardMsgsSpecElt___boxed), 3, 0);
v___x_4271_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4267_, v___x_4268_, v___x_4269_, v___x_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1___boxed(lean_object* v_a_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1();
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSpec(lean_object* v_x_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v___x_4282_; uint8_t v___x_4283_; 
v___x_4282_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsSpec___closed__1));
lean_inc(v_x_4279_);
v___x_4283_ = l_Lean_Syntax_isOfKind(v_x_4279_, v___x_4282_);
if (v___x_4283_ == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
lean_dec(v_x_4279_);
v___x_4284_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4284_);
lean_ctor_set(v___x_4285_, 1, v_a_4281_);
return v___x_4285_;
}
else
{
lean_object* v___x_4286_; lean_object* v_lbTk_4287_; lean_object* v___x_4288_; 
v___x_4286_ = lean_unsigned_to_nat(0u);
v_lbTk_4287_ = l_Lean_Syntax_getArg(v_x_4279_, v___x_4286_);
v___x_4288_ = l_Lean_Fmt_fmt(v_lbTk_4287_, v_a_4280_, v_a_4281_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v_a_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v_elts_4293_; lean_object* v___x_4294_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
v_a_4290_ = lean_ctor_get(v___x_4288_, 1);
lean_inc(v_a_4290_);
lean_dec_ref_known(v___x_4288_, 2);
v___x_4291_ = lean_unsigned_to_nat(1u);
v___x_4292_ = l_Lean_Syntax_getArg(v_x_4279_, v___x_4291_);
v_elts_4293_ = l_Lean_Syntax_getArgs(v___x_4292_);
lean_dec(v___x_4292_);
v___x_4294_ = l_Lean_Fmt_fmtTSepArray___redArg(v_elts_4293_, v_a_4280_, v_a_4290_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; lean_object* v_a_4296_; lean_object* v___x_4297_; lean_object* v_rbTk_4298_; lean_object* v___x_4299_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
lean_inc(v_a_4295_);
v_a_4296_ = lean_ctor_get(v___x_4294_, 1);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4294_, 2);
v___x_4297_ = lean_unsigned_to_nat(2u);
v_rbTk_4298_ = l_Lean_Syntax_getArg(v_x_4279_, v___x_4297_);
lean_dec(v_x_4279_);
v___x_4299_ = l_Lean_Fmt_fmt(v_rbTk_4298_, v_a_4280_, v_a_4296_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4312_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
v_a_4301_ = lean_ctor_get(v___x_4299_, 1);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4303_ = v___x_4299_;
v_isShared_4304_ = v_isSharedCheck_4312_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_inc(v_a_4300_);
lean_dec(v___x_4299_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4312_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4305_; uint8_t v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4310_; 
v___x_4305_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsSpec___closed__2));
v___x_4306_ = 0;
v___x_4307_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4307_, 0, v___x_4306_);
lean_ctor_set_uint8(v___x_4307_, 1, v___x_4283_);
v___x_4308_ = l_Lean_Fmt_Layouts_collection(v___x_4305_, v_a_4289_, v_a_4295_, v_a_4300_, v___x_4307_);
lean_dec(v_a_4295_);
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 0, v___x_4308_);
v___x_4310_ = v___x_4303_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4308_);
lean_ctor_set(v_reuseFailAlloc_4311_, 1, v_a_4301_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
else
{
lean_dec(v_a_4295_);
lean_dec(v_a_4289_);
return v___x_4299_;
}
}
else
{
lean_object* v_a_4313_; lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
lean_dec(v_a_4289_);
lean_dec(v_x_4279_);
v_a_4313_ = lean_ctor_get(v___x_4294_, 0);
v_a_4314_ = lean_ctor_get(v___x_4294_, 1);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4294_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_inc(v_a_4313_);
lean_dec(v___x_4294_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4313_);
lean_ctor_set(v_reuseFailAlloc_4320_, 1, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
else
{
lean_dec(v_x_4279_);
return v___x_4288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsSpec___boxed(lean_object* v_x_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l_Lean_Fmt_fmtGuardMsgsSpec(v_x_4322_, v_a_4323_, v_a_4324_);
lean_dec_ref(v_a_4323_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1(){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4332_ = l_Lean_Fmt_fmtAttribute;
v___x_4333_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsSpec___closed__1));
v___x_4334_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___closed__1));
v___x_4335_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardMsgsSpec___boxed), 3, 0);
v___x_4336_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4332_, v___x_4333_, v___x_4334_, v___x_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1___boxed(lean_object* v_a_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1();
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsCmd(lean_object* v_x_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v___x_4360_; uint8_t v___x_4361_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v_spec_x3f_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; 
v___x_4360_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsCmd___closed__1));
lean_inc(v_x_4357_);
v___x_4361_ = l_Lean_Syntax_isOfKind(v_x_4357_, v___x_4360_);
if (v___x_4361_ == 0)
{
lean_object* v___x_4447_; lean_object* v___x_4448_; 
lean_dec(v_x_4357_);
v___x_4447_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4447_);
lean_ctor_set(v___x_4448_, 1, v_a_4359_);
return v___x_4448_;
}
else
{
lean_object* v___x_4449_; lean_object* v_doc_x3f_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___x_4469_; uint8_t v___x_4470_; 
v___x_4449_ = lean_unsigned_to_nat(0u);
v___x_4469_ = l_Lean_Syntax_getArg(v_x_4357_, v___x_4449_);
v___x_4470_ = l_Lean_Syntax_isNone(v___x_4469_);
if (v___x_4470_ == 0)
{
lean_object* v___x_4471_; uint8_t v___x_4472_; 
v___x_4471_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4469_);
v___x_4472_ = l_Lean_Syntax_matchesNull(v___x_4469_, v___x_4471_);
if (v___x_4472_ == 0)
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
lean_dec(v___x_4469_);
lean_dec(v_x_4357_);
v___x_4473_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4473_);
lean_ctor_set(v___x_4474_, 1, v_a_4359_);
return v___x_4474_;
}
else
{
lean_object* v_doc_x3f_4475_; lean_object* v___x_4476_; uint8_t v___x_4477_; 
v_doc_x3f_4475_ = l_Lean_Syntax_getArg(v___x_4469_, v___x_4449_);
lean_dec(v___x_4469_);
v___x_4476_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsCmd___closed__7));
lean_inc(v_doc_x3f_4475_);
v___x_4477_ = l_Lean_Syntax_isOfKind(v_doc_x3f_4475_, v___x_4476_);
if (v___x_4477_ == 0)
{
lean_object* v___x_4478_; lean_object* v___x_4479_; 
lean_dec(v_doc_x3f_4475_);
lean_dec(v_x_4357_);
v___x_4478_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
lean_ctor_set(v___x_4479_, 1, v_a_4359_);
return v___x_4479_;
}
else
{
lean_object* v___x_4480_; 
v___x_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4480_, 0, v_doc_x3f_4475_);
v_doc_x3f_4451_ = v___x_4480_;
v___y_4452_ = v_a_4358_;
v___y_4453_ = v_a_4359_;
goto v___jp_4450_;
}
}
}
else
{
lean_object* v___x_4481_; 
lean_dec(v___x_4469_);
v___x_4481_ = lean_box(0);
v_doc_x3f_4451_ = v___x_4481_;
v___y_4452_ = v_a_4358_;
v___y_4453_ = v_a_4359_;
goto v___jp_4450_;
}
v___jp_4450_:
{
lean_object* v___x_4454_; lean_object* v_tk_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; uint8_t v___x_4458_; 
v___x_4454_ = lean_unsigned_to_nat(1u);
v_tk_4455_ = l_Lean_Syntax_getArg(v_x_4357_, v___x_4454_);
v___x_4456_ = lean_unsigned_to_nat(2u);
v___x_4457_ = l_Lean_Syntax_getArg(v_x_4357_, v___x_4456_);
v___x_4458_ = l_Lean_Syntax_isNone(v___x_4457_);
if (v___x_4458_ == 0)
{
uint8_t v___x_4459_; 
lean_inc(v___x_4457_);
v___x_4459_ = l_Lean_Syntax_matchesNull(v___x_4457_, v___x_4454_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4460_; lean_object* v___x_4461_; 
lean_dec(v___x_4457_);
lean_dec(v_tk_4455_);
lean_dec(v_doc_x3f_4451_);
lean_dec(v_x_4357_);
v___x_4460_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
lean_ctor_set(v___x_4461_, 1, v___y_4453_);
return v___x_4461_;
}
else
{
lean_object* v_spec_x3f_4462_; lean_object* v___x_4463_; uint8_t v___x_4464_; 
v_spec_x3f_4462_ = l_Lean_Syntax_getArg(v___x_4457_, v___x_4449_);
lean_dec(v___x_4457_);
v___x_4463_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsSpec___closed__1));
lean_inc(v_spec_x3f_4462_);
v___x_4464_ = l_Lean_Syntax_isOfKind(v_spec_x3f_4462_, v___x_4463_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
lean_dec(v_spec_x3f_4462_);
lean_dec(v_tk_4455_);
lean_dec(v_doc_x3f_4451_);
lean_dec(v_x_4357_);
v___x_4465_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4465_);
lean_ctor_set(v___x_4466_, 1, v___y_4453_);
return v___x_4466_;
}
else
{
lean_object* v___x_4467_; 
v___x_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4467_, 0, v_spec_x3f_4462_);
v___y_4426_ = v_doc_x3f_4451_;
v___y_4427_ = v_tk_4455_;
v_spec_x3f_4428_ = v___x_4467_;
v___y_4429_ = v___y_4452_;
v___y_4430_ = v___y_4453_;
goto v___jp_4425_;
}
}
}
else
{
lean_object* v___x_4468_; 
lean_dec(v___x_4457_);
v___x_4468_ = lean_box(0);
v___y_4426_ = v_doc_x3f_4451_;
v___y_4427_ = v_tk_4455_;
v_spec_x3f_4428_ = v___x_4468_;
v___y_4429_ = v___y_4452_;
v___y_4430_ = v___y_4453_;
goto v___jp_4425_;
}
}
}
v___jp_4362_:
{
lean_object* v___x_4370_; 
v___x_4370_ = l_Lean_Fmt_fmt_x3f(v___y_4369_, v___y_4367_, v___y_4364_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v_a_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc(v_a_4371_);
v_a_4372_ = lean_ctor_get(v___x_4370_, 1);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4370_, 2);
v___x_4373_ = 0;
v___x_4374_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4374_, 0, v___x_4361_);
lean_ctor_set_uint8(v___x_4374_, 1, v___x_4373_);
lean_ctor_set_uint8(v___x_4374_, 2, v___x_4373_);
lean_ctor_set_uint8(v___x_4374_, 3, v___x_4373_);
v___x_4375_ = l_Lean_Fmt_fmt(v___y_4363_, v___y_4367_, v_a_4372_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v_a_4377_; lean_object* v___x_4378_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc(v_a_4376_);
v_a_4377_ = lean_ctor_get(v___x_4375_, 1);
lean_inc(v_a_4377_);
lean_dec_ref_known(v___x_4375_, 2);
v___x_4378_ = l_Lean_Fmt_fmt(v___y_4366_, v___y_4367_, v_a_4377_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4397_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
v_a_4380_ = lean_ctor_get(v___x_4378_, 1);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4382_ = v___x_4378_;
v_isShared_4383_ = v_isSharedCheck_4397_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_inc(v_a_4379_);
lean_dec(v___x_4378_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4397_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4384_ = lean_unsigned_to_nat(2u);
v___x_4385_ = lean_mk_empty_array_with_capacity(v___x_4384_);
lean_inc_ref(v___x_4385_);
v___x_4386_ = lean_array_push(v___x_4385_, v___y_4365_);
v___x_4387_ = lean_array_push(v___x_4386_, v_a_4371_);
v___x_4388_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4387_, v___x_4374_);
v___x_4389_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsCmd___closed__2));
v___x_4390_ = l_Lean_Fmt_Layouts_keywordSeparated(v___x_4388_, v_a_4376_, v_a_4379_, v___x_4389_);
v___x_4391_ = lean_array_push(v___x_4385_, v___y_4368_);
v___x_4392_ = lean_array_push(v___x_4391_, v___x_4390_);
v___x_4393_ = l_Lean_Fmt_Layouts_lines(v___x_4392_);
lean_dec_ref(v___x_4392_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v___x_4393_);
v___x_4395_ = v___x_4382_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
lean_ctor_set(v_reuseFailAlloc_4396_, 1, v_a_4380_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
else
{
lean_dec(v_a_4376_);
lean_dec_ref_known(v___x_4374_, 0);
lean_dec(v_a_4371_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v___y_4365_);
return v___x_4378_;
}
}
else
{
lean_dec_ref_known(v___x_4374_, 0);
lean_dec(v_a_4371_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
return v___x_4375_;
}
}
else
{
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4363_);
return v___x_4370_;
}
}
v___jp_4398_:
{
lean_object* v___x_4408_; 
lean_inc(v___y_4402_);
v___x_4408_ = l_Lean_Fmt_fmtWith_x3f(v___y_4403_, v___y_4402_, v___y_4407_, v___y_4405_, v___y_4401_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v_a_4410_; lean_object* v___x_4411_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
v_a_4410_ = lean_ctor_get(v___x_4408_, 1);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4408_, 2);
v___x_4411_ = l_Lean_Fmt_fmt(v___y_4406_, v___y_4405_, v_a_4410_);
if (lean_obj_tag(v___x_4411_) == 0)
{
if (lean_obj_tag(v___y_4400_) == 0)
{
lean_object* v_a_4412_; lean_object* v_a_4413_; lean_object* v___x_4414_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4412_);
v_a_4413_ = lean_ctor_get(v___x_4411_, 1);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4411_, 2);
v___x_4414_ = lean_box(0);
v___y_4363_ = v___y_4399_;
v___y_4364_ = v_a_4413_;
v___y_4365_ = v_a_4412_;
v___y_4366_ = v___y_4404_;
v___y_4367_ = v___y_4405_;
v___y_4368_ = v_a_4409_;
v___y_4369_ = v___x_4414_;
goto v___jp_4362_;
}
else
{
lean_object* v_a_4415_; lean_object* v_a_4416_; lean_object* v_val_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
v_a_4415_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4415_);
v_a_4416_ = lean_ctor_get(v___x_4411_, 1);
lean_inc(v_a_4416_);
lean_dec_ref_known(v___x_4411_, 2);
v_val_4417_ = lean_ctor_get(v___y_4400_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___y_4400_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___y_4400_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_val_4417_);
lean_dec(v___y_4400_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_val_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
v___y_4363_ = v___y_4399_;
v___y_4364_ = v_a_4416_;
v___y_4365_ = v_a_4415_;
v___y_4366_ = v___y_4404_;
v___y_4367_ = v___y_4405_;
v___y_4368_ = v_a_4409_;
v___y_4369_ = v___x_4422_;
goto v___jp_4362_;
}
}
}
}
else
{
lean_dec(v_a_4409_);
lean_dec(v___y_4404_);
lean_dec(v___y_4400_);
lean_dec(v___y_4399_);
return v___x_4411_;
}
}
else
{
lean_dec(v___y_4406_);
lean_dec(v___y_4404_);
lean_dec(v___y_4400_);
lean_dec(v___y_4399_);
return v___x_4408_;
}
}
v___jp_4425_:
{
lean_object* v___x_4431_; lean_object* v_inTk_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4431_ = lean_unsigned_to_nat(3u);
v_inTk_4432_ = l_Lean_Syntax_getArg(v_x_4357_, v___x_4431_);
v___x_4433_ = lean_unsigned_to_nat(4u);
v___x_4434_ = l_Lean_Syntax_getArg(v_x_4357_, v___x_4433_);
lean_dec(v_x_4357_);
v___x_4435_ = lean_box(v___x_4361_);
v___x_4436_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDocCommentWith___boxed), 4, 1);
lean_closure_set(v___x_4436_, 0, v___x_4435_);
v___x_4437_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsCmd___closed__4));
if (lean_obj_tag(v___y_4426_) == 0)
{
lean_object* v___x_4438_; 
v___x_4438_ = lean_box(0);
v___y_4399_ = v_inTk_4432_;
v___y_4400_ = v_spec_x3f_4428_;
v___y_4401_ = v___y_4430_;
v___y_4402_ = v___x_4437_;
v___y_4403_ = v___x_4436_;
v___y_4404_ = v___x_4434_;
v___y_4405_ = v___y_4429_;
v___y_4406_ = v___y_4427_;
v___y_4407_ = v___x_4438_;
goto v___jp_4398_;
}
else
{
lean_object* v_val_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
v_val_4439_ = lean_ctor_get(v___y_4426_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___y_4426_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___y_4426_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_val_4439_);
lean_dec(v___y_4426_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_val_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
v___y_4399_ = v_inTk_4432_;
v___y_4400_ = v_spec_x3f_4428_;
v___y_4401_ = v___y_4430_;
v___y_4402_ = v___x_4437_;
v___y_4403_ = v___x_4436_;
v___y_4404_ = v___x_4434_;
v___y_4405_ = v___y_4429_;
v___y_4406_ = v___y_4427_;
v___y_4407_ = v___x_4444_;
goto v___jp_4398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardMsgsCmd___boxed(lean_object* v_x_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_Fmt_fmtGuardMsgsCmd(v_x_4482_, v_a_4483_, v_a_4484_);
lean_dec_ref(v_a_4483_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1(){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4492_ = l_Lean_Fmt_fmtAttribute;
v___x_4493_ = ((lean_object*)(l_Lean_Fmt_fmtGuardMsgsCmd___closed__1));
v___x_4494_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___closed__1));
v___x_4495_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardMsgsCmd___boxed), 3, 0);
v___x_4496_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4492_, v___x_4493_, v___x_4494_, v___x_4495_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1___boxed(lean_object* v_a_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1();
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardPanicCmd(lean_object* v_x_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v___x_4506_; uint8_t v___x_4507_; 
v___x_4506_ = ((lean_object*)(l_Lean_Fmt_fmtGuardPanicCmd___closed__1));
lean_inc(v_x_4503_);
v___x_4507_ = l_Lean_Syntax_isOfKind(v_x_4503_, v___x_4506_);
if (v___x_4507_ == 0)
{
lean_object* v___x_4508_; lean_object* v___x_4509_; 
lean_dec(v_x_4503_);
v___x_4508_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4508_);
lean_ctor_set(v___x_4509_, 1, v_a_4505_);
return v___x_4509_;
}
else
{
lean_object* v___x_4510_; lean_object* v_tk_4511_; lean_object* v___x_4512_; 
v___x_4510_ = lean_unsigned_to_nat(0u);
v_tk_4511_ = l_Lean_Syntax_getArg(v_x_4503_, v___x_4510_);
v___x_4512_ = l_Lean_Fmt_fmt(v_tk_4511_, v_a_4504_, v_a_4505_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; lean_object* v_a_4514_; lean_object* v___x_4515_; lean_object* v_inTk_4516_; lean_object* v___x_4517_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_a_4513_);
v_a_4514_ = lean_ctor_get(v___x_4512_, 1);
lean_inc(v_a_4514_);
lean_dec_ref_known(v___x_4512_, 2);
v___x_4515_ = lean_unsigned_to_nat(1u);
v_inTk_4516_ = l_Lean_Syntax_getArg(v_x_4503_, v___x_4515_);
v___x_4517_ = l_Lean_Fmt_fmt(v_inTk_4516_, v_a_4504_, v_a_4514_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v_a_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
v_a_4519_ = lean_ctor_get(v___x_4517_, 1);
lean_inc(v_a_4519_);
lean_dec_ref_known(v___x_4517_, 2);
v___x_4520_ = lean_unsigned_to_nat(2u);
v___x_4521_ = l_Lean_Syntax_getArg(v_x_4503_, v___x_4520_);
lean_dec(v_x_4503_);
v___x_4522_ = l_Lean_Fmt_fmt(v___x_4521_, v_a_4504_, v_a_4519_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4538_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
v_a_4524_ = lean_ctor_get(v___x_4522_, 1);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4526_ = v___x_4522_;
v_isShared_4527_ = v_isSharedCheck_4538_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_inc(v_a_4523_);
lean_dec(v___x_4522_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4538_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4536_; 
v___x_4528_ = lean_mk_empty_array_with_capacity(v___x_4520_);
lean_inc_ref(v___x_4528_);
v___x_4529_ = lean_array_push(v___x_4528_, v_a_4513_);
v___x_4530_ = lean_array_push(v___x_4529_, v_a_4518_);
v___x_4531_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4530_);
lean_dec_ref(v___x_4530_);
v___x_4532_ = lean_array_push(v___x_4528_, v___x_4531_);
v___x_4533_ = lean_array_push(v___x_4532_, v_a_4523_);
v___x_4534_ = l_Lean_Fmt_Layouts_lines(v___x_4533_);
lean_dec_ref(v___x_4533_);
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 0, v___x_4534_);
v___x_4536_ = v___x_4526_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4534_);
lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_a_4524_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
else
{
lean_dec(v_a_4518_);
lean_dec(v_a_4513_);
return v___x_4522_;
}
}
else
{
lean_dec(v_a_4513_);
lean_dec(v_x_4503_);
return v___x_4517_;
}
}
else
{
lean_dec(v_x_4503_);
return v___x_4512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGuardPanicCmd___boxed(lean_object* v_x_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_Fmt_fmtGuardPanicCmd(v_x_4539_, v_a_4540_, v_a_4541_);
lean_dec_ref(v_a_4540_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1(){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4549_ = l_Lean_Fmt_fmtAttribute;
v___x_4550_ = ((lean_object*)(l_Lean_Fmt_fmtGuardPanicCmd___closed__1));
v___x_4551_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___closed__1));
v___x_4552_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGuardPanicCmd___boxed), 3, 0);
v___x_4553_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4549_, v___x_4550_, v___x_4551_, v___x_4552_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1___boxed(lean_object* v_a_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1();
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfoTreesCmd(lean_object* v_x_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_){
_start:
{
lean_object* v___x_4563_; uint8_t v___x_4564_; 
v___x_4563_ = ((lean_object*)(l_Lean_Fmt_fmtInfoTreesCmd___closed__1));
lean_inc(v_x_4560_);
v___x_4564_ = l_Lean_Syntax_isOfKind(v_x_4560_, v___x_4563_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
lean_dec(v_x_4560_);
v___x_4565_ = l_Lean_Fmt_Error_partialFormatter;
v___x_4566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4565_);
lean_ctor_set(v___x_4566_, 1, v_a_4562_);
return v___x_4566_;
}
else
{
lean_object* v___x_4567_; lean_object* v_tk_4568_; lean_object* v___x_4569_; 
v___x_4567_ = lean_unsigned_to_nat(0u);
v_tk_4568_ = l_Lean_Syntax_getArg(v_x_4560_, v___x_4567_);
v___x_4569_ = l_Lean_Fmt_fmt(v_tk_4568_, v_a_4561_, v_a_4562_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v_a_4571_; lean_object* v___x_4572_; lean_object* v_inTk_4573_; lean_object* v___x_4574_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc(v_a_4570_);
v_a_4571_ = lean_ctor_get(v___x_4569_, 1);
lean_inc(v_a_4571_);
lean_dec_ref_known(v___x_4569_, 2);
v___x_4572_ = lean_unsigned_to_nat(1u);
v_inTk_4573_ = l_Lean_Syntax_getArg(v_x_4560_, v___x_4572_);
v___x_4574_ = l_Lean_Fmt_fmt(v_inTk_4573_, v_a_4561_, v_a_4571_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v_a_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
v_a_4576_ = lean_ctor_get(v___x_4574_, 1);
lean_inc(v_a_4576_);
lean_dec_ref_known(v___x_4574_, 2);
v___x_4577_ = lean_unsigned_to_nat(2u);
v___x_4578_ = l_Lean_Syntax_getArg(v_x_4560_, v___x_4577_);
lean_dec(v_x_4560_);
v___x_4579_ = l_Lean_Fmt_fmt(v___x_4578_, v_a_4561_, v_a_4576_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4595_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
v_a_4581_ = lean_ctor_get(v___x_4579_, 1);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4583_ = v___x_4579_;
v_isShared_4584_ = v_isSharedCheck_4595_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_inc(v_a_4580_);
lean_dec(v___x_4579_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4595_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4593_; 
v___x_4585_ = lean_mk_empty_array_with_capacity(v___x_4577_);
lean_inc_ref(v___x_4585_);
v___x_4586_ = lean_array_push(v___x_4585_, v_a_4570_);
v___x_4587_ = lean_array_push(v___x_4586_, v_a_4575_);
v___x_4588_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4587_);
lean_dec_ref(v___x_4587_);
v___x_4589_ = lean_array_push(v___x_4585_, v___x_4588_);
v___x_4590_ = lean_array_push(v___x_4589_, v_a_4580_);
v___x_4591_ = l_Lean_Fmt_Layouts_lines(v___x_4590_);
lean_dec_ref(v___x_4590_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4591_);
v___x_4593_ = v___x_4583_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4591_);
lean_ctor_set(v_reuseFailAlloc_4594_, 1, v_a_4581_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
else
{
lean_dec(v_a_4575_);
lean_dec(v_a_4570_);
return v___x_4579_;
}
}
else
{
lean_dec(v_a_4570_);
lean_dec(v_x_4560_);
return v___x_4574_;
}
}
else
{
lean_dec(v_x_4560_);
return v___x_4569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfoTreesCmd___boxed(lean_object* v_x_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_Lean_Fmt_fmtInfoTreesCmd(v_x_4596_, v_a_4597_, v_a_4598_);
lean_dec_ref(v_a_4597_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1(){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4606_ = l_Lean_Fmt_fmtAttribute;
v___x_4607_ = ((lean_object*)(l_Lean_Fmt_fmtInfoTreesCmd___closed__1));
v___x_4608_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___closed__1));
v___x_4609_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInfoTreesCmd___boxed), 3, 0);
v___x_4610_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4606_, v___x_4607_, v___x_4608_, v___x_4609_);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1___boxed(lean_object* v_a_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1();
return v_res_4612_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Notation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrecParen___regBuiltin_Lean_Fmt_fmtPrecParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtAddPrec = _init_l_Lean_Fmt_fmtAddPrec();
lean_mark_persistent(l_Lean_Fmt_fmtAddPrec);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrec___regBuiltin_Lean_Fmt_fmtAddPrec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtSubPrec = _init_l_Lean_Fmt_fmtSubPrec();
lean_mark_persistent(l_Lean_Fmt_fmtSubPrec);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrec___regBuiltin_Lean_Fmt_fmtSubPrec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtAddPrio = _init_l_Lean_Fmt_fmtAddPrio();
lean_mark_persistent(l_Lean_Fmt_fmtAddPrio);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtAddPrio___regBuiltin_Lean_Fmt_fmtAddPrio__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtSubPrio = _init_l_Lean_Fmt_fmtSubPrio();
lean_mark_persistent(l_Lean_Fmt_fmtSubPrio);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubPrio___regBuiltin_Lean_Fmt_fmtSubPrio__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtPrioParen___regBuiltin_Lean_Fmt_fmtPrioParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxPostfix___regBuiltin_Lean_Fmt_fmtStxPostfix__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_instInhabitedEndsInIdent_default = _init_l_Lean_Fmt_instInhabitedEndsInIdent_default();
l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instInhabitedEndsInIdent = _init_l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_instInhabitedEndsInIdent();
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOptional___regBuiltin_Lean_Fmt_fmtStxOptional__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxNotFollowedBy___regBuiltin_Lean_Fmt_fmtStxNotFollowedBy__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtStxOrelse = _init_l_Lean_Fmt_fmtStxOrelse();
lean_mark_persistent(l_Lean_Fmt_fmtStxOrelse);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtStxOrelse___regBuiltin_Lean_Fmt_fmtStxOrelse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNot___regBuiltin_Lean_Fmt_fmtTermNot__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNeg___regBuiltin_Lean_Fmt_fmtTermNeg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermInv___regBuiltin_Lean_Fmt_fmtTermInv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtTermMem = _init_l_Lean_Fmt_fmtTermMem();
lean_mark_persistent(l_Lean_Fmt_fmtTermMem);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermMem___regBuiltin_Lean_Fmt_fmtTermMem__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtTermNotMem = _init_l_Lean_Fmt_fmtTermNotMem();
lean_mark_persistent(l_Lean_Fmt_fmtTermNotMem);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermNotMem___regBuiltin_Lean_Fmt_fmtTermNotMem__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtTermLe = _init_l_Lean_Fmt_fmtTermLe();
lean_mark_persistent(l_Lean_Fmt_fmtTermLe);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermLe___regBuiltin_Lean_Fmt_fmtTermLe__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtTermGe = _init_l_Lean_Fmt_fmtTermGe();
lean_mark_persistent(l_Lean_Fmt_fmtTermGe);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermGe___regBuiltin_Lean_Fmt_fmtTermGe__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtTermAnd = _init_l_Lean_Fmt_fmtTermAnd();
lean_mark_persistent(l_Lean_Fmt_fmtTermAnd);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermAnd___regBuiltin_Lean_Fmt_fmtTermAnd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_fmtTermOr = _init_l_Lean_Fmt_fmtTermOr();
lean_mark_persistent(l_Lean_Fmt_fmtTermOr);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermOr___regBuiltin_Lean_Fmt_fmtTermOr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeLeft___regBuiltin_Lean_Fmt_fmtTermPipeLeft__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermPipeRight___regBuiltin_Lean_Fmt_fmtTermPipeRight__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTermDollar___regBuiltin_Lean_Fmt_fmtTermDollar__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRawNatLit___regBuiltin_Lean_Fmt_fmtRawNatLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBinderIdent___regBuiltin_Lean_Fmt_fmtBinderIdent__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCaseArg___regBuiltin_Lean_Fmt_fmtCaseArg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfThenElse___regBuiltin_Lean_Fmt_fmtIfThenElse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDepIfThenElse___regBuiltin_Lean_Fmt_fmtDepIfThenElse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIfLet___regBuiltin_Lean_Fmt_fmtIfLet__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBoolIfThenElse___regBuiltin_Lean_Fmt_fmtBoolIfThenElse__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSubtype___regBuiltin_Lean_Fmt_fmtSubtype__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithoutExpectedType___regBuiltin_Lean_Fmt_fmtWithoutExpectedType__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtModCast___regBuiltin_Lean_Fmt_fmtModCast__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtIncludeStr___regBuiltin_Lean_Fmt_fmtIncludeStr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtWithAnnotateTerm___regBuiltin_Lean_Fmt_fmtWithAnnotateTerm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtByElab___regBuiltin_Lean_Fmt_fmtByElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecated___regBuiltin_Lean_Fmt_fmtDeprecated__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDeprecatedArg___regBuiltin_Lean_Fmt_fmtDeprecatedArg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSuggestFor___regBuiltin_Lean_Fmt_fmtSuggestFor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnivOutParams___regBuiltin_Lean_Fmt_fmtUnivOutParams__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCommandCodeAction___regBuiltin_Lean_Fmt_fmtCommandCodeAction__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtBuiltinCommandCodeAction___regBuiltin_Lean_Fmt_fmtBuiltinCommandCodeAction__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunCmd___regBuiltin_Lean_Fmt_fmtRunCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunElab___regBuiltin_Lean_Fmt_fmtRunElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtRunMeta___regBuiltin_Lean_Fmt_fmtRunMeta__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtReduceCmd___regBuiltin_Lean_Fmt_fmtReduceCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSetLibrarySuggestions___regBuiltin_Lean_Fmt_fmtSetLibrarySuggestions__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeKeyCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtDiscrTreeSimpKeyCmd___regBuiltin_Lean_Fmt_fmtDiscrTreeSimpKeyCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtSeal___regBuiltin_Lean_Fmt_fmtSeal__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtUnseal___regBuiltin_Lean_Fmt_fmtUnseal__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtTimeCmd___regBuiltin_Lean_Fmt_fmtTimeCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTactic___regBuiltin_Lean_Fmt_fmtCheckTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckTacticFailure___regBuiltin_Lean_Fmt_fmtCheckTacticFailure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimp___regBuiltin_Lean_Fmt_fmtCheckSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtCheckSimpFailure___regBuiltin_Lean_Fmt_fmtCheckSimpFailure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsFilter___regBuiltin_Lean_Fmt_fmtGuardMsgsFilter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsWhitespace___regBuiltin_Lean_Fmt_fmtGuardMsgsWhitespace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsOrdering___regBuiltin_Lean_Fmt_fmtGuardMsgsOrdering__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsPositions___regBuiltin_Lean_Fmt_fmtGuardMsgsPositions__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSubstring___regBuiltin_Lean_Fmt_fmtGuardMsgsSubstring__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpecElt___regBuiltin_Lean_Fmt_fmtGuardMsgsSpecElt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsSpec___regBuiltin_Lean_Fmt_fmtGuardMsgsSpec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardMsgsCmd___regBuiltin_Lean_Fmt_fmtGuardMsgsCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtGuardPanicCmd___regBuiltin_Lean_Fmt_fmtGuardPanicCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Notation_0__Lean_Fmt_fmtInfoTreesCmd___regBuiltin_Lean_Fmt_fmtInfoTreesCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Notation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Notation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Notation(builtin);
}
#ifdef __cplusplus
}
#endif
